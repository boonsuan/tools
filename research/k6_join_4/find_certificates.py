"""Find the certificates that verify_k6_join_4.py checks.

    python find_certificates.py

This needs numpy, scipy and cvxpy (with the Clarabel solver).  It writes
k6_join_4_certificates.json.  The model, the residue maps and the exact
checks are imported from verify_k6_join_4.py, so the two programs cannot
disagree about what is being certified.

For each residue map (c, x):

1. Linear certificate.  Look for multipliers lam (lam >= 0 on inequalities)
   that combine the rows a.v <= b (or =) into w.v <= d with
   sum_j min(w_j, 0) > d.  Since every variable lies in [0, 1], no v then
   satisfies the rows.  With lam in [-1, 1] this is a linear program
   (HiGHS, through scipy).  It succeeds for 740 of the 768 maps.

2. Cuts from positivity.  Otherwise solve the semidefinite program
       minimize t  subject to  every row violated by at most t,
                               every PSD block + t I  PSD,  0 <= v <= 1.
   Its optimum is positive.  The dual matrices Z of the PSD constraints are
   PSD; rounded to rational PSD matrices they give valid linear cuts
   <Z, P> >= 0, and the linear program of step 1 with these cuts added
   then succeeds.

3. Rounding.  The multipliers and the cut matrices are rounded to the
   smallest denominators (from a short list) for which the certificate still
   verifies exactly.  This keeps the file small.
"""
import json
import warnings
from fractions import Fraction
from pathlib import Path

import cvxpy as cp
import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog

from verify_k6_join_4 import Q, S, N, build_model, check_certificate, cut_row, is_psd, residue_maps

HERE = Path(__file__).parent
warnings.filterwarnings("ignore", module="cvxpy")


# ---------------------------------------------------------------- step 1

def farkas_lp(rows, nvars):
    """Maximize sum_j min(w_j, 0) - d over multipliers lam in [-1, 1]
    ([0, 1] on inequalities), where w = sum lam_r a_r and d = sum lam_r b_r.
    Returns the optimal value and lam, or (None, None)."""
    data, var, row_index = [], [], []
    for r, (coefs, _, _) in enumerate(rows):
        for v, a in coefs.items():
            data.append(float(a)); var.append(v); row_index.append(r)
    A = sp.csr_matrix((data, (var, row_index)), shape=(nvars, len(rows)))   # w = A lam
    # Unknowns (lam, z) with z_j <= min(w_j, 0); minimize d - sum z.
    A_ub = sp.hstack([-A, sp.identity(nvars)]).tocsr()
    cost = np.concatenate([[float(b) for _, _, b in rows], -np.ones(nvars)])
    bounds = [(-1, 1) if sense == "=" else (0, 1) for _, sense, _ in rows] + [(None, 0)] * nvars
    result = linprog(cost, A_ub=A_ub, b_ub=np.zeros(nvars), bounds=bounds, method="highs")
    if result.status != 0:
        return None, None
    return -result.fun, result.x[:len(rows)]


# ---------------------------------------------------------------- step 2

def slack_sdp(rows, nvars, blocks):
    """Solve the slack SDP; return the optimal t and the dual matrix of each
    PSD block (as numpy arrays)."""
    v = cp.Variable(nvars)
    t = cp.Variable(nonneg=True)
    constraints = [v >= 0, v <= 1]
    for sense in ("=", "<="):
        selected = [(coefs, b) for coefs, s, b in rows if s == sense]
        data, r_index, c_index = [], [], []
        for r, (coefs, _) in enumerate(selected):
            for var, a in coefs.items():
                data.append(float(a)); r_index.append(r); c_index.append(var)
        A = sp.csr_matrix((data, (r_index, c_index)), shape=(len(selected), nvars))
        b = np.array([float(b) for _, b in selected])
        constraints.append(A @ v - b <= t)
        if sense == "=":
            constraints.append(b - A @ v <= t)
    psd = {}
    for name, (size, entries) in blocks.items():
        data, r_index, c_index, const = [], [], [], np.zeros(size * size)
        for (i, j), (form, c0) in entries.items():
            for var, a in form.items():
                data.append(float(a)); r_index.append(i * size + j); c_index.append(var)
            const[i * size + j] += float(c0)
        B = sp.csr_matrix((data, (r_index, c_index)), shape=(size * size, nvars))
        P = cp.reshape(B @ v + const, (size, size), order="C")
        psd[name] = (P + P.T) / 2 + t * np.eye(size) >> 0
        constraints.append(psd[name])
    problem = cp.Problem(cp.Minimize(t), constraints)
    for solver in ("CLARABEL", "SCS"):
        try:
            problem.solve(solver=solver)
        except cp.error.SolverError:
            continue
        if problem.status == "optimal":
            break
    return t.value, {name: con.dual_value for name, con in psd.items()}


def rational_psd(Zf, size, denominator=2 ** 24):
    """A rational PSD matrix near the numerical matrix Zf: shift the diagonal
    a little, round to the given denominator, and check exactly."""
    Zf = (Zf + Zf.T) / 2
    eigenvalues = np.linalg.eigvalsh(Zf)
    shift = 2 * max(0.0, -eigenvalues.min()) + 1e-9 * max(1.0, abs(eigenvalues).max())
    for _ in range(8):
        Z = {}
        for i in range(size):
            for j in range(i, size):
                f = Fraction(round((Zf[i, j] + (shift if i == j else 0)) * denominator), denominator)
                if f:
                    Z[i, j] = Z[j, i] = f
        if is_psd(Z, size):
            return Z
        shift = 10 * shift + 1e-9
    return None


# ---------------------------------------------------------------- step 3

def as_certificate(lam, lam_den, cuts, cut_den):
    """The JSON form read by verify_k6_join_4.py."""
    cert = {"lam": {"den": lam_den, "num": {str(r): int(f * lam_den) for r, f in lam.items()}}}
    if cuts:
        cert["cuts"] = [{"block": name, "den": cut_den,
                         "upper": [[i, j, int(z * cut_den)] for (i, j), z in Z.items() if i <= j]}
                        for name, Z in cuts]
    return cert


def round_to(values, den):
    return {k: f for k, f in ((k, Fraction(round(Fraction(v) * den), den)) for k, v in values.items()) if f}


def shortest_certificate(c, x, rows, lam, cuts):
    """Round lam (and the cuts) to the smallest denominators that verify."""
    for lam_den in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6, 10 ** 9):
        for cut_den in ((2 ** 10, 2 ** 14, 2 ** 18, 2 ** 24) if cuts else (1,)):
            rounded_cuts = [(name, round_to(Z, cut_den)) for name, Z in cuts]
            rounded_lam = {r: f for r, f in round_to(lam, lam_den).items()
                           if f > 0 or (r < len(rows) and rows[r][1] == "=")}
            cert = as_certificate(rounded_lam, lam_den, rounded_cuts, cut_den)
            if check_certificate(c, x, cert)[0]:
                return cert
    return None


def certify(c, x):
    rows, nvars, blocks = build_model(c, x)
    cuts = []
    value, lam = farkas_lp(rows, nvars)
    if value is None or value <= 1e-9:
        t, duals = slack_sdp(rows, nvars, blocks)
        for name, Zf in duals.items():
            if Zf is not None:
                Z = rational_psd(np.array(Zf), blocks[name][0])
                if Z is None:
                    raise RuntimeError(f"could not round the dual matrix of {name} for c={c}, x={x}")
                if Z:
                    cuts.append((name, Z))
        all_rows = rows + [cut_row(blocks[name], Z) for name, Z in cuts]
        value, lam = farkas_lp(all_rows, nvars)
        if value is None or value <= 1e-9:
            raise RuntimeError(f"no certificate for c={c}, x={x} (SDP optimum t = {t:.3g})")
    lam = {r: Fraction(round(v * 10 ** 9), 10 ** 9) for r, v in enumerate(lam) if abs(v) > 1e-12}
    cert = shortest_certificate(c, x, rows, lam, cuts)
    if cert is None:
        raise RuntimeError(f"rounded certificate for c={c}, x={x} does not verify")
    return {"c": list(c), "x": list(x), **cert}


def main():
    maps = residue_maps()
    entries = []
    for k, (c, x) in enumerate(maps):
        entries.append(certify(c, x))
        if (k + 1) % 32 == 0:
            print(f"{k + 1} of {len(maps)} maps certified "
                  f"({sum('cuts' in e for e in entries)} with PSD cuts)", flush=True)
    out = {"graph": "K_6 v complement(K_4)", "s": S, "N": N, "q": Q, "maps": entries}
    (HERE / "k6_join_4_certificates.json").write_text(json.dumps(out, separators=(",", ":")))
    print(f"wrote certificates for {len(entries)} maps")


if __name__ == "__main__":
    main()
