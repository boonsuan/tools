"""A machine-checkable proof that K_6 v complement(K_4) is not graceful,
using residues mod 8, positions in [0, m], and positivity together.

Standard library only; every check is exact (fractions.Fraction).  Run:

    python verify_k6_join_4.py

G = K_6 v complement(K_4): a clique on 6 vertices joined to 4 independent
vertices, with 10 vertices and m = 15 + 24 = 39 edges.  It is not graceful by
exhaustive search, but each tool of the paper fails to show it: Tool I
(iterated parity, and the residue equations for every q <= 16), Tool II
(positivity) and Tool III (the interval bounds).

The argument
------------
Suppose f is a graceful labeling.  Reduce the labels mod q = 8 and let c_r
and x_r be the numbers of clique and of independent vertices with label = r
(mod 8).  We call (c, x) the residue map of f.

Step 1 (residues, Tool I).  (c, x) satisfies the residue equations mod 8 and
the capacities (Section 3.3 of the paper).  We enumerate ALL such (c, x) by
brute force: there are 768.

Step 2 (positions, Tool III).  Fix (c, x).  Split the vertices into groups
g = (clique or independent, residue r), of size n_g, whose labels lie in
A_g = {a in [0, 39] : a = r mod 8}.  Define 0/1 numbers
   p[g,a] = 1 if some vertex of g has label a,
   y[(g,a),(h,b)] = 1 if a vertex of g has label a and a DIFFERENT vertex of
                    h has label b      (only for a != b: labels are distinct).
They satisfy the linear constraints listed in build_model.  Each is an
immediate property of a graceful labeling: n_g labels per group, at most one
vertex per label, row sums, y <= p, the product rule for occupancies, and
exactly one edge of each difference k = 1..39.

Step 3 (positivity, Tool II).  Two families of matrices are PSD:
   P1 = [[1, p^T], [p, Y + Diag p]] = (1, p)(1, p)^T,
   P2_g = (n_g - 1) Diag(p_g) - Y_gg, which is n_g I - J on the used labels.
For every rational PSD matrix Z of the same size, <Z, P> >= 0 is then a
valid LINEAR inequality.

The certificates.  Let v be the vector of all the variables p and y; each
lies in [0, 1].  For each residue map the certificate consists of
  * rational symmetric matrices Z, one per PSD block used, each checked PSD
    exactly here, giving cuts <Z, P> >= 0, and
  * rational multipliers lam (>= 0 on inequalities) for the linear
    constraints and these cuts.
With w = sum lam_r a_r and d = sum lam_r b_r, every solution has w.v <= d,
yet the minimum of w.v over [0, 1] (in every coordinate) is
sum_j min(w_j, 0) > d.  So no residue map extends to a graceful labeling,
and G is not graceful.

The certificates were found with floating-point LP/SDP solvers (see
find_certificates.py); nothing here depends on them.  For 740 maps the
linear constraints suffice; the other 28 need the PSD cuts.
"""
import json
import sys
from fractions import Fraction
from math import comb
from pathlib import Path

S, N, Q = 6, 4, 8
M = comb(S, 2) + S * N          # 39 edges


# ----------------------------------------------------------------------------
# Step 1: all residue maps mod 8 satisfying the residue equations and capacities
# ----------------------------------------------------------------------------

def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def residue_maps():
    """Ordered pairs (u, v) on edges with f(u) - f(v) = d (mod 8) must number
    #{0 < |j| <= 39 : j = d mod 8}; at most floor((39 - r)/8) + 1 labels are r mod 8."""
    target = [0] * Q
    for j in range(1, M + 1):
        target[j % Q] += 1
        target[-j % Q] += 1
    capacity = [(M - r) // Q + 1 for r in range(Q)]
    maps = []
    for c in compositions(S, Q):
        for x in compositions(N, Q):
            if any(c[r] + x[r] > capacity[r] for r in range(Q)):
                continue
            if all(sum(c[r] * c[(r - d) % Q] for r in range(Q)) - (S if d == 0 else 0)
                   + sum(c[r] * x[(r - d) % Q] + x[r] * c[(r - d) % Q] for r in range(Q))
                   == target[d] for d in range(Q)):
                maps.append((c, x))
    return maps


# ----------------------------------------------------------------------------
# Step 2: the relaxation for one residue map
# ----------------------------------------------------------------------------

def build_model(c, x):
    """The relaxation for the residue map (c, x).

    A group g is a nonempty class (clique or independent, residue r) with
    size[g] vertices, whose labels lie in labels[g] = {a in [0, 39] : a = r
    mod 8}.  A slot s = (g, i) stands for "a vertex of g has label
    labels[g][i]"; its variable is p_s.  For two slots s, s' with different
    labels, y_{s,s'} stands for "s holds, and a different vertex has s'".
    There is no y for two slots of a group with a single vertex, nor for two
    slots with the same label: such events are impossible.  Variables are
    numbered p first (in slot order), then y (in pair order).

    Returns (rows, number of variables, blocks).  A row is
    ({variable: coefficient}, '=' or '<=', right side).  A block is
    name -> (size, entries), where entries maps (i, j) to (linear form,
    constant) and the block is PSD at every graceful labeling.
    """
    groups = [("C", r, c[r]) for r in range(Q) if c[r]] + [("X", r, x[r]) for r in range(Q) if x[r]]
    size = [n for _, _, n in groups]
    labels = [[a for a in range(M + 1) if a % Q == r] for _, r, _ in groups]
    slots = [(g, i) for g in range(len(groups)) for i in range(len(labels[g]))]
    label = {(g, i): labels[g][i] for g, i in slots}

    p_var = {s: k for k, s in enumerate(slots)}
    y_var = {}                                       # (s, s') with s before s' in slot order
    for k, s in enumerate(slots):
        for s2 in slots[k + 1:]:
            if label[s] != label[s2] and not (s[0] == s2[0] and size[s[0]] < 2):
                y_var[s, s2] = len(slots) + len(y_var)

    def y(s, s2):
        return y_var.get((s, s2), y_var.get((s2, s)))

    def adjacent(g, h):                              # only independent vertices are non-adjacent
        return not (groups[g][0] == "X" and groups[h][0] == "X")

    rows = []
    for g in range(len(groups)):                     # group g has size[g] vertices
        rows.append(({p_var[g, i]: 1 for i in range(len(labels[g]))}, "=", size[g]))
    at_label = {}                                    # label -> its x variables
    for s in slots:
        at_label.setdefault(label[s], []).append(p_var[s])
    for xs in at_label.values():                     # at most one vertex per label
        rows.append(({v: 1 for v in xs}, "<=", 1))
    for s in slots:                                  # given s, the other vertices of h are
        for h in range(len(groups)):                 # size[h] (minus one if h is s's group)
            row = {}
            for j in range(len(labels[h])):
                v = y(s, (h, j))
                if v is not None:
                    row[v] = row.get(v, 0) + 1
            others = size[h] - (1 if s[0] == h else 0)
            if others:
                row[p_var[s]] = row.get(p_var[s], 0) - others
            if row:
                rows.append((row, "=", 0))
    pairs_at = {}                                    # {a, b} -> the y variables on labels a, b
    for (s, s2), v in y_var.items():
        rows.append(({v: 1, p_var[s]: -1}, "<=", 0))      # y <= p at both ends
        rows.append(({v: 1, p_var[s2]: -1}, "<=", 0))
        pairs_at.setdefault(tuple(sorted((label[s], label[s2]))), []).append(v)
    for (a, b), ys in pairs_at.items():
        rows.append(({v: 1 for v in ys}, "<=", 1))        # at most one pair on {a, b}
        row = {}                                          # both labels used => a pair on them:
        for v in at_label.get(a, []) + at_label.get(b, []):   # occ(a) + occ(b) - pairs <= 1
            row[v] = row.get(v, 0) + 1
        for v in ys:
            row[v] = row.get(v, 0) - 1
        rows.append((row, "<=", 1))
    for k in range(1, M + 1):                        # exactly one edge of difference k
        rows.append(({v: 1 for (s, s2), v in y_var.items()
                      if adjacent(s[0], s2[0]) and abs(label[s] - label[s2]) == k}, "=", 1))

    blocks = {}
    # P1 = [[1, p^T], [p, Y + Diag p]], which is (1, p)(1, p)^T at a labeling.
    P1 = {(0, 0): ({}, 1)}
    for a, s in enumerate(slots):
        P1[0, a + 1] = P1[a + 1, 0] = ({p_var[s]: 1}, 0)
        P1[a + 1, a + 1] = ({p_var[s]: 1}, 0)
        for b, s2 in enumerate(slots):
            if a != b and y(s, s2) is not None:
                P1[a + 1, b + 1] = ({y(s, s2): 1}, 0)
    blocks["P1"] = (1 + len(slots), P1)
    # P2_g = (size[g] - 1) Diag(p_g) - Y_gg, which is n I - J on the used labels.
    for g in range(len(groups)):
        if size[g] >= 2:
            P = {}
            for i in range(len(labels[g])):
                P[i, i] = ({p_var[g, i]: size[g] - 1}, 0)
                for j in range(len(labels[g])):
                    if i != j and y((g, i), (g, j)) is not None:
                        P[i, j] = ({y((g, i), (g, j)): -1}, 0)
            blocks[f"P2_{g}"] = (len(labels[g]), P)
    return rows, len(slots) + len(y_var), blocks


# ----------------------------------------------------------------------------
# Step 3: exact verification of a certificate
# ----------------------------------------------------------------------------

def is_psd(Z, size):
    """Exact PSD test of a rational symmetric matrix by symmetric elimination."""
    A = [[Z.get((i, j), Fraction(0)) for j in range(size)] for i in range(size)]
    for k in range(size):
        if A[k][k] < 0:
            return False
        if A[k][k] == 0:
            if any(A[k][j] != 0 for j in range(k + 1, size)):
                return False
            continue
        for i in range(k + 1, size):
            if A[i][k]:
                f = A[i][k] / A[k][k]
                for j in range(k + 1, size):
                    if A[k][j]:
                        A[i][j] -= f * A[k][j]
    return True


def cut_row(block, Z):
    """The cut <Z, P> >= 0 for a PSD block P, as a row 'a.v <= b'."""
    _, entries = block
    row, rhs = {}, Fraction(0)
    for (i, j), (form, const) in entries.items():
        z = Z.get((i, j), 0)
        for var, a in form.items():
            row[var] = row.get(var, 0) - z * a
        rhs += z * const
    return row, "<=", rhs


def check_certificate(c, x, cert):
    """Check one certificate exactly.  Returns (True, margin) with margin =
    min of w.v over the box minus d > 0, or (False, reason)."""
    rows, _, blocks = build_model(c, x)
    for cut in cert.get("cuts", []):
        size, _ = blocks[cut["block"]]
        Z = {}
        for i, j, num in cut["upper"]:
            Z[(i, j)] = Z[(j, i)] = Fraction(num, cut["den"])
        if not is_psd(Z, size):
            return False, f"cut matrix for {cut['block']} is not PSD"
        rows.append(cut_row(blocks[cut["block"]], Z))
    w, d = {}, Fraction(0)
    den = cert["lam"]["den"]
    for r, num in cert["lam"]["num"].items():
        lam = Fraction(num, den)
        coefs, sense, rhs = rows[int(r)]
        if sense == "<=" and lam < 0:
            return False, "negative multiplier on an inequality"
        for var, a in coefs.items():
            w[var] = w.get(var, 0) + lam * a
        d += lam * rhs
    box_min = sum(min(a, 0) for a in w.values())
    if box_min <= d:
        return False, f"the combined inequality is satisfiable (margin {box_min - d})"
    return True, box_min - d


def main():
    data = json.loads((Path(__file__).parent / "k6_join_4_certificates.json").read_text())
    certs = {(tuple(e["c"]), tuple(e["x"])): e for e in data["maps"]}
    maps = residue_maps()
    print(f"Step 1: {len(maps)} residue maps mod {Q} satisfy the residue equations and capacities")
    missing = [mp for mp in maps if mp not in certs]
    if missing:
        sys.exit(f"no certificate for {len(missing)} maps, e.g. {missing[0]}")
    print("Steps 2 and 3: building the relaxation for each map and checking its certificate")
    worst, with_cuts = None, 0
    for k, (c, x) in enumerate(maps):
        ok, margin = check_certificate(c, x, certs[(c, x)])
        if not ok:
            sys.exit(f"certificate for c={c}, x={x} FAILED: {margin}")
        with_cuts += bool(certs[(c, x)].get("cuts"))
        worst = margin if worst is None else min(worst, margin)
        if (k + 1) % 128 == 0:
            print(f"  {k + 1} certificates verified", flush=True)
    print(f"Step 3: all {len(maps)} certificates verified exactly "
          f"({with_cuts} use PSD cuts; smallest margin {float(worst):.4f})")
    print("Hence K_6 v complement(K_4) is not graceful.")


if __name__ == "__main__":
    main()
