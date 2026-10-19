# K₆ ∨ K̄₄ is not graceful: a combined certificate

K₆ ∨ K̄₄ is a clique on six vertices joined to four independent vertices;
it has 10 vertices and m = 39 edges. An exhaustive search shows that it is not graceful,
but each tool of the paper fails on it separately:

- Tool I: it passes the iterated parity test, and its residue equations,
  with capacities, are solvable for every q ≤ 16;
- Tool II: positivity misses it (μ = 22 > β₃₉ ≈ 18.2);
- Tool III: it satisfies the interval bounds.

The proof here uses the three tools together. It is explained in
[`../README.md`](../README.md), Part 2. In short: residues mod 8 split the
problem into 768 cases, and in each case a relaxation in the positions of
the labels, with positivity constraints, has no solution.

| File | Contents |
| --- | --- |
| [`verify_k6_join_4.py`](verify_k6_join_4.py) | The verifier: exact arithmetic, standard library only. |
| [`k6_join_4_certificates.json`](k6_join_4_certificates.json) | One certificate per residue map (3 MB). |
| [`find_certificates.py`](find_certificates.py) | The program that found the certificates (LP and SDP solvers). |

## Checking the proof

```
python verify_k6_join_4.py
```

This needs Python 3.9 or later and nothing else, and takes about 20 seconds.
It works in three steps.

1. **Residue maps.** By brute force, it finds every residue map mod 8 that
   satisfies the residue equations and capacities. There are 768.
2. **The model.** For each map it builds the constraints of the relaxation.
   The docstring of `build_model` lists them, and each one holds at every
   graceful labeling.
3. **The certificates.** For each map it checks the certificate exactly:
   - every cut matrix Z is positive semidefinite (by exact symmetric
     elimination);
   - the multipliers have the right signs;
   - the combined inequality w·v ≤ d is impossible when every variable lies
     in [0, 1], because the minimum of w·v there exceeds d.

The verifier finds the residue maps and builds the model itself. It reads
only the multipliers and cut matrices from the JSON file, so a wrong or
missing certificate makes it fail.

## Finding the certificates

```
python find_certificates.py
```

This needs numpy, scipy and cvxpy (with the Clarabel solver) and takes about
ten minutes. It rewrites `k6_join_4_certificates.json`. With scipy 1.18 and
cvxpy 1.9 it reproduces the current file byte for byte; other versions may
find different certificates, which the verifier checks just the same. It
imports the model from the verifier, so the two programs always describe the
same relaxation.

- For 740 maps a linear program finds the multipliers directly.
- For the other 28, the program first solves a semidefinite program. It then
  rounds that program's dual matrices to rational PSD matrices Z, which give
  the cuts ⟨Z, P⟩ ≥ 0.

The floating-point solvers are only used to find the certificates. The
verifier does not depend on them.
