# Verification scripts for "Tools for proving that graphs are not graceful" (version 2)

These scripts check the finite and numerical claims of the paper: explicit
labelings, thresholds, decimal constants, polynomial identities, the
rational numbers in the proof of Theorem 4.18, and the data behind
Figure 5. They check the computational steps of the proofs, not the
proofs' reasoning; that is in the paper.

## Running

From this directory:

```
python run_all.py
```

Python 3.9 or later, standard library only. The run takes about ten seconds and
lists every check next to the paper result it belongs to, ending with
`46 of 46 checks passed`. The exit status is nonzero if anything fails.

```
python run_all.py --list     # list the checks without running them
python run_all.py sec4       # run only the modules whose names contain "sec4"
python -c "import sec3_parity as s; s.check_K6_modulo_31()"    # run one check
```

`figures.py` compares its output with `../mapdata.tex`, the data file the
paper's source reads for Figure 5, so it expects to sit in a subdirectory
of the paper's source directory. `python figures.py --write` regenerates
that file.

## How the checks are exact

Except in the few numerical checks listed below, all arithmetic uses Python
integers and `fractions.Fraction`, so nothing is rounded. The irrational numbers the paper needs are pi, a few square roots,
and Leech's constant kappa = -min sin(x)/x = 0.21723362821... `exact.py`
computes rational lower and upper bounds for them, with the reasons written
out in comments: Machin's formula and alternating Taylor series for pi, sin
and cos, integer square roots for square roots, and for kappa the argument
of Lemma 2.1 at a trial point. A check that uses kappa uses whichever bound
makes the inequality harder to satisfy: a claim that positivity *excludes* a
graph (trace <= 1 + kappa(2m+1)) is checked with the lower bound on kappa,
and a remark that it *does not* is checked with the upper bound.

A claim about infinitely many parameters ("for all r >= 46") is checked the
way the paper proves it. The algebraic steps are checked as polynomial
identities with `polynomial.py`, which compares coefficients and so proves
them for all values of the variables; inequalities are checked at the base
case, and monotonicity is checked through an identity for the increment or
the derivative. A claim that depends only on a residue (say n mod 12) is
checked on one full period. Each check's docstring says which of these it
does.

Some checks are finite loops over small parameters. These are sanity
checks of the conclusion (for example, that the bound of Theorem 5.1 never
exceeds the length of an optimal Golomb ruler for r <= 28), not the proof,
and their comments say so. The construction in the proof of Lemma 5.3 is
also checked only on actual graphs with r < 26.

A few checks are numerical (floating point), and their descriptions say so:
the values shown in Figures 2 and 4, the attainment in the plane in
Proposition 4.10, and a comparison of the bound of Lemma A.1 with a sampled
minimum of the Dirichlet kernel. No proof in the paper depends on them.

## Files

| File | Contents |
| --- | --- |
| `run_all.py` | runs everything below |
| `exact.py` | `check`, and rational bounds for pi, sin, cos, square roots and kappa |
| `polynomial.py` | a small exact polynomial class for checking identities |
| `graphs.py` | graph constructions (cliques, complete multipartite graphs, products, Kneser graphs), the two sides of the master identity, and the test for a graceful labeling |
| `sec2_identity.py` | Figure 1 and identity (1); Lemma 2.1; the rho-labelings of Section 2.1 |
| `sec3_parity.py` | Section 3 (Tool I): Bosak's condition, Golomb's cut and iterated parity, residues, Corollaries 3.7 and 3.8, Section 3.5 |
| `sec4_positivity.py` | Sections 4.1-4.6 (Tool II): Corollaries 4.4-4.14, Theorem 4.6, Proposition 4.10, the K4-snakes |
| `sec4_planar_kneser.py` | Section 4.7 and Appendix B: Theorem 4.18 and Corollary 4.19 for K(11,2) |
| `sec5_interval.py` | Section 5 (Tool III): Theorem 5.1 to Corollary 5.5 |
| `appendix_a_dirichlet.py` | Appendix A: Lemma A.1, and the rational bounds for beta_m used elsewhere |
| `figures.py` | Figures 2, 4 and 5 |
| `data/residue_witnesses.json` | the residue maps of Section 3.5 |
| `data/residue_maps_K6_join_4.json` | residue maps of K6 v complement(K4) for 2 <= q <= 16 (the remark after Corollary 3.9) |
| `discovery/` | the searches that found those maps (see below) |

Each module begins with a list of the claims it checks and ends with a list
`CHECKS` of `(paper reference, description, function)`. Each check function
has a docstring that states the claim in the paper's notation, so a module
can be read from top to bottom alongside the paper.

## Paper result -> check

| Paper | Function |
| --- | --- |
| Figure 1, identity (1) | `sec2_identity.check_figure_1_and_identity` |
| Lemma 2.1 | `sec2_identity.check_lemma_2_1_decimals` |
| Section 2.1 (rho-labelings) | `sec2_identity.check_rho_labelings_of_K444_and_K555` |
| Section 3.1, Example 3.4 | `sec3_parity.check_bosak_examples` |
| Section 3.2, Proposition 3.5, Example 3.6 | `sec3_parity.check_K8_and_K9_examples`, `check_complete_graph_table` |
| Section 3.3 (K6 modulo 31) | `sec3_parity.check_K6_modulo_31` |
| Corollary 3.7 | `sec3_parity.check_corollary_3_7_modulus_3` |
| Identity (2), Corollary 3.8 | `sec3_parity.check_identity_2_on_examples`, `check_corollary_3_8` |
| Corollary 3.9 and the remark after it (K6 v complement(K4)) | `sec3_parity.check_corollary_3_9_gaussian`, `check_K6_join_4` |
| Section 3.5 | `sec3_parity.check_windmill_cut_counts`, `check_residue_equations_up_to_12` |
| Decimal constants (Section 4, Table 1) | `sec4_positivity.check_decimal_constants` |
| Corollary 4.4 | `sec4_positivity.check_corollary_4_4` |
| Corollary 4.5 | `sec4_positivity.check_corollary_4_5` |
| Theorem 4.6 | `sec4_positivity.check_theorem_4_6` |
| Section 4.4: two or three K4's; K4-snakes | `sec4_positivity.check_two_or_three_K4`, `check_K4_snakes` |
| Corollary 4.8(c) | `sec4_positivity.check_corollary_4_8c` |
| Corollary 4.9 | `sec4_positivity.check_corollary_4_9` |
| Proposition 4.10 | `sec4_positivity.check_proposition_4_10` |
| Corollary 4.11 | `sec4_positivity.check_corollary_4_11` |
| Corollary 4.12 and the remarks after it | `sec4_positivity.check_paley` |
| Corollaries 4.13, 4.14(a), (b) | `sec4_positivity.check_ramanujan_random_and_lambda_2` |
| Corollary 4.14(c) | `sec4_positivity.check_polarity_graphs` |
| Values of mu in Section 4.3 and Section 7 (items 1-2) | `sec4_positivity.check_multipartite_values` |
| Theorem 4.18, Appendix B | `sec4_planar_kneser.check_incidence_identities`, `check_moment_identities`, `check_fourth_moment_bound_and_quartic` |
| Corollary 4.19 | `sec4_planar_kneser.check_kappa_383`, `check_deletion_and_edit_margins`, `check_sdp_comparison` |
| Section 4.7, the paragraph after Corollary 4.19 | `sec4_planar_kneser.check_deletion_and_edit_margins`, `check_bosak_remark` |
| Theorem 5.1 | `sec5_interval.check_theorem_5_1` |
| Corollary 5.2 | `sec5_interval.check_corollary_5_2` |
| Lemma 5.3 | `sec5_interval.check_balanced_class_inequality`, `check_lemma_5_3_construction` |
| Proposition 5.4 | `sec5_interval.check_proposition_5_4` |
| Corollary 5.5 and the discussion after it | `sec5_interval.check_corollary_5_5` |
| Lemma A.1 | `appendix_a_dirichlet.check_rational_consequence`, `check_sinc_bound_numerically` |
| Figures 2, 4, 5 | `figures.check_figure_2`, `check_figure_4`, `check_figure_5` |

Three items are checked beyond what the paper prints: a rho-labeling of
K_{5,5,5} (the paper only says one exists), a graceful labeling of the
K4-snake with t = 5 (reported by Dore-Hall), and a few "extra" inequalities
marked as such in the code, showing where a margin runs out.

## What is not checked here

* The reasoning of the general proofs (Theorem 4.1, Lemma 4.2,
  Proposition 4.15, and so on). The scripts check their computational
  steps only.
* Results quoted from the literature, such as Golomb's criterion (checked
  only for n < 200), the spectra of standard families, and the verification
  of the Beutner-Harborth conjecture up to 23 vertices.
* The author's search extending that verification to 26 vertices
  (Section 7), which the paper reports but does not reproduce.

## The residue maps and `discovery/`

Section 3.5 states that for K_{3,3,3}, K_{2,2,2,2,2}, K_{4,4,4} and K_{3,4,5}
the residue equations, together with the capacities, are solvable for every
modulus 2 <= q <= 12. The file `data/residue_witnesses.json` is a list of
44 records (4 graphs times 11 moduli) of the form

```
{"parts": [3, 4, 5], "modulus": 7, "residues": [0, 3, ...]}
```

where `residues` lists the residue of each vertex, part by part (the
vertex order of `graphs.complete_multipartite`). `sec3_parity.py` checks
each record exactly.

The maps were found by `discovery/find_residue_witnesses.cpp` (simulated
annealing) and translated to respect the capacities by
`discovery/archive_residue_witnesses.py`. These two programs record how
the data was produced; the check does not depend on them. To reproduce the
archive with g++ (other compilers may give different but equally valid maps),
from this directory:

```
g++ -O2 -o residue_search discovery/find_residue_witnesses.cpp
./residue_search > search_output.txt
python discovery/archive_residue_witnesses.py search_output.txt --output data/residue_witnesses.json
```

This overwrites the archive in `data/`.

The maps for K6 v complement(K4) in `data/residue_maps_K6_join_4.json` are
found directly by `discovery/find_split_residue_maps.py` (under a second):

```
python discovery/find_split_residue_maps.py --output data/residue_maps_K6_join_4.json
```

## Authorship

The scripts were written by Claude Opus 5.5 (Anthropic) for version 2 of the
paper, partly adapted from scripts by GPT-6 Pro (OpenAI) in its revision of
version 1.
