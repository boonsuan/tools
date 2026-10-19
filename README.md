# Tools for proving that graphs are not graceful

[![verify](https://github.com/boonsuan/tools/actions/workflows/verify.yml/badge.svg)](https://github.com/boonsuan/tools/actions/workflows/verify.yml)

Source and verification scripts for the paper
[*Tools for proving that graphs are not graceful*](https://hexagonmath.org/2610.00316)
(version 2). The text of the paper was written by Claude Opus 5.5
(Anthropic); see the box "About this article" at the start of the paper and
its Section 6 for how the results were found.

| Path | Contents |
| --- | --- |
| `tools.pdf` | the paper |
| `tools.tex`, `mapdata.tex` | its LaTeX source (`mapdata.tex` holds the data for Figure 5) |
| `verification/` | Python scripts that check the finite and numerical claims of the paper |
| `research/` | two results found after the paper, with their programs (not in version 2) |

## Checking the paper's claims

```
cd verification
python run_all.py
```

This needs Python 3.9 or later and nothing else. It runs 47 checks in about ten
seconds, each labelled with the result of the paper it belongs to. See
[`verification/README.md`](verification/README.md) for what is checked, how
(exact rational arithmetic and polynomial identities), and what is not.

GitHub Actions runs the same checks on every push (badge above), and also
reruns the search in `verification/discovery/` to confirm that it reproduces
the stored residue maps exactly.

## Research after the paper

The folder [`research/`](research/) holds two results found after version 2,
which are not in the paper on Hexagon:

- the graceful graphs B(n, r, t) (t copies of K_n sharing a K_r) for
  2 ≤ r, t ≤ 5 and all n, by a finite search that covers all large n at once;
- a proof that K₆ ∨ K̄₄ is not graceful, combining residues, positions and
  positivity.

Both are computer proofs, written by Claude Opus 5.5 and not refereed.
[`research/README.md`](research/README.md) explains the methods. GitHub
Actions checks the stored results on every push.

## Building the paper

```
pdflatex tools.tex
pdflatex tools.tex
```

## License

Everything in this repository, the paper and the scripts, is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), the same license
as the paper on Hexagon; see [`LICENSE`](LICENSE).
