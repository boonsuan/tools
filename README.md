# Tools for proving that graphs are not graceful

[![verify](https://github.com/boonsuan/tools/actions/workflows/verify.yml/badge.svg)](https://github.com/boonsuan/tools/actions/workflows/verify.yml)

Source and verification scripts for the paper *Tools for proving that graphs
are not graceful* by Boon Suan Ho (version 2). The text of the paper was
written by Claude Opus 5.5 (Anthropic), at the direction of the author; see
the box "About this article" at the start of the paper and its Section 6 for
how the results were found.

| Path | Contents |
| --- | --- |
| `tools.pdf` | the paper |
| `tools.tex`, `mapdata.tex` | its LaTeX source (`mapdata.tex` holds the data for Figure 5) |
| `verification/` | Python scripts that check the finite and numerical claims of the paper |

## Checking the paper's claims

```
cd verification
python run_all.py
```

This needs Python 3.9 or later and nothing else. It runs 44 checks in a few
seconds, each labelled with the result of the paper it belongs to. See
[`verification/README.md`](verification/README.md) for what is checked, how
(exact rational arithmetic and polynomial identities), and what is not.

GitHub Actions runs the same checks on every push (badge above), and also
reruns the search in `verification/discovery/` to confirm that it reproduces
the stored residue maps exactly.

## Building the paper

```
pdflatex tools.tex
pdflatex tools.tex
```
