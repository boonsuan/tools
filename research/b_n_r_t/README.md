# B(n, r, t): programs and data

This folder decides which B(n, r, t) are graceful, for 2 ≤ r ≤ 5 and
2 ≤ t ≤ 5. B(n, r, t) is t copies of K_n sharing a common K_r. The method and
the result are explained in [`../README.md`](../README.md); this page says
what each file is and how to rerun everything.

| File | Contents |
| --- | --- |
| [`endgame.c`](endgame.c) | The end-game search. It proves B(n, r, t) ungraceful for all large n at once. |
| [`complete_search.c`](complete_search.c) | The complete search for one graph B(n, r, t). It prints a graceful labeling or proves that none exists. |
| [`reproduce.py`](reproduce.py) | Runs both programs on every case needed and writes the two data files below. |
| [`endgame_runs.txt`](endgame_runs.txt) | For each (r, t): the end-game search at depth L − 1 (some branch survives) and at depth L (none does). |
| [`complete_search_runs.txt`](complete_search_runs.txt) | The complete search for each r < n ≤ n0. |
| [`complete_search_extras.txt`](complete_search_extras.txt) | Complete searches for t = 6 and 7, outside the table. |
| [`classify.py`](classify.py) | Checks the data files and prints the classification. |

## Checking the result

```
python classify.py
```

This needs Python 3.9 or later and nothing else, and takes well under a
second. It reads the data files and checks the following.

- Every graceful labeling in them is verified from scratch: distinct labels
  in 0..m, and edge differences exactly 1..m.
- For each (r, t), the end-game search fails at depth L and survives at
  depth L − 1. Let n0 be the smallest n with m ≥ 2L + 2.
- Every n with r < n < n0 has a complete search.
- No complete search with n ≥ n0 finds a labeling.
- The graceful cases are exactly those claimed in the README.

This check trusts the programs' verdicts ("no branch survives", "not
graceful"). GitHub Actions runs it on every push. It also rebuilds both
programs and runs `python reproduce.py --check`, which reruns every stored
case with t ≤ 4 (a minute or two) and compares verdicts and node counts. The
cases with t = 5 take too long for that; `python reproduce.py --check --all`
reruns every stored case (about an hour on 16 threads).

## Rerunning the searches

The programs need a C compiler with OpenMP (gcc, or clang with libomp).

```
gcc -O3 -march=native -fopenmp -o endgame endgame.c
gcc -O3 -march=native -fopenmp -o complete_search complete_search.c
python reproduce.py
python reproduce.py --extras
python classify.py
```

`reproduce.py` takes about half an hour on 16 threads, and `--extras` about
20 minutes more. The largest single runs are the end-game searches for t = 5,
at about 640 million nodes, and the complete search for B(5, 2, 7), at
6.5 billion. The node counts do not depend on the number of threads or on
the split depth, except in runs that stop early because they found
something.

Each program can also be run by hand:

```
./endgame 13 B 2 2          # depth 13 for two K_n sharing an edge
./endgame scan 1 B 3 4      # increase the depth until the search fails
./endgame 23 kp 2           # Knuth's K_n □ P_2
./complete_search 5 2 4     # a graceful labeling of B(5, 2, 4)
```

Both programs explain their method, and the symmetry reductions they use, in
the comment at the top of the source.

## Cross-checks

- The end-game search reproduces Knuth's K_n □ P_2 case at depth L = 23
  (`./endgame 23 kp 2`).
- For a single clique (`./endgame 5 kp 1`) it fails at L = 5, which gives
  Golomb's theorem for n ≥ 6.
- The complete search reproduces every result of Smith and Puget quoted in
  [`../README.md`](../README.md), and the graceful labelings of B(3, 2, t),
  B(4, 2, t) and B(4, 3, t) known before.
- For each (r, t), the complete search at n = n0 agrees with the end-game.
