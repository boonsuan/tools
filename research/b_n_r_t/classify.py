"""Check the classification of B(n, r, t) for 2 <= r <= 5 and 2 <= t <= 5.

B(n, r, t) is t copies of K_n sharing a common K_r (n > r); it has
m = C(r,2) + t (C(n,2) - C(r,2)) edges.  The evidence is the output of the
two C programs in this folder, as written by reproduce.py:

  endgame_runs.txt          For each (r, t), the end-game search at depths
                            L - 1 and L.  "no branch survives" at depth L
                            proves that B(n, r, t) is not graceful whenever
                            m >= 2L + 2, that is, for all n >= n0.
  complete_search_runs.txt  The complete search for each r < n <= n0:
                            a graceful labeling, or "not graceful".

This script checks that the two together decide every n > r, verifies every
graceful labeling from scratch, checks that the outcome is the classification
stated in README.md, and prints it.  The labelings in
complete_search_extras.txt (t = 6, 7) are verified too, if that file exists.
"""
import re
import sys
from itertools import combinations
from math import comb
from pathlib import Path

HERE = Path(__file__).parent

# The classification claimed in README.md: (r, t) -> the n for which
# B(n, r, t) is graceful.
CLAIMED = {
    (2, 2): {3, 4, 5}, (2, 3): {3, 4}, (2, 4): {3, 4, 5}, (2, 5): {3, 4, 6},
    (3, 2): {4}, (3, 3): {4, 5}, (3, 4): {4, 5}, (3, 5): {4},
    (4, 2): set(), (4, 3): set(), (4, 4): set(), (4, 5): set(),
    (5, 2): set(), (5, 3): set(), (5, 4): set(), (5, 5): set(),
}


def edges(n, r, t):
    return comb(r, 2) + t * (comb(n, 2) - comb(r, 2))


def is_graceful_labeling(n, r, t, shared, copies):
    """Is this a graceful labeling of B(n, r, t)?  `shared` holds the labels
    of the r shared vertices, copies[g] those of the other vertices of copy g."""
    m = edges(n, r, t)
    if len(shared) != r or len(copies) != t or any(len(c) != n - r for c in copies):
        return False
    labels = shared + [x for c in copies for x in c]
    if len(set(labels)) != len(labels) or not all(0 <= x <= m for x in labels):
        return False
    pairs = list(combinations(shared, 2))
    for c in copies:
        pairs += list(combinations(c, 2)) + [(a, b) for a in shared for b in c]
    return sorted(abs(a - b) for a, b in pairs) == list(range(1, m + 1))


def read_complete_searches(path):
    """{(n, r, t): True/False} from complete_search output; graceful
    labelings are verified on the way."""
    graceful = {}
    for line in path.read_text().splitlines():
        match = re.search(r"B\((\d+),(\d+),(\d+)\) m=(\d+): (graceful|not graceful)", line)
        n, r, t, m = map(int, match.groups()[:4])
        assert m == edges(n, r, t), line
        assert (n, r, t) not in graceful, f"B({n},{r},{t}) appears twice"
        if match.group(5) == "graceful":
            fields = line.split("shared:")[1].split("[nodes")[0].split("|")
            shared = [int(x) for x in fields[0].split()]
            copies = [[int(x) for x in field.split(":")[1].split()] for field in fields[1:]]
            assert is_graceful_labeling(n, r, t, shared, copies), f"bad labeling: {line}"
        graceful[n, r, t] = match.group(5) == "graceful"
    return graceful


def read_endgame_depths(path):
    """{(r, t): L}, where the search fails at depth L and survives at L - 1."""
    outcome = {}
    for line in path.read_text().splitlines():
        match = re.match(r"endgame (\d+) B (\d+) (\d+): L=(\d+): (survives|no branch survives)", line)
        L, r, t, printed_L = map(int, match.groups()[:4])
        assert L == printed_L and (r, t, L) not in outcome, line
        outcome[r, t, L] = match.group(5) == "survives"
    depth = {}
    for (r, t, L), survives in outcome.items():
        if not survives:
            assert outcome.get((r, t, L - 1)) is True, f"no surviving run at depth {L - 1} for (r,t)=({r},{t})"
            depth[r, t] = L
    return depth


def main():
    depth = read_endgame_depths(HERE / "endgame_runs.txt")
    graceful = read_complete_searches(HERE / "complete_search_runs.txt")

    print("B(n,r,t) is graceful exactly for the n listed (and not graceful for all other n > r).")
    print("L: depth at which the end-game search fails; it settles all n >= n0.\n")
    print("        " + "".join(f"t = {t:<18}" for t in range(2, 6)))
    for r in range(2, 6):
        row = f"r = {r}   "
        for t in range(2, 6):
            L = depth[r, t]
            n0 = next(n for n in range(r + 1, 1000) if edges(n, r, t) >= 2 * L + 2)
            for n in range(r + 1, n0):
                assert (n, r, t) in graceful, f"no complete search for B({n},{r},{t})"
            for (n, r2, t2), g in graceful.items():
                assert not (r2 == r and t2 == t and n >= n0 and g), f"B({n},{r},{t}) contradicts the end-game"
            found = {n for n in range(r + 1, n0) if graceful[n, r, t]}
            assert found == CLAIMED[r, t], f"(r,t)=({r},{t}): found {sorted(found)}, claimed {sorted(CLAIMED[r, t])}"
            cell = ("{" + ",".join(map(str, sorted(found))) + "}" if found else "none") + f"  L={L} n0={n0}"
            row += f"{cell:<22}"
        print(row)

    extras = HERE / "complete_search_extras.txt"
    if extras.exists():
        results = read_complete_searches(extras)
        print("\nFurther complete searches (graceful labelings verified):")
        print("  " + ", ".join(f"B({n},{r},{t}) {'graceful' if g else 'not graceful'}"
                               for (n, r, t), g in results.items()))
    print("\nAll checks passed.")


if __name__ == "__main__":
    sys.exit(main())
