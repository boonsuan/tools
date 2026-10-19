"""Regenerate the data behind the classification of B(n, r, t).

    python reproduce.py            # about half an hour on 16 threads
    python reproduce.py --extras   # about 20 minutes more
    python reproduce.py --check    # a minute or two; used by GitHub Actions
    python reproduce.py --check --all

The default run executes the two C programs in this folder and writes
    endgame_runs.txt          for each (r, t): the end-game search at depth
                              L - 1 (a branch survives) and at depth L (none
                              does);
    complete_search_runs.txt  the complete search for every n with r < n <= n0,
                              where n0 is the smallest n with m >= 2L + 2
                              (so n = n0 is a cross-check of the end-game).
The depths L below were found with `endgame scan`. A surviving branch at
depth L restricts to one at depth L - 1, so the two runs show that L is the
smallest depth at which the search fails.

--extras writes complete_search_extras.txt: complete searches for t = 6 and
7, outside the table.

--check reruns every stored run with t <= 4 (with --all: every stored run,
including the extras) and confirms that the programs print the same verdicts
and, for verdicts that do not stop the search early ("no branch survives",
"not graceful"), the same node counts.

Build the programs first (see README.md); classify.py then checks the data.
"""
import re
import subprocess
import sys
from math import comb
from pathlib import Path

HERE = Path(__file__).parent
DEPTH = {  # (r, t): L
    (2, 2): 13, (2, 3): 26, (2, 4): 39, (2, 5): 54,
    (3, 2): 16, (3, 3): 26, (3, 4): 45, (3, 5): 63,
    (4, 2): 16, (4, 3): 27, (4, 4): 45, (4, 5): 66,
    (5, 2): 16, (5, 3): 27, (5, 4): 47, (5, 5): 66,
}
EXTRAS = [(3, 2, 6), (4, 2, 6), (5, 2, 6), (5, 2, 7), (4, 3, 6), (5, 3, 6),
          (5, 4, 6), (6, 4, 6), (6, 5, 6), (7, 5, 6)]
DATA_FILES = ["endgame_runs.txt", "complete_search_runs.txt"]


def edges(n, r, t):
    return comb(r, 2) + t * (comb(n, 2) - comb(r, 2))


def program(name):
    for path in (HERE / name, HERE / (name + ".exe")):
        if path.exists():
            return str(path)
    sys.exit(f"{name} not found; build it first (see README.md)")


def run(name, args):
    """Run one of the programs; return 'name args: output'."""
    output = subprocess.run([program(name)] + [str(a) for a in args],
                            capture_output=True, text=True, check=True).stdout.strip()
    return " ".join([name] + [str(a) for a in args]) + ": " + output


def write_runs(path, commands):
    with open(path, "w") as log:
        for name, args in commands:
            line = run(name, args)
            print(line, flush=True)
            log.write(line + "\n")
            log.flush()


def summary(line):
    """The part of an output line that must not depend on threads or timing."""
    verdict = re.search(r"(no branch survives|survives|not graceful|graceful)", line).group(1)
    if verdict in ("no branch survives", "not graceful"):
        return verdict + " " + re.search(r"nodes (\d+)", line).group(1)
    return verdict


def check(everything):
    count = 0
    files = DATA_FILES + (["complete_search_extras.txt"] if everything else [])
    for name in files:
        for line in (HERE / name).read_text().splitlines():
            command = line.split(":")[0].split()
            if int(command[-1]) > 4 and not everything:
                continue
            again = run(command[0], command[1:])
            if summary(again) != summary(line):
                sys.exit(f"MISMATCH\n  stored: {line}\n  now:    {again}")
            count += 1
    print(f"{count} stored runs reproduced" + ("" if everything else " (those with t <= 4)"))


def main():
    if "--check" in sys.argv:
        check("--all" in sys.argv)
    elif "--extras" in sys.argv:
        write_runs(HERE / "complete_search_extras.txt",
                   [("complete_search", case) for case in EXTRAS])
    else:
        write_runs(HERE / "endgame_runs.txt",
                   [("endgame", (depth, "B", r, t))
                    for (r, t), L in DEPTH.items() for depth in (L - 1, L)])
        cases = []
        for (r, t), L in DEPTH.items():
            n = r + 1
            while True:
                cases.append(("complete_search", (n, r, t)))
                if edges(n, r, t) >= 2 * L + 2:
                    break
                n += 1
        write_runs(HERE / "complete_search_runs.txt", cases)


if __name__ == "__main__":
    main()
