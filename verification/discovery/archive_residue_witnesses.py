"""Turn the output of find_residue_witnesses.cpp into the archive
data/residue_witnesses.json.

Like the C++ program, this is part of how the data was produced, not of the
verification; run_all.py checks the archive independently.

Each line of the search output gives part sizes, a modulus q and a residue
map that satisfies the residue equations.  Adding a constant to every residue
preserves all differences, so we try the q translates in turn and keep the
first one that also respects the capacities (at most floor((m - j)/q) + 1
vertices with residue j).  Each kept map is checked with the same function
that run_all.py uses.

Usage, from the verification directory:
    python discovery/archive_residue_witnesses.py search_output.txt --output data/residue_witnesses.json
"""
from pathlib import Path
import argparse
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from sec3_parity import check_one_residue_map     # noqa: E402
from exact import CheckFailed                     # noqa: E402


def parse_line(line):
    words = line.split()
    parts = [int(s) for s in words[0].rstrip(",").split(",")]
    return parts, int(words[1]), [int(x) for x in words[2:]]


def capacity_respecting_translate(parts, q, residues):
    for shift in range(q):
        record = {"parts": parts, "modulus": q,
                  "residues": [(x + shift) % q for x in residues]}
        try:
            check_one_residue_map(record)
            return record
        except CheckFailed:
            continue
    raise CheckFailed(f"no translate of the map for {parts}, q = {q} fits the capacities")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("search_output", type=Path)
    parser.add_argument("--output", type=Path, default=Path("residue_witnesses.json"))
    args = parser.parse_args()
    raw = args.search_output.read_bytes()
    # (Windows PowerShell's ">" writes UTF-16 with a byte-order mark.)
    text = raw.decode("utf-16") if raw[:2] in (b"\xff\xfe", b"\xfe\xff") else raw.decode("utf-8")
    records = [capacity_respecting_translate(*parse_line(line))
               for line in text.splitlines() if line.strip()]
    args.output.write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {len(records)} checked maps to {args.output}")


if __name__ == "__main__":
    main()
