"""Find the residue maps of K_6 v complement(K_4) stored in
data/residue_maps_K6_join_4.json (the remark after Corollary 3.9).

Like the other programs in this directory, this records how the data was
produced; run_all.py checks the stored maps independently.

For a split graph K_s v complement(K_N), let c_r and x_r be the numbers of
clique and of independent vertices with residue r (mod q).  The number of
ordered pairs (u, v), uv an edge, with r(u) - r(v) = d is

    sum_r c_r c_(r-d)  - (s if d = 0)   +   sum_b x_b (c_(b+d) + c_(b-d)),

which for fixed c is linear in x.  We try each c and search for x.

Usage, from the verification directory:
    python discovery/find_split_residue_maps.py --output data/residue_maps_K6_join_4.json
"""
from math import comb
from pathlib import Path
import argparse
import json
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from sec3_parity import check_one_residue_map     # noqa: E402

S, N = 6, 4


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def find_map(q):
    m = comb(S, 2) + S * N
    target = [0] * q
    for j in range(1, m + 1):
        target[j % q] += 1
        target[-j % q] += 1
    capacity = [(m - r) // q + 1 for r in range(q)]
    for c in compositions(S, q):
        if any(c[r] > capacity[r] for r in range(q)):
            continue
        need = [target[d] - sum(c[r] * c[(r - d) % q] for r in range(q)) + (S if d == 0 else 0)
                for d in range(q)]
        coefficient = [[c[(b + d) % q] + c[(b - d) % q] for d in range(q)] for b in range(q)]

        def search(b, left, need):
            if b == q:
                return [] if left == 0 and not any(need) else None
            for xb in range(min(left, capacity[b] - c[b]) + 1):
                rest = [need[d] - xb * coefficient[b][d] for d in range(q)]
                if min(rest) < 0:
                    break
                found = search(b + 1, left - xb, rest)
                if found is not None:
                    return [xb] + found
            return None
        x = search(0, N, need)
        if x is not None:
            clique = [r for r in range(q) for _ in range(c[r])]
            independent = [r for r in range(q) for _ in range(x[r])]
            return {"parts": [1] * S + [N], "modulus": q, "residues": clique + independent}
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", type=Path, default=Path("residue_maps_K6_join_4.json"))
    args = parser.parse_args()
    records = []
    for q in range(2, 17):
        record = find_map(q)
        check_one_residue_map(record)
        records.append(record)
    args.output.write_text(json.dumps(records, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {len(records)} checked maps to {args.output}")


if __name__ == "__main__":
    main()
