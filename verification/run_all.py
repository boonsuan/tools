"""Run every check in this directory and report the results.

    python run_all.py            run everything (a few seconds)
    python run_all.py --list     list the checks without running them
    python run_all.py sec4       run only the modules whose names contain "sec4"

Each module corresponds to a part of the paper and ends with a list CHECKS of
(paper reference, description, function).  A function returns normally when
the claim holds and raises CheckFailed otherwise.  The exit status is nonzero
if any check fails.
"""
import sys
import time
import traceback

sys.dont_write_bytecode = True

import exact                                           # noqa: E402
import sec2_identity, sec3_parity, sec4_positivity     # noqa: E402
import sec4_planar_kneser, sec5_interval               # noqa: E402
import appendix_a_dirichlet, figures                   # noqa: E402

MODULES = [sec2_identity, sec3_parity, sec4_positivity, sec4_planar_kneser,
           sec5_interval, appendix_a_dirichlet, figures]


def main(arguments):
    listing = "--list" in arguments
    filters = [a for a in arguments if not a.startswith("--")]
    modules = [m for m in MODULES
               if not filters or any(f in m.__name__ for f in filters)]

    print(exact.describe_constants())
    print()
    failures = 0
    start = time.perf_counter()
    for module in modules:
        print(f"{module.__name__}.py")
        for reference, description, function in module.CHECKS:
            label = f"  [{reference}] {description}"
            if listing:
                print(label)
                continue
            began = time.perf_counter()
            try:
                function()
                status = "ok"
            except Exception as error:                 # report and keep going
                failures += 1
                status = f"FAILED: {error}"
                if not isinstance(error, exact.CheckFailed):
                    traceback.print_exc()
            print(f"{label} ... {status} ({time.perf_counter() - began:.1f} s)")
    if not listing:
        total = sum(len(m.CHECKS) for m in modules)
        print()
        print(f"{total - failures} of {total} checks passed "
              f"in {time.perf_counter() - start:.1f} s.")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
