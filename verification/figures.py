"""The numbers shown in Figures 2, 4 and 5.

Claims checked here
-------------------
* Figure 2 (floating point; an illustration): for m = 31 the first dip is at
  t* = 2 alpha/63 = 0.1426..., where D_31(t*) = -13.70...
* Figure 4 (floating point; an illustration): for the labels 0, 1, 4, 6 at
  t = 2 alpha/13, the points e^{itx} are at angles 0, 39.61, 158.43 and
  237.65 degrees, their sum is (0.305, 0.160), and |sum z_v|^2 is about
  0.12; for K_5 at t = 2 alpha/21 the identity would give about -0.60.
* Figure 5 (exact): every one of the 250 plotted points in ../mapdata.tex
  is regenerated from the spectral formulas below, with exact rounding to
  four decimal places.  Run `python figures.py --write` to regenerate the
  file.

Figure 5 plots (number of vertices, |lambda_min|/degree) for
    Hamming H(d,q), q = 3..12, d = 1..4:           (q^d,     1/(q-1))
    Johnson J(n,k), k = 2..4, n = 2k+1..25:        (C(n,k),  1/(n-k))
    Kneser K(n,k), k = 2, 3, n = 2k+1..39:         (C(n,k),  k/(n-k))
    Paley P(q), q prime, q = 1 (mod 4), q <= 400:  (q,       (1 + sqrt q)/(q-1))
    T(n), n = 5..25, and K_a box K_a, a = 3..29:   (C(n,2),  1/(n-2)) and (a^2, 1/(a-1))
"""
from fractions import Fraction
from math import comb, isqrt
from pathlib import Path
import cmath
import math
import sys

from exact import check, interval_inside, ALPHA_TRIAL, KAPPA_LOWER, KAPPA_UPPER

PAPER_DIRECTORY = Path(__file__).resolve().parent.parent
ALPHA = float(ALPHA_TRIAL)          # 4.4934094579, accurate enough for the figures


def dirichlet(m, t):
    return math.sin((m + 0.5) * t) / math.sin(t / 2)


def rounds_to(value, printed):
    """Does the float `value` round to the printed decimal string?"""
    places = len(printed.split(".")[1])
    return f"{value:.{places}f}" == printed


def check_figure_2():
    """Figure 2: the dotted line at t* = 0.1426 down to D_31(t*) = -13.70."""
    t_star = 2 * ALPHA / 63
    check(rounds_to(t_star, "0.1426"), f"t* = {t_star}")
    check(rounds_to(dirichlet(31, t_star), "-13.70"), f"D_31(t*) = {dirichlet(31, t_star)}")


def check_figure_4():
    """Figure 4: the four points, their sum, and the two values printed."""
    t = 2 * ALPHA / 13
    angles = [math.degrees(x * t) for x in (0, 1, 4, 6)]
    for angle, printed in zip(angles, ("0.00", "39.61", "158.43", "237.65")):
        check(rounds_to(angle, printed), f"angle {angle}")
    total = sum(cmath.exp(1j * t * x) for x in (0, 1, 4, 6))
    check(rounds_to(total.real, "0.305") and rounds_to(total.imag, "0.160"), f"sum {total}")
    value = abs(total) ** 2
    check(rounds_to(value, "0.12"), f"|sum z|^2 = {value}")
    check(abs(value - (4 + dirichlet(6, t) - 1)) < 1e-12, "the identity n + D_m - 1")
    check(rounds_to(5 + dirichlet(10, 2 * ALPHA / 21) - 1, "-0.60"), "the K_5 value")


# ----------------------------------------------------------------------------
# Figure 5
# ----------------------------------------------------------------------------

def four_places(fraction):
    """A nonnegative rational, rounded to four decimal places (ties to even),
    as a string."""
    rounded, remainder = divmod(fraction.numerator * 10000, fraction.denominator)
    if 2 * remainder > fraction.denominator or (2 * remainder == fraction.denominator
                                                and rounded % 2):
        rounded += 1
    return f"{rounded // 10000}.{rounded % 10000:04d}"


def paley_ratio_four_places(q):
    """(1 + sqrt q)/(q - 1), q not a square, rounded to four places exactly:
    put sqrt q between low/scale and (low+1)/scale, and refine until both
    ends round to the same string."""
    scale = 10 ** 4
    while True:
        low = isqrt(q * scale * scale)
        a = four_places(Fraction(scale + low, scale * (q - 1)))
        b = four_places(Fraction(scale + low + 1, scale * (q - 1)))
        if a == b:
            return a
        scale *= 10


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def figure_5_points():
    """The plotted points of each family, as (size, ratio string)."""
    def rounded(points):
        return [(size, four_places(ratio)) for size, ratio in sorted(points)]
    return {
        "hamming": rounded((q ** d, Fraction(1, q - 1))
                           for q in range(3, 13) for d in range(1, 5)),
        "johnson": rounded((comb(n, k), Fraction(1, n - k))
                           for k in range(2, 5) for n in range(2 * k + 1, 26)),
        "kneser": rounded((comb(n, k), Fraction(k, n - k))
                          for k in range(2, 4) for n in range(2 * k + 1, 40)),
        "paley": [(q, paley_ratio_four_places(q))
                  for q in range(5, 401, 4) if is_prime(q)],
        "line": rounded([(comb(n, 2), Fraction(1, n - 2)) for n in range(5, 26)]
                        + [(a * a, Fraction(1, a - 1)) for a in range(3, 30)]),
    }


def figure_5_text():
    """The contents of mapdata.tex: one pgfplots \\addplot per family."""
    lines = []
    for family, points in figure_5_points().items():
        lines.append(f"% {family}")
        lines.append("\\addplot coordinates {"
                     + " ".join(f"({size},{ratio})" for size, ratio in points) + "};")
    return "\n".join(lines) + "\n"


def check_figure_5():
    """Figure 5: ../mapdata.tex is exactly the regenerated data (250 points),
    and the shaded region ends at kappa ~ 0.2172."""
    points = figure_5_points()
    check(sum(len(p) for p in points.values()) == 250, "250 points")
    mapdata = PAPER_DIRECTORY / "mapdata.tex"
    check(mapdata.exists(), f"expected the paper's mapdata.tex at {mapdata}")
    check(mapdata.read_text(encoding="utf-8") == figure_5_text(),
          "mapdata.tex differs from the regenerated data")
    check(interval_inside(KAPPA_LOWER, KAPPA_UPPER, "0.21715", "0.21725"), "the line at 0.2172")


CHECKS = [
    ("Fig. 2", "t* and the first dip of D_31 (numerical)", check_figure_2),
    ("Fig. 4", "the points, their sum, and |sum z|^2 for K_4, K_5 (numerical)", check_figure_4),
    ("Fig. 5", "all 250 plotted points, regenerated exactly", check_figure_5),
]


if __name__ == "__main__":
    # python figures.py           print the data for mapdata.tex
    # python figures.py --write   write it to ../mapdata.tex (UTF-8)
    if "--write" in sys.argv[1:]:
        (PAPER_DIRECTORY / "mapdata.tex").write_text(figure_5_text(), encoding="utf-8")
    else:
        sys.stdout.write(figure_5_text())
