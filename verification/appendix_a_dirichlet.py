"""Appendix A: the upper bound for beta_m (Lemma A.1), and rational bounds for
beta_m used elsewhere.

Recall beta_m = 1 - min_t D_m(t), where D_m(t) = sin((m + 1/2)t)/sin(t/2) is
the Dirichlet kernel, and N = 2m + 1.

Claims checked here
-------------------
* Lemma A.1, first part: beta_m <= 1 + kappa N / sinc(3 pi/(2N)).  This is an
  analytic argument.  We only compare it numerically (floating point) with a
  finely sampled minimum of D_m for a few m, as an illustration.
* Lemma A.1, second part: beta_m <= 1 + 525(2m+1)/2399 for m >= 46.  Every
  numerical step of the proof is checked exactly.

The functions beta_lower and beta_upper give rigorous rational bounds for
beta_m: the lower bound is Lemma 2.1 (beta_m > 1 + kappa N), and the upper
bound is the first part of Lemma A.1 with sinc(x) >= 1 - x^2/6.
"""
from fractions import Fraction
import math

from exact import check, KAPPA_LOWER, KAPPA_UPPER, PI_LOWER, PI_UPPER


def beta_lower(m):
    """A rational number < beta_m (Lemma 2.1)."""
    return 1 + KAPPA_LOWER * (2 * m + 1)


def beta_upper(m):
    """A rational number >= beta_m (Lemma A.1).  Since sin x >= x - x^3/6,
    sinc(x0) >= 1 - x0^2/6, and x0 = 3 pi/(2N) is at most 3 PI_UPPER/(2N)."""
    N = 2 * m + 1
    x0_high = 3 * PI_UPPER / (2 * N)
    check(x0_high ** 2 < 6, "the sinc bound needs x0 < sqrt 6")
    return 1 + KAPPA_UPPER * N / (1 - x0_high ** 2 / 6)


# ----------------------------------------------------------------------------
# The rational consequence
# ----------------------------------------------------------------------------

def check_rational_consequence():
    """Lemma A.1: for m >= 46, beta_m <= 1 + 525(2m+1)/2399.  The proof:
    kappa < 1/sqrt 21; for N >= 93, x0 = 3 pi/(2N) < 1/19, so
    sinc(x0) > 1 - x0^2/6 > 1 - 1/(6 * 19^2) = 2165/2166; and
    2166/(2165 sqrt 21) < 525/2399."""
    # kappa < 1/sqrt 21.  The paper derives this from alpha > sqrt 20, which
    # in turn uses 3 pi/2 > sqrt 20 + 1/sqrt 20 = 21/sqrt 20 and
    # pi > 157/50 > 7/sqrt 5.  We check that route, and also kappa < 1/sqrt 21
    # directly from the bound in exact.py.
    check(PI_LOWER > Fraction(157, 50), "pi > 157/50")
    check(Fraction(157, 50) ** 2 > Fraction(49, 5), "157/50 > 7/sqrt 5")
    check((Fraction(3, 2) * 7) ** 2 / 5 == Fraction(21) ** 2 / 20,
          "(3/2)(7/sqrt 5) = 21/sqrt 20")
    check(KAPPA_UPPER ** 2 < Fraction(1, 21), "kappa < 1/sqrt 21")
    # m >= 46 means N >= 93, and then x0 = 3 pi/(2N) <= 3 pi/186 < 1/19.
    check(3 * PI_UPPER / (2 * 93) < Fraction(1, 19), "x0 < 1/19")
    check(1 - Fraction(1, 6 * 19 ** 2) == Fraction(2165, 2166), "1 - 1/2166 = 2165/2166")
    # 2166/(2165 sqrt 21) < 525/2399, squared and cleared of denominators:
    check((2166 * 2399) ** 2 < 21 * (2165 * 525) ** 2, "2166/(2165 sqrt 21) < 525/2399")


# ----------------------------------------------------------------------------
# The sinc bound, numerically
# ----------------------------------------------------------------------------

def sampled_dirichlet_minimum(m, samples=200000):
    """The minimum of D_m(t) over the sample points t = pi i/samples,
    0 < i <= samples (floating point).  The first dip has width about
    2 pi/N, far wider than the spacing pi/samples."""
    N = 2 * m + 1
    return min(math.sin(N * t / 2) / math.sin(t / 2)
               for t in (math.pi * i / samples for i in range(1, samples + 1)))


def check_sinc_bound_numerically():
    """Lemma 2.1 and Lemma A.1 together say 1 + kappa N < beta_m <=
    1 + kappa N / sinc(3 pi/(2N)).  We compare both with the sampled minimum
    for a few m (floating point; an illustration, not a proof).  The sampled
    value is slightly below the true beta_m, so it illustrates the lower
    inequality well and the upper one only roughly."""
    kappa = float(KAPPA_LOWER)
    for m in (1, 2, 5, 10, 46, 100):
        N = 2 * m + 1
        beta = 1 - sampled_dirichlet_minimum(m)
        x0 = 3 * math.pi / (2 * N)
        bound = 1 + kappa * N / (math.sin(x0) / x0)
        check(1 + kappa * N < beta <= bound + 1e-9, f"m = {m}")


CHECKS = [
    ("Lemma A.1", "the rational bound 1 + 525(2m+1)/2399 for m >= 46",
     check_rational_consequence),
    ("Lemma A.1", "the sinc bound against a sampled minimum (numerical)",
     check_sinc_bound_numerically),
]
