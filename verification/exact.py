"""Exact arithmetic shared by all the checks.

Everything in this package is done with Python integers and fractions, so
there is no rounding.  The only irrational numbers the paper needs are pi,
square roots, and Leech's constant

    kappa = -min_{x>0} sin(x)/x = 0.21723362821...

For these we compute rational lower and upper bounds; the reasons the bounds
are valid are written out in the comments below.  A check that uses kappa
uses whichever of the two bounds makes the inequality harder to satisfy.
For example, "positivity excludes the graph" means trace <= 1 + kappa(2m+1);
the right side grows with kappa, so we confirm it with KAPPA_LOWER.

Reading guide
-------------
    check(condition, message)       raise CheckFailed unless condition holds
    ceil_div(a, b)                  the integer ceiling of a/b
    interval_inside(...)            for checking printed decimals
    PI_LOWER < pi < PI_UPPER        from Machin's formula
    cos_bounds(y), sin_bounds(y)    rational bounds for 0 <= y <= 1
    sqrt_lower(x), sqrt_upper(x)    rational bounds for the square root of a rational
    KAPPA_LOWER < kappa < KAPPA_UPPER
"""
from fractions import Fraction
from math import isqrt


class CheckFailed(Exception):
    """Raised when a claim of the paper is not confirmed."""


def check(condition, message):
    """Raise CheckFailed(message) unless `condition` is true."""
    if not condition:
        raise CheckFailed(message)


def ceil_div(a, b):
    """The ceiling of a/b, for integers (or Fractions) a and b > 0."""
    return -(-a // b)


def interval_inside(low_value, high_value, low, high):
    """Is [low_value, high_value] inside [low, high)?  Used for printed
    decimals: "x is about 0.2172" is checked as 0.21715 <= x < 0.21725, given
    rational bounds low_value <= x <= high_value."""
    return Fraction(low) <= low_value and high_value < Fraction(high)


# ----------------------------------------------------------------------------
# Alternating series
# ----------------------------------------------------------------------------
#
# All the series below are alternating, with terms that decrease in absolute
# value.  For such a series, consecutive partial sums lie on opposite sides
# of the limit, so the last two partial sums are a lower and an upper bound.

def last_two_partial_sums(terms):
    """(lower, upper) from the last two partial sums of a finite list of
    terms of an alternating series with decreasing absolute values."""
    total, previous = Fraction(0), None
    for term in terms:
        previous, total = total, total + term
    return min(previous, total), max(previous, total)


# ----------------------------------------------------------------------------
# pi
# ----------------------------------------------------------------------------

def arctan_inverse_bounds(k, number_of_terms):
    """Bounds (lower, upper) for arctan(1/k), k >= 2, from

        arctan(x) = x - x^3/3 + x^5/5 - ...      (0 < x <= 1)."""
    x = Fraction(1, k)
    return last_two_partial_sums((-1) ** i * x ** (2 * i + 1) / (2 * i + 1)
                                 for i in range(number_of_terms))


def pi_bounds(number_of_terms=13):
    """Rational bounds (lower, upper) for pi from Machin's formula

        pi = 16 arctan(1/5) - 4 arctan(1/239).

    The lower bound combines the lower bound for arctan(1/5) with the upper
    bound for arctan(1/239), and vice versa.  Thirteen terms give an
    interval of width about 2e-18."""
    lo5, hi5 = arctan_inverse_bounds(5, number_of_terms)
    lo239, hi239 = arctan_inverse_bounds(239, number_of_terms)
    return 16 * lo5 - 4 * hi239, 16 * hi5 - 4 * lo239


PI_LOWER, PI_UPPER = pi_bounds()


# ----------------------------------------------------------------------------
# Sine, cosine and square roots
# ----------------------------------------------------------------------------

def cos_bounds(y, number_of_terms=9):
    """Bounds (lower, upper) for cos(y), for a rational 0 <= y <= 1, from
    cos(y) = 1 - y^2/2! + y^4/4! - ...  (alternating and decreasing for y <= 1)."""
    check(0 <= y <= 1, "cos_bounds needs 0 <= y <= 1")
    terms, factorial = [], 1
    for i in range(number_of_terms):
        if i > 0:
            factorial *= (2 * i - 1) * (2 * i)          # factorial = (2i)!
        terms.append((-1) ** i * Fraction(y) ** (2 * i) / factorial)
    return last_two_partial_sums(terms)


def sin_bounds(y, number_of_terms=9):
    """Bounds (lower, upper) for sin(y), for a rational 0 <= y <= 1, from
    sin(y) = y - y^3/3! + y^5/5! - ..."""
    check(0 <= y <= 1, "sin_bounds needs 0 <= y <= 1")
    terms, factorial = [], 1
    for i in range(number_of_terms):
        if i > 0:
            factorial *= (2 * i) * (2 * i + 1)          # factorial = (2i+1)!
        terms.append((-1) ** i * Fraction(y) ** (2 * i + 1) / factorial)
    return last_two_partial_sums(terms)


def sqrt_lower(x, digits=12):
    """A rational number <= sqrt(x), within 10^-digits of it: the integer
    square root of x * 10^(2 digits), divided by 10^digits."""
    x = Fraction(x)
    scale = 10 ** digits
    return Fraction(isqrt(x.numerator * scale * scale // x.denominator), scale)


def sqrt_upper(x, digits=12):
    """A rational number >= sqrt(x), within 2 * 10^-digits of it."""
    candidate = sqrt_lower(x, digits) + Fraction(1, 10 ** digits)
    check(candidate * candidate >= x, "sqrt_upper failed")
    return candidate


# ----------------------------------------------------------------------------
# Leech's constant kappa (Lemma 2.1)
# ----------------------------------------------------------------------------
#
# Lemma 2.1: the minimum of sin(x)/x over x > 0 is attained at the root alpha
# of tan(alpha) = alpha in (pi, 3pi/2), alpha = 4.4934094579..., so
#
#     kappa = -sin(alpha)/alpha = 1/sqrt(1 + alpha^2).
#
# (The second form: tan(alpha) = alpha with alpha in the third quadrant gives
# sin(alpha) = -alpha/sqrt(1 + alpha^2).)  We take the trial point
# a0 = 4.4934094579 and write y = 3pi/2 - a0, so that -sin(a0) = cos(y) and
# tan(a0) = cot(y).  The bounds on pi show 0 < y < 1, so a0 lies in
# (pi, 3pi/2) and the Taylor bounds above apply to y.
#
# Lower bound.  kappa >= -sin(x)/x for EVERY x > 0, by the definition as a
# minimum; take x = a0.
#
# Upper bound.  tan(x) - x is increasing on (pi, 3pi/2) (its derivative is
# tan(x)^2 > 0) and vanishes at alpha.  So if tan(a0) < a0 then a0 < alpha,
# and kappa = 1/sqrt(1 + alpha^2) < 1/sqrt(1 + a0^2).  This uses Lemma 2.1's
# statement that the minimum is attained at alpha.

ALPHA_TRIAL = Fraction(44934094579, 10 ** 10)    # a0, just below alpha


def _kappa_bounds():
    # We do not know y exactly, only that y_low <= y <= y_high.
    y_low = 3 * PI_LOWER / 2 - ALPHA_TRIAL
    y_high = 3 * PI_UPPER / 2 - ALPHA_TRIAL
    check(0 < y_low < y_high < 1, "unexpected range for y")

    # cos is decreasing on [0, 1], so -sin(a0) = cos(y) >= cos(y_high).
    lower = cos_bounds(y_high)[0] / ALPHA_TRIAL

    # cot is decreasing on (0, 1], so tan(a0) = cot(y) <= cot(y_low).
    sin_y_low = sin_bounds(y_low)[0]
    check(sin_y_low > 0, "the lower bound for sin(y) must be positive")
    tan_a0_upper = cos_bounds(y_low)[1] / sin_y_low
    check(tan_a0_upper < ALPHA_TRIAL, "could not certify a0 < alpha")
    upper = sqrt_upper(1 / (1 + ALPHA_TRIAL ** 2), digits=16)
    return lower, upper


KAPPA_LOWER, KAPPA_UPPER = _kappa_bounds()


def describe_constants():
    """Summary printed by run_all.py.  Lower bounds are rounded down and
    upper bounds rounded up, so the printed intervals are also valid."""
    def decimal(x, places, round_up):
        if round_up:
            scaled = ceil_div(x.numerator * 10 ** places, x.denominator)
        else:
            scaled = x.numerator * 10 ** places // x.denominator
        whole, rest = divmod(scaled, 10 ** places)
        return f"{whole}.{rest:0{places}d}"
    return ("Rational bounds used throughout:\n"
            f"  {decimal(PI_LOWER, 20, False)} < pi    < {decimal(PI_UPPER, 20, True)}\n"
            f"  {decimal(KAPPA_LOWER, 13, False)}        < kappa < {decimal(KAPPA_UPPER, 13, True)}")
