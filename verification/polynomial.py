"""A very small exact polynomial class, used to check algebraic identities.

An identity such as

    sum_{j=1}^{h-1} (4j-1) C(h-j+1, 2) = h(h-1)(h+1)^2 / 6

is checked by expanding both sides into monomials and comparing the
coefficients exactly.  This proves the identity for ALL values of the
variables, not just for sampled values.

A polynomial is stored as a dictionary {monomial: coefficient}, where a
monomial is a sorted tuple of variable names (with repetition, so h^2 is
('h', 'h')) and the empty tuple stands for the constant 1.  Coefficients are
integers or Fractions.  Only the operations needed in this package exist.
"""
from fractions import Fraction


class Poly:
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = dict(value.terms)
        elif isinstance(value, dict):
            self.terms = {mono: c for mono, c in value.items() if c != 0}
        elif isinstance(value, (int, Fraction)):
            self.terms = {(): value} if value != 0 else {}
        else:
            raise TypeError("coefficients must be integers or Fractions")

    @classmethod
    def var(cls, name):
        """The polynomial consisting of the single variable `name`."""
        return cls({(name,): 1})

    # arithmetic -------------------------------------------------------------

    def __add__(self, other):
        result = dict(self.terms)
        for mono, c in Poly(other).terms.items():
            result[mono] = result.get(mono, 0) + c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({mono: -c for mono, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-Poly(other))

    def __rsub__(self, other):
        return Poly(other) - self

    def __mul__(self, other):
        other = Poly(other)
        result = {}
        for mono1, c1 in self.terms.items():
            for mono2, c2 in other.terms.items():
                mono = tuple(sorted(mono1 + mono2))
                result[mono] = result.get(mono, 0) + c1 * c2
        return Poly(result)

    __rmul__ = __mul__

    def __truediv__(self, number):
        """Division by a nonzero integer or Fraction (not by a polynomial)."""
        return self * (Fraction(1) / number)

    def __pow__(self, exponent):
        result = Poly(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        return self.terms == Poly(other).terms

    # helpers ----------------------------------------------------------------

    def substitute(self, name, value):
        """Replace the variable `name` by `value` (a number or a Poly)."""
        result = Poly(0)
        for mono, c in self.terms.items():
            power = mono.count(name)
            rest = tuple(x for x in mono if x != name)
            result = result + Poly({rest: c}) * Poly(value) ** power
        return result

    def coefficients(self):
        return list(self.terms.values())

    def __repr__(self):
        return f"Poly({self.terms})"


def sum_over(polynomial, variable, upper):
    """The sum of `polynomial` over variable = 1, 2, ..., upper.

    `upper` may itself be a polynomial (for example h - 1).  We use the
    classical closed forms for sums of j^0, j^1, j^2, j^3; the polynomials in
    this package never need higher powers.
    """
    U = Poly(upper)
    power_sums = [U,
                  U * (U + 1) / 2,
                  U * (U + 1) * (2 * U + 1) / 6,
                  (U * (U + 1) / 2) ** 2]
    result = Poly(0)
    for mono, c in polynomial.terms.items():
        power = mono.count(variable)
        if power > 3:
            raise ValueError("powers above 3 are not supported")
        rest = tuple(x for x in mono if x != variable)
        result = result + Poly({rest: c}) * power_sums[power]
    return result


def all_coefficients_positive(polynomial):
    """True if the constant term and every other coefficient are positive, so
    that the value is positive whenever all the variables are >= 0.  (Used
    as: p(r) > 0 for all r >= r0, by checking p(r0 + u) in the variable u.)"""
    return (polynomial.terms.get((), 0) > 0
            and all(c > 0 for c in polynomial.coefficients()))


def variables(names):
    """Poly variables from a space-separated string: variables("n r t")."""
    return [Poly.var(name) for name in names.split()]
