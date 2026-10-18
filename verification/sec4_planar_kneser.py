"""Section 4.7 and Appendix B: the planar bound for the Kneser graph K(11,2).

Theorem 4.18 says gamma_2(K(11,2)) <= 26409/64 = 412.64, while mu = 440.
Its proof (Appendix B) is a chain of explicit algebraic steps; we check every
identity and every rational number in it.  Corollary 4.19 then compares this
bound with 2 kappa m after deleting up to seven edges, and with the SDP
value; we check those margins exactly too.

Notation: H = K(11,2) has the 55 pairs {i,j} from {0,...,10} as vertices.
B is the 11 x 55 incidence matrix of K_11 (row i, column {i,j}), and A is
the adjacency matrix of H.

Claims checked here
-------------------
* Theorem 4.18 and Appendix B: B B^T = 9I + J, A = J + I - B^T B,
  36-regular with 990 edges, the eigenvalues 36, -8, 1 with multiplicities
  1, 10, 44, and mu(H) = 440.
* Appendix B: the moment identities (5), the bound (6), the square-root
  identity and the constants 357/16 and 2279/3072, the quartic, its
  reduction and discriminant -2163696, and the final step to 26409/64.
* Corollary 4.19: kappa > 383/1764; the margins for seven deletions (the
  last one is 6143/28224); the SDP matrix X_0 and mu(H_b) > 436 > beta; the
  blowups; and, in the paragraph after it, the edit budget
  44192a + 68704b <= 487070 and which H_b Bosak's condition excludes.
"""
from fractions import Fraction
from itertools import combinations

from exact import check, KAPPA_LOWER, PI_LOWER, PI_UPPER
from polynomial import Poly, variables
from graphs import kneser_graph


def matmul(P, Q):
    """The product of two matrices given as lists of rows."""
    columns = list(zip(*Q))
    return [[sum(a * b for a, b in zip(row, column)) for column in columns] for row in P]


def transpose(P):
    return [list(column) for column in zip(*P)]


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def kneser_matrices():
    """(pairs, B, A) for H = K(11,2), with the 55 pairs in a fixed order."""
    pairs = list(combinations(range(11), 2))
    B = [[int(i in pair) for pair in pairs] for i in range(11)]
    A = [[int(not set(p) & set(p2)) for p2 in pairs] for p in pairs]
    return pairs, B, A


# ----------------------------------------------------------------------------
# The graph and its spectrum
# ----------------------------------------------------------------------------

def check_incidence_identities():
    """Appendix B, first paragraph: B B^T = 9I + J and A = J + I - B^T B;
    H is 36-regular with 990 edges; A has eigenvalues 36, -8, 1 on <1>,
    U = {B^T a : sum a_i = 0} and ker B, of dimensions 1, 10, 44; so
    mu(H) = 55 * 8 = 440."""
    pairs, B, A = kneser_matrices()
    Bt = transpose(B)
    check(matmul(B, Bt) == [[9 * (i == j) + 1 for j in range(11)] for i in range(11)],
          "B B^T = 9I + J")
    BtB = matmul(Bt, B)
    check(A == [[1 + (i == j) - BtB[i][j] for j in range(55)] for i in range(55)],
          "A = J + I - B^T B")
    check(all(sum(row) == 36 for row in A) and sum(map(sum, A)) == 2 * 990,
          "36-regular with 990 edges")
    check(len(kneser_graph(11, 2)[1]) == 990, "edge count from the definition")

    # The spectrum.  (A + 8I)(A - I) = 28J, and A1 = 36 * 1, so on the
    # complement of <1> every eigenvalue is -8 or 1.  For a = e_i - e_10,
    # i < 10 (a basis of the a with sum a_i = 0), A B^T a = -8 B^T a; B^T is
    # injective because B B^T is invertible, so -8 has multiplicity >= 10.
    # Since tr A = 0 = 36 - 8 * 10 + 1 * 44, the multiplicities are exactly
    # 1, 10, 44.
    I55 = identity(55)
    left = [[A[i][j] + 8 * I55[i][j] for j in range(55)] for i in range(55)]
    right = [[A[i][j] - I55[i][j] for j in range(55)] for i in range(55)]
    check(matmul(left, right) == [[28] * 55 for _ in range(55)], "(A + 8I)(A - I) = 28J")
    for i in range(10):
        a = [[int(k == i) - int(k == 10)] for k in range(11)]      # a column vector
        Bta = matmul(Bt, a)
        check(matmul(A, Bta) == [[-8 * x] for (x,) in Bta], "A B^T a = -8 B^T a")
    check(sum(A[i][i] for i in range(55)) == 0 == 36 - 8 * 10 + 1 * 44, "multiplicities")
    # mu = n |lambda_min| = 55 * 8 for a vertex-transitive graph (Prop. 4.15(b)).
    # Directly: A + 8I is positive semidefinite with trace 440, so mu <= 440;
    # check_sdp_comparison below exhibits X_0 with -<A, X_0> = 440, so mu >= 440.
    check(sum(left[i][i] for i in range(55)) == 440, "tr(A + 8I) = 440")


# ----------------------------------------------------------------------------
# Appendix B
# ----------------------------------------------------------------------------

def check_moment_identities():
    """Identity (5): for complex a_0, ..., a_10 with sum a_i = 0 and
    sum |a_i|^2 = 1, and x_ij = |a_i + a_j|^2, Q = sum |a_i|^4,

        sum_{i<j} x_ij = 9,     sum_{i<j} x_ij^2 = 3Q + 2 + |sum a_i^2|^2.

    We prove the homogeneous forms (which hold without sum |a_i|^2 = 1)

        sum_{i<j} x_ij   = 9 S,     sum_{i<j} x_ij^2 = 3Q + 2 S^2 + |sum a_i^2|^2,

    with S = sum |a_i|^2.  Write a_i = p_i + i q_i, eliminate a_10 by the
    zero-sum condition, and compare both sides as real polynomials in the
    remaining 20 variables.  (For 11 points, 9 = 11 - 2 and 3 = 11 - 8.)"""
    points = 11
    a = [(Poly.var(f"p{i}"), Poly.var(f"q{i}")) for i in range(points - 1)]
    a.append((-sum((p for p, _ in a), Poly(0)), -sum((q for _, q in a), Poly(0))))
    squared_norms = [p * p + q * q for p, q in a]
    S = sum(squared_norms, Poly(0))
    Q = sum((w * w for w in squared_norms), Poly(0))
    x = [(p + r) ** 2 + (q + s) ** 2 for (p, q), (r, s) in combinations(a, 2)]
    real_part = sum((p * p - q * q for p, q in a), Poly(0))     # Re sum a_i^2
    imaginary_part = sum((2 * p * q for p, q in a), Poly(0))    # Im sum a_i^2
    check(sum(x, Poly(0)) == 9 * S, "second-moment identity")
    check(sum((v * v for v in x), Poly(0))
          == 3 * Q + 2 * S * S + real_part ** 2 + imaginary_part ** 2,
          "fourth-moment identity")


def check_fourth_moment_bound_and_quartic():
    """Appendix B from (6) to the end."""
    h, sigma = variables("h sigma")

    # (6).  For the pair attaining h, Cauchy-Schwarz gives |a_i|^4 + |a_j|^4
    # >= sigma^2/2 and, for the other nine entries, sum |a_k|^4 >= (1-sigma)^2/9.
    # The function f(sigma) = sigma^2/2 + (1-sigma)^2/9 equals
    # (11/18)(sigma - 2/11)^2 + 1/11, so it increases for sigma >= 2/11, and
    # sigma >= h^2/2 (since |a_i + a_j|^2 <= 2 sigma) >= 2/11.  At sigma = h^2/2
    # it is the right side of (6).
    f = sigma * sigma / 2 + (1 - sigma) ** 2 / 9
    check(f == Fraction(11, 18) * (sigma - Fraction(2, 11)) ** 2 + Fraction(1, 11),
          "f(sigma) = (11/18)(sigma - 2/11)^2 + 1/11")
    lower_Q = Fraction(1, 11) + (11 * h * h - 4) ** 2 / 792          # right side of (6)
    check(f.substitute("sigma", h * h / 2) == lower_Q, "f(h^2/2) is the bound (6)")

    # The square-root identity: with u = sqrt x and w = sqrt rho,
    #   u = w + (u^2 - w^2)/(2w) - (u^2 - w^2)^2/(2w(u + w)^2);
    # multiplied by 2w(u + w)^2 it is a polynomial identity.
    u, w = variables("u w")
    check(2 * w * (u + w) ** 2 * u
          == 2 * w * w * (u + w) ** 2 + (u * u - w * w) * (u + w) ** 2 - (u * u - w * w) ** 2,
          "square-root identity")

    # Sum the identity over the 55 pairs, with rho = 9/64 (so sqrt rho = 3/8):
    #   sum sqrt x = 55 (3/8) + (4/3)(sum x - 55 rho) - (4/3) sum (x - rho)^2/(sqrt x + 3/8)^2.
    # Since sqrt x <= h, the last sum is at least
    #   sum (x - rho)^2/(h + 3/8)^2,  and
    #   sum (x - rho)^2 = sum x^2 - 2 rho sum x + 55 rho^2 >= 3Q + 2 - 18 rho + 55 rho^2
    # by (5).  So sum sqrt x <= 357/16 - (4Q + 2279/3072)/(h + 3/8)^2, where:
    rho = Fraction(9, 64)
    check(1 / (2 * Fraction(3, 8)) == Fraction(4, 3), "1/(2 sqrt rho) = 4/3")
    check(55 * Fraction(3, 8) + Fraction(4, 3) * (9 - 55 * rho) == Fraction(357, 16),
          "the constant 357/16")
    check(Fraction(4, 3) * (2 - 18 * rho + 55 * rho ** 2) == Fraction(2279, 3072),
          "the constant 2279/3072")

    # 357/16 - N/(h + 3/8)^2 <= 173/8 is N >= (357/16 - 173/8)(h + 3/8)^2,
    # i.e. N - (11/16)(h + 3/8)^2 >= 0, where N = 4Q + 2279/3072.  By (6):
    check(Fraction(357, 16) - Fraction(173, 8) == Fraction(11, 16), "357/16 - 173/8 = 11/16")
    quartic = 4 * lower_Q + Fraction(2279, 3072) - Fraction(11, 16) * (h + Fraction(3, 8)) ** 2
    check(quartic == Fraction(11, 18) * h ** 4 - Fraction(163, 144) * h ** 2
          - Fraction(33, 64) * h + Fraction(5021, 4608), "the quartic")
    # Using 2h <= h^2 + 1, i.e. dropping (33/128)(h - 1)^2 >= 0:
    quadratic_in_h2 = (2816 * h ** 4 - 6404 * h ** 2 + 3833) / 4608
    check(quartic - quadratic_in_h2 == Fraction(33, 128) * (h - 1) ** 2,
          "the difference is (33/128)(h - 1)^2")
    check(6404 ** 2 - 4 * 2816 * 3833 == -2163696, "the discriminant")

    # Conclusion.  The unit vectors of U are B^T a/3 (since ||B^T a||^2 = 9||a||^2
    # for a orthogonal to 1), with entries (a_i + a_j)/3; so ||Pz|| <= 173/24.
    # With p = ||Pz||^2 and s the squared length of the component of z along 1,
    # the spectrum gives z*Az = 36 s - 8 p + (55 - s - p), so
    # -z*Az = 9p - 55 - 35s <= 9p - 55:
    p, s = variables("p s")
    check(-(36 * s - 8 * p + (55 - s - p)) == 9 * p - 55 - 35 * s, "-z*Az = 9p - 55 - 35s")
    check(9 * Fraction(173, 24) ** 2 == Fraction(173, 8) ** 2, "9 (173/24)^2 = (173/8)^2")
    check(Fraction(173, 8) ** 2 - 55 == Fraction(26409, 64) == Fraction("412.640625"),
          "(173/8)^2 - 55 = 26409/64 = 412.640625")


# ----------------------------------------------------------------------------
# Corollary 4.19 and the paragraph after it
# ----------------------------------------------------------------------------

GAMMA_BOUND = Fraction(26409, 64)        # Theorem 4.18
KAPPA_383 = Fraction(383, 1764)          # the lower bound for kappa used in the proof


def check_kappa_383():
    """Corollary 4.19: kappa >= -sin(9/2)/(9/2) = (2/9) cos(3pi/2 - 9/2), and
    0 < 3pi/2 - 9/2 < 3/14, so kappa > (2/9)(1 - (3/14)^2/2) = 383/1764."""
    check(PI_LOWER > 3, "pi > 3, so 3pi/2 - 9/2 > 0")
    check(PI_UPPER < Fraction(22, 7), "pi < 22/7")
    check(Fraction(3, 2) * Fraction(22, 7) - Fraction(9, 2) == Fraction(3, 14),
          "so 3pi/2 - 9/2 < (3/2)(22/7) - 9/2 = 3/14")
    check(Fraction(2, 9) * (1 - Fraction(3, 14) ** 2 / 2) == KAPPA_383, "383/1764")
    check(KAPPA_383 < KAPPA_LOWER, "consistent with the sharper bound in exact.py")


def check_deletion_and_edit_margins():
    """Corollary 4.19: with gamma_2(H_b) <= 26409/64 + 2b,
    (383/882)(990 - b) - 26409/64 - 2b >= 6143/28224 > 0 for 0 <= b <= 7.
    After it: with a additions and b deletions the margin is
    (487071 - 44192a - 68704b)/28224, positive when 44192a + 68704b <= 487070,
    for instance for eleven additions."""
    margins = [2 * KAPPA_383 * (990 - b) - GAMMA_BOUND - 2 * b for b in range(8)]
    check(min(margins) == margins[7] == Fraction(6143, 28224) > 0,
          "the smallest margin, at b = 7, is 6143/28224")
    a, b = variables("a b")
    budget = 2 * KAPPA_383 * (990 + a - b) - GAMMA_BOUND - 2 * (a + b)
    check(budget == (487071 - 44192 * a - 68704 * b) / 28224, "the edit budget")
    check(44192 * 11 <= 487070, "eleven additions")
    # (Extra, not claimed in the paper: with these constants, eight deletions
    # or twelve additions would not be covered.)
    check(2 * KAPPA_383 * 982 - GAMMA_BOUND - 16 < 0 and 44192 * 12 > 487070,
          "the margins run out at eight deletions and twelve additions")


def check_sdp_comparison():
    """Corollary 4.19, second paragraph: X_0 = (11/18) B^T (I - J/11) B is
    positive semidefinite with unit diagonal and entry -2/9 on each edge, so
    mu(H_b) >= 440 - (4/9) b >= 3932/9 > 436; and beta_(990-b) <=
    1 + 525 * 1981/2399 < 436, also after blowups.  We work with the integer
    matrix 18 X_0 = B^T (11 I - J) B."""
    pairs, B, A = kneser_matrices()
    middle = [[11 * (i == j) - 1 for j in range(11)] for i in range(11)]
    X18 = matmul(matmul(transpose(B), middle), B)
    check(all(X18[i][i] == 18 for i in range(55)), "unit diagonal")
    check(all(X18[i][j] == -4 for i in range(55) for j in range(55) if A[i][j]),
          "entry -2/9 on every edge")
    # (18 X_0)^2 = 99 (18 X_0): a real symmetric matrix with this property has
    # only the eigenvalues 0 and 99, so it is positive semidefinite.
    check(matmul(X18, X18) == [[99 * x for x in row] for row in X18], "(18 X_0)^2 = 99 (18 X_0)")
    # The objective: -<A, X_0> = 990 * 2 * (2/9) = 440, so mu(H) >= 440.
    check(-sum(A[i][j] * X18[i][j] for i in range(55) for j in range(55)) == 440 * 18,
          "-<A, X_0> = 440")
    # Deleting an edge changes -<A, X_0> by -2 * (2/9).
    check(440 - Fraction(4, 9) * 7 == Fraction(3932, 9) > 436, "mu(H_b) >= 3932/9 > 436")
    # Lemma A.1 (m = 990 - b >= 46): beta_m <= 1 + 525(2m+1)/2399, largest at b = 0.
    beta_bound = 1 + Fraction(525 * 1981, 2399)
    check(2 * 990 + 1 == 1981 and beta_bound < 436, "beta_(990-b) < 436")
    # Blowup by t: m becomes t^2 m, and beta_(t^2 m)/t^2 <= (1 + 525/2399)/t^2
    # + 1050 m/2399, which is largest at t = 1, where it is the bound above.
    check(1 + Fraction(525, 2399) + Fraction(1050 * 990, 2399) == beta_bound, "blowups")


def check_bosak_remark():
    """The paragraph after Corollary 4.19: K(11,2) has even degrees and
    990 = 2 (mod 4), so Bosak excludes it.  For 1 <= b <= 7, H_b has all
    degrees even only if the deleted edges form an even subgraph, which needs
    b >= 3 (one or two edges always leave a vertex meeting exactly one of
    them).  Then 990 - b = 1, 2 (mod 4) only for b = 4, 5, and a deleted 4-cycle
    or 5-cycle shows these occur.  For b = 3, 6, 7, 990 - b = 3, 0, 3 (mod 4)."""
    check(990 % 4 == 2, "K(11,2) itself")
    check([b for b in range(3, 8) if (990 - b) % 4 in (1, 2)] == [4, 5], "b = 4, 5")
    check([(990 - b) % 4 for b in (3, 6, 7)] == [3, 0, 3], "b = 3, 6, 7")
    # A 4-cycle and a 5-cycle in K(11,2): consecutive pairs are disjoint.
    for cycle in ([(0, 1), (2, 3), (0, 4), (2, 5)],
                  [(0, 1), (2, 3), (4, 5), (1, 6), (3, 7)]):
        length = len(cycle)
        check(len(set(cycle)) == length, "distinct vertices")
        check(all(not set(cycle[i]) & set(cycle[(i + 1) % length]) for i in range(length)),
              f"a {length}-cycle in K(11,2)")


CHECKS = [
    ("Thm. 4.18, App. B", "incidence identities, spectrum, mu = 440", check_incidence_identities),
    ("App. B, eq. (5)", "the moment identities", check_moment_identities),
    ("App. B, eq. (6)", "the fourth-moment bound, constants, quartic, 26409/64",
     check_fourth_moment_bound_and_quartic),
    ("Cor. 4.19", "kappa > 383/1764", check_kappa_383),
    ("Cor. 4.19", "seven deletions; the edit budget; eleven additions",
     check_deletion_and_edit_margins),
    ("Cor. 4.19", "the SDP matrix X_0; mu(H_b) > 436 > beta", check_sdp_comparison),
    ("Sec. 4.7", "which H_b Bosak's condition excludes", check_bosak_remark),
]
