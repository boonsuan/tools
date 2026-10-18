"""Section 5 of the paper: the interval (Tool III).

Claims checked here
-------------------
* Theorem 5.1: the sums behind the two correction terms, the monotonicity
  step for the +2p term, and (as a finite sanity check) that the bound never
  exceeds the known lengths of optimal Golomb rulers.
* Corollary 5.2: the two polynomials and the thresholds r >= 46, r >= 102.
* Lemma 5.3: the balanced-class computation, and the construction in its
  proof, carried out on actual graphs.
* Proposition 5.4: the hypothesis m >= r^2/2, the cut sizes B >= 2m/3, and
  beta_m < 2m/3 for m >= 100.
* Corollary 5.5: the deficit identity, the K_20 example (249t + 9/2, hence
  at most 59t + 4 further edges), and the comparisons per copy of K_r with
  positivity (Corollary 4.4): about 0.64 r^2; positivity stronger for
  6 <= r <= 11 and the interval from r = 12 on (77 against 76.65); 15.33
  against Shearer's 91/6 at r = 6; and, without the boundary-gap term (as in
  Ma and Yi), the interval only from r = 14.
"""
from fractions import Fraction
from itertools import combinations
from math import comb

from exact import ceil_div, check, interval_inside, KAPPA_LOWER, KAPPA_UPPER, PI_LOWER
from polynomial import Poly, all_coefficients_positive, sum_over, variables


# ----------------------------------------------------------------------------
# Theorem 5.1
# ----------------------------------------------------------------------------

def dense_core_bound(r, h, p=0, clique=False):
    """The lower bound for m in Theorem 5.1, with T = hr - h(h+1)/2 - p."""
    T = h * r - h * (h + 1) // 2 - p
    if clique:
        check(p == 0 and r >= 2 * h, "the clique form needs p = 0 and r >= 2h")
        return Fraction(T * (T + 1), h * (h + 1)) + Fraction(h * h - 1, 3)
    return Fraction(T * (T + 1) + 2 * p, h * (h + 1)) + Fraction(2 * (h - 1), 3)


# Lengths of optimal Golomb rulers with r marks, r = 1, ..., 28 (OEIS A003022).
OPTIMAL_GOLOMB_LENGTH = [0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85, 106, 127, 151,
                         177, 199, 216, 246, 283, 333, 356, 372, 425, 480, 492, 553, 585]


def check_theorem_5_1():
    """Theorem 5.1.  The proof shows
        T(T+1)/2 + p  <=  S_h  <=  W m - (h-1)h(h+1)/3,     W = h(h+1)/2,
    and in the clique case replaces (h-1)h(h+1)/3 by h(h-1)(h+1)^2/6; dividing
    by W gives the two bounds.  We check the sums and the monotonicity step."""
    h, j = variables("h j")
    # Upper bound: sum_{j=1}^h (j m - j(j-1)), and sum j = W.
    check(sum_over(j, "j", h) == h * (h + 1) / 2, "sum_{j<=h} j = W")
    check(sum_over(j * (j - 1), "j", h) == (h - 1) * h * (h + 1) / 3,
          "sum_{j<=h} j(j-1) = (h-1)h(h+1)/3; divided by W this is 2(h-1)/3")
    # Lower bound: with P pairs of which p' <= p are non-edges,
    # S_h >= g(p') with g(x) = (P-x)(P-x+1)/2 + x, and g decreases for x <= P-1,
    # so g(p') >= g(p) = T(T+1)/2 + p with T = P - p.
    P, x = variables("P x")

    def g(y):
        return (P - y) * (P - y + 1) / 2 + y
    check(g(x + 1) - g(x) == 1 - (P - x), "g(x+1) - g(x) = 1 - (P - x) <= 0 for x <= P - 1")
    # Clique form: the deficits C(h-i+1, 2), 1 <= i <= h-1, each occur twice;
    # giving the smallest gaps 2j-1 and 2j to the j-th largest deficit gives
    # sum_{j=1}^{h-1} (4j - 1) C(h-j+1, 2) = h(h-1)(h+1)^2/6, and divided by W
    # this is (h^2 - 1)/3.
    summand = (4 * j - 1) * (h - j + 1) * (h - j) / 2
    check(sum_over(summand, "j", h - 1) == h * (h - 1) * (h + 1) ** 2 / 6, "the deficit sum")
    check((h * h - 1) / 3 * (h * (h + 1) / 2) == h * (h - 1) * (h + 1) ** 2 / 6,
          "divided by W it is (h^2 - 1)/3")
    # Finite sanity check: for K_r, r <= 28, no bound exceeds the length of an
    # optimal Golomb ruler (which is ell(K_r)).
    for r in range(2, 29):
        best = max(dense_core_bound(r, h, clique=(r >= 2 * h)) for h in range(1, r))
        check(best <= OPTIMAL_GOLOMB_LENGTH[r - 1], f"the bound for K_{r} exceeds a known ruler")


# ----------------------------------------------------------------------------
# Corollary 5.2
# ----------------------------------------------------------------------------

def check_corollary_5_2():
    """Corollary 5.2 (a) K_r plus floor(r^2/4) leaves, r >= 46, and (b) K_r
    minus a perfect matching plus r^2/4 leaves, r >= 102 even."""
    r, u = variables("r u")
    # (a) m = C(r,2) + floor(r^2/4) <= 3r^2/4 - r/2.  With h = 6 (clique form,
    # valid as r >= 12): T = 6r - 21, and the bound is T(T+1)/42 + 35/3.
    T = 6 * r - 21                               # hr - h(h+1)/2 with h = 6
    gap_a = T * (T + 1) / 42 + Fraction(35, 3) - (Fraction(3, 4) * r * r - r / 2)
    check(gap_a == (9 * r * r - 450 * r + 1820) / 84, "polynomial (a)")
    # (b) p = r/2 and m = C(r,2) - r/2 + r^2/4 = 3r^2/4 - r.  With h = 13:
    # T = 13r - 91 - r/2 = (25r - 182)/2, and the first bound minus its other,
    # nonnegative terms (2p/182 and 2(h-1)/3) is T(T+1)/182.
    T = (25 * r - 182) / 2
    check(T == 13 * r - 13 * 14 // 2 - r / 2, "(b) T = hr - h(h+1)/2 - p")
    check(r * (r - 1) / 2 - r / 2 + r * r / 4 == Fraction(3, 4) * r * r - r, "(b) m")
    gap_b = T * (T + 1) / 182 - (Fraction(3, 4) * r * r - r)
    check(gap_b == (79 * r * r - 8322 * r + 32760) / 728, "polynomial (b)")
    # Positive for all r >= 46 (resp. 102): after substituting r = 46 + u
    # (resp. 102 + u) every coefficient is positive.  (T > 0 there too.)
    check(all_coefficients_positive((9 * r * r - 450 * r + 1820).substitute("r", 46 + u)),
          "(a) holds for r >= 46")
    check(all_coefficients_positive((79 * r * r - 8322 * r + 32760).substitute("r", 102 + u)),
          "(b) holds for r >= 102")
    # (Extra: the polynomials are negative just below, so with these h the
    # thresholds are exactly 46 and 102.)
    check(9 * 45 ** 2 - 450 * 45 + 1820 < 0, "(a) fails at r = 45")
    check(79 * 101 ** 2 - 8322 * 101 + 32760 < 0, "(b) fails at r = 101")


# ----------------------------------------------------------------------------
# Lemma 5.3 and Proposition 5.4
# ----------------------------------------------------------------------------

def check_balanced_class_inequality():
    """In the proof of Lemma 5.3: if {0,...,r-1} is split into its q residue
    classes, of sizes r_a in {k, k+1} (r = kq + s, 0 <= s < q), then
    r^2/(4q) - sum_a floor(r_a^2/4) is s^2/(4q) (k even) or (q-s)^2/(4q)
    (k odd).  In particular sum_a floor(r_a^2/4) <= floor(r^2/(4q))."""
    q, s, half = variables("q s half")
    # k = 2 half: s classes of size 2 half + 1 (floor(size^2/4) = half^2 + half)
    # and q - s classes of size 2 half (half^2).
    r = 2 * half * q + s
    floor_sum = s * (half * half + half) + (q - s) * half * half
    check(r * r - 4 * q * floor_sum == s * s, "k even")
    # k = 2 half + 1: s classes of size 2 half + 2 ((half + 1)^2) and q - s of
    # size 2 half + 1 (half^2 + half).
    r = (2 * half + 1) * q + s
    floor_sum = s * (half + 1) ** 2 + (q - s) * (half * half + half)
    check(r * r - 4 * q * floor_sum == (q - s) ** 2, "k odd")
    # Finite sanity check of the conclusion, with actual residue classes.
    for r in range(1, 120):
        for q in range(1, 130):
            sizes = [len(range(a, r, q)) for a in range(q)]
            check(sum(x * x // 4 for x in sizes) <= r * r // (4 * q), "balanced classes")


def two_adic_valuation(x):
    """The exponent of 2 in the nonzero integer x."""
    check(x != 0, "the 2-adic valuation of 0 is undefined")
    x, v = abs(x), 0
    while x % 2 == 0:
        x //= 2
        v += 1
    return v


def required_count(m, j):
    """o_j = ceil(m_j/2) with m_j = floor(m/2^j): the number of edges whose
    difference has 2-adic valuation exactly j, in any graceful labeling."""
    return ceil_div(m >> j, 2)


def leaf_differences_for_lemma_5_3(core_edges, leaves):
    """The construction in the proof of Lemma 5.3.  The core H has vertices
    0, ..., r-1, with auxiliary label = vertex number (vertex 0 carries the
    leaves).  For each level j, give o_j - c_j leaves the label 2^j, whose
    difference with the label 0 has valuation exactly j.  Returns the list of
    differences of the leaf edges, or None if some o_j < c_j or the leaves do
    not come out exactly."""
    m = len(core_edges) + leaves
    core_differences = [b - a for a, b in core_edges]
    leaf_differences = []
    for j in range(m.bit_length()):
        c_j = sum(1 for d in core_differences if two_adic_valuation(d) == j)
        o_j = required_count(m, j)
        if o_j < c_j:
            return None
        leaf_differences += [2 ** j] * (o_j - c_j)
    return leaf_differences if len(leaf_differences) == leaves else None


def passes_iterated_parity_with(differences, m):
    """The iterated parity test (Section 3.2) for a given map: for every j,
    exactly ceil(m_j/2) edges have difference of 2-adic valuation j."""
    return all(sum(1 for d in differences if two_adic_valuation(d) == j) == required_count(m, j)
               for j in range(m.bit_length()))


def check_lemma_5_3_construction():
    """Lemma 5.3, on actual graphs: for H = K_r, and for H = K_r minus a
    perfect matching with r even (the cores of Corollary 5.2), r < 26, and every m with
    r^2/2 <= m < r^2, the construction succeeds and the resulting map passes
    the iterated parity test.  (A finite check of the proof's construction.)"""
    for r in range(2, 26):
        cores = {
            "K_r": list(combinations(range(r), 2)),
        }
        if r % 2 == 0:
            cores["K_r minus a perfect matching"] = [
                (a, b) for a, b in combinations(range(r), 2) if not (a % 2 == 0 and b == a + 1)]
        for name, core in cores.items():
            for m in range(ceil_div(r * r, 2), r * r):
                leaves = m - len(core)
                if leaves < 0:
                    continue
                leaf_differences = leaf_differences_for_lemma_5_3(core, leaves)
                check(leaf_differences is not None, f"construction for {name}, r = {r}, m = {m}")
                all_differences = [b - a for a, b in core] + leaf_differences
                check(passes_iterated_parity_with(all_differences, m),
                      f"iterated parity for {name}, r = {r}, m = {m}")


def check_proposition_5_4():
    """Proposition 5.4: both families of Corollary 5.2 have m >= r^2/2 (so
    Lemma 5.3 applies) and m >= 100; the cut has B >= 2m/3 edges; and
    beta_m <= 1 + csc(pi/(2m+1)) <= 1 + (2m+1)/pi + pi/(2m+1) < 2m/3."""
    k, x = variables("k x")
    # m >= r^2/2.  (a) m = C(r,2) + floor(r^2/4), and m - r^2/2 is k(k-1) for
    # r = 2k and k^2 - 1/2 for r = 2k+1, both >= 0 for k >= 1.
    r = 2 * k
    check(r * (r - 1) / 2 + k * k - r * r / 2 == k * k - k, "(a), r even: m - r^2/2 = k(k-1)")
    r = 2 * k + 1
    check(r * (r - 1) / 2 + (k * k + k) - r * r / 2 == k * k - Fraction(1, 2),
          "(a), r odd: m - r^2/2 = k^2 - 1/2 > 0")
    # (b) m = 3r^2/4 - r, and m - r^2/2 = r(r - 4)/4 >= 0 for r >= 4.
    r = Poly.var("r")
    check(Fraction(3, 4) * r * r - r - r * r / 2 == r * (r - 4) / 4, "(b) m - r^2/2")
    check(comb(46, 2) + 46 * 46 // 4 >= 100 and 3 * 102 * 102 // 4 - 102 >= 100,
          "m >= 100 in both families (and m grows with r)")

    # The cut, with the leaves opposite their vertex: its +-1 vector has energy
    # 4B - 2m, so gamma_2 >= 4B - 2m >= 2m/3 once B >= 2m/3.
    # (a) B = 2 floor(r^2/4) and 3B - 2m = 4 floor(r^2/4) - r(r-1), which is
    # 2k for r = 2k (floor = k^2) and for r = 2k + 1 (floor = k^2 + k):
    check(4 * k * k - (2 * k) * (2 * k - 1) == 2 * k
          and 4 * (k * k + k) - (2 * k + 1) * (2 * k) == 2 * k, "(a) 3B - 2m >= 0")
    # (b) B >= r^2/2 - r/2 and m = 3r^2/4 - r: 3B - 2m >= r/2 >= 0.
    check(3 * (r * r / 2 - r / 2) - 2 * (Fraction(3, 4) * r * r - r) == r / 2, "(b) 3B - 2m")

    # csc x <= 1/x + x for 0 < x^2 <= 5 (here x = pi/(2m+1) < 1): since
    # sin x >= x - x^3/6 and (1 - x^2/6)(1 + x^2) - 1 = x^2(5 - x^2)/6 >= 0
    # for x^2 <= 5, we get sin x >= x/(1 + x^2).
    check((1 - x * x / 6) * (1 + x * x) - 1 == x * x * (5 - x * x) / 6, "csc x <= 1/x + x")
    # 1 + (2m+1)/pi + pi/(2m+1) < 2m/3 at m = 100 (with pi/(2m+1) < 4/(2m+1)),
    # and the left side grows by at most 2/pi < 2/3 per unit increase of m,
    # while the right side grows by 2/3.
    m = 100
    check(1 + Fraction(2 * m + 1) / PI_LOWER + Fraction(4, 2 * m + 1) < Fraction(2 * m, 3),
          "m = 100")
    check(2 / PI_LOWER < Fraction(2, 3), "the slope 2/pi < 2/3")


# ----------------------------------------------------------------------------
# Corollary 5.5
# ----------------------------------------------------------------------------
#
# Per copy of K_r, for large t:
#   the interval (Corollary 5.5) gives m >= t T^2/(h(h+1)) + ..., plus
#     t h(h-1)/3 from the boundary-gap term when r >= 2h;
#   positivity (Corollary 4.4 with t cliques of size r and e0 = m - t C(r,2)
#     other edges) excludes m <= (t r(r-2) + 1 + kappa)/(2 - 2 kappa).

def per_copy_interval(r, h, gap):
    """The coefficient of t in Corollary 5.5, with T = hr - h(h+1)/2."""
    T = h * r - h * (h + 1) // 2
    value = Fraction(T * T, h * (h + 1))
    return value + Fraction(h * (h - 1), 3) if gap else value


def best_per_copy_interval(r, gap_term_allowed):
    """The best coefficient over 1 <= h <= r - 1, using the boundary-gap form
    whenever it is allowed (r >= 2h) and the first form otherwise."""
    return max(per_copy_interval(r, h, gap=gap_term_allowed and r >= 2 * h)
               for h in range(1, r))


def per_copy_positivity(r, kappa):
    """The coefficient of t in the positivity bound: r(r-2)/(2 - 2 kappa)."""
    return Fraction(r * (r - 2)) / (2 - 2 * kappa)


def check_corollary_5_5():
    """Corollary 5.5 and the discussion after it."""
    h, t, j, m, r, kappa = variables("h t j m r kappa")
    # The total deficit in the proof:
    summand = t * (4 * t * j - 2 * t + 1) * (h - j + 1) * (h - j) / 2
    check(sum_over(summand, "j", h - 1) == t * h * (h - 1) * (h + 1) * (t * h + 1) / 6,
          "the deficit identity")
    # K_20 with h = 4: T = 80 - 10 = 70, and the bound is
    # 70(70t + 1)/20 + 3(4t + 1)/3 = 249t + 9/2.  Each K_20 has 190 edges, and
    # 190t + 59t + 4 < 249t + 9/2.
    check(4 * 20 - 4 * 5 // 2 == 70 and 20 >= 2 * 4, "K_20: T = 70, r >= 2h")
    bound = 70 * (70 * t + 1) / 20 + (4 - 1) * (4 * t + 1) / 3
    check(bound == 249 * t + Fraction(9, 2), "K_20: 249t + 9/2")
    check(bound - (190 * t + 59 * t + 4) == Fraction(1, 2), "at most 59t + 4 further edges")

    # Positivity per copy: the criterion tr + 2(m - t C(r,2)) <= 1 + kappa(2m+1)
    # is m(2 - 2 kappa) <= t r(r-2) + 1 + kappa.
    slack = 1 + kappa * (2 * m + 1) - (t * r + 2 * (m - t * r * (r - 1) / 2))
    check(slack == t * r * (r - 2) + 1 + kappa - m * (2 - 2 * kappa), "the positivity bound")
    check(interval_inside(1 / (2 - 2 * KAPPA_LOWER), 1 / (2 - 2 * KAPPA_UPPER), "0.635", "0.645"),
          "1/(2 - 2 kappa) ~ 0.64")

    # With h = 3 the interval gives (3/4)(r - 2)^2 + 2 per copy, 77 at r = 12,
    # against 76.65 from positivity; it wins for every r >= 12.
    check((3 * r - 6) ** 2 / 12 + 2 == Fraction(3, 4) * (r - 2) ** 2 + 2, "h = 3")
    check(per_copy_interval(12, 3, gap=True) == 77, "77 at r = 12")
    check(interval_inside(per_copy_positivity(12, KAPPA_LOWER),
                          per_copy_positivity(12, KAPPA_UPPER), "76.645", "76.655"),
          "76.65 at r = 12")
    u = Poly.var("u")
    difference = (2 - 2 * KAPPA_UPPER) * (Fraction(3, 4) * (r - 2) ** 2 + 2) - r * (r - 2)
    check(all_coefficients_positive(difference.substitute("r", 12 + u)),
          "with h = 3 the interval wins for every r >= 12")
    # ...and positivity is stronger for 6 <= r <= 11, against every h:
    for r_value in range(6, 12):
        check(best_per_copy_interval(r_value, gap_term_allowed=True)
              < per_copy_positivity(r_value, KAPPA_LOWER), f"positivity wins at r = {r_value}")

    # Shearer, r = 6: positivity gives 24/(2 - 2 kappa) = 15.33 per copy,
    # above the 91/6 = 15.1666... of (91t + 6)/6.
    check(interval_inside(per_copy_positivity(6, KAPPA_LOWER),
                          per_copy_positivity(6, KAPPA_UPPER), "15.325", "15.335")
          and Fraction(91, 6) < per_copy_positivity(6, KAPPA_LOWER), "Shearer")

    # Without the boundary-gap term (Ma and Yi): positivity wins for
    # 6 <= r <= 13 against every h, and with h = 3 the interval gives
    # (3/4)(r - 2)^2, which wins for every r >= 14.
    for r_value in range(6, 14):
        check(best_per_copy_interval(r_value, gap_term_allowed=False)
              < per_copy_positivity(r_value, KAPPA_LOWER), f"Ma-Yi, r = {r_value}")
    difference = (2 - 2 * KAPPA_UPPER) * Fraction(3, 4) * (r - 2) ** 2 - r * (r - 2)
    check(all_coefficients_positive(difference.substitute("r", 14 + u)),
          "without the gap term the interval wins for every r >= 14")


CHECKS = [
    ("Thm. 5.1", "the sums in the proof; optimal Golomb rulers", check_theorem_5_1),
    ("Cor. 5.2", "the polynomials and the thresholds r >= 46, r >= 102", check_corollary_5_2),
    ("Lemma 5.3", "balanced residue classes", check_balanced_class_inequality),
    ("Lemma 5.3", "the construction in the proof, on actual graphs", check_lemma_5_3_construction),
    ("Prop. 5.4", "m >= r^2/2, cut sizes, beta_m < 2m/3", check_proposition_5_4),
    ("Cor. 5.5", "K_20; comparisons with positivity; Shearer; Ma-Yi", check_corollary_5_5),
]
