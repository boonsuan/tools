"""Sections 4.1-4.6 of the paper: positivity on the unit circle (Tool II).

Almost every claim in these sections says that the criterion of Theorem 4.1,

        trace of a certificate  <=  1 + kappa (2m + 1),

holds (so the graph is not graceful) or fails, for some parameters.  The
right side grows with kappa, so we confirm that it HOLDS using KAPPA_LOWER
and that it FAILS using KAPPA_UPPER (see criterion_holds, criterion_fails).

A claim "for all n >= n0" is checked the way the paper proves it: the
algebraic step is checked as a polynomial identity (polynomial.py), and the
inequality at the base case is checked exactly.  Loops over finitely many
parameters appear only as extra sanity checks, and say so.

Claims checked here
-------------------
* The decimal constants of Section 4 and Table 1: 0.2172, 0.4108, 0.1785,
  4.60, 5.603, 5.61, 9.21, 0.6086.
* Corollary 4.4 (a)-(d): the thresholds 5, 6, 6, 13.
* Corollary 4.5: the two forms of the density bound, and r >= 6 equal parts.
* Theorem 4.6: the threshold 6, and the mixed systems (6,4) and (6,5,5).
* Section 4.4: two or three K_4's (iterated parity), and the K_4-snakes.
* Corollary 4.8(c): the parity companion.
* Corollary 4.9: every step of the proof for B(n,r,t), the thresholds
  6, 8, 10, 12, 14, and n >= 2.4 r + 6.
* Proposition 4.10: the maximization in the proof, and the formula.
* Corollary 4.11: line graphs and rook's graphs, the clique sizes in (b)-(e),
  and the large cliques in q-Kneser graphs used in (g).
* Corollary 4.12 and the remarks after it: Paley graphs.
* Corollaries 4.13 and 4.14: d >= 84, average degree 9.21, and the polarity
  graphs ER_q.
* Section 4.3 and Section 7: mu(K_{3,3,3}) = 27, mu(K_{2,2,2,2,2}) = 20 and
  mu(K_{1,1,1,1,N}) = 8N - 12 from Proposition 4.15(c), and the comparisons
  with beta_m (beta_40 is about 18.6; 8N - 12 > beta_(4N+6)).
"""
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb
import cmath
import math

from exact import (check, interval_inside, KAPPA_LOWER, KAPPA_UPPER,
                   sqrt_lower, sqrt_upper)
from polynomial import Poly, all_coefficients_positive, variables
from graphs import (cartesian_product_with_path_or_cycle, clique_edges,
                    is_graceful_labeling, kneser_graph)
from sec3_parity import bosak_excludes
from appendix_a_dirichlet import beta_lower, beta_upper


def criterion_holds(trace, m):
    """Theorem 4.1 with a certificate of the given trace certainly excludes a
    graph with m edges: trace <= 1 + kappa (2m+1), checked with KAPPA_LOWER."""
    return trace <= 1 + KAPPA_LOWER * (2 * m + 1)


def criterion_fails(trace, m):
    """The same criterion certainly fails: trace > 1 + kappa (2m+1), checked
    with KAPPA_UPPER."""
    return trace > 1 + KAPPA_UPPER * (2 * m + 1)


# ----------------------------------------------------------------------------
# Decimal constants
# ----------------------------------------------------------------------------

def check_decimal_constants():
    """The decimals printed in Section 4 and Table 1.  For an approximation
    'x ~ 0.4108' we check that x rounds to the printed digits; where the
    table uses a printed decimal as a sufficient condition (m >= 0.4108 n^2,
    n >= 5.61 k, average degree >= 9.21) we also check that it is on the
    safe side."""
    KL, KU = KAPPA_LOWER, KAPPA_UPPER        # kappa lies between these
    check(interval_inside(KL, KU, "0.21715", "0.21725"), "kappa ~ 0.2172")

    # Corollary 4.5: (n^2 - 1 - kappa)/(2 + 2 kappa) ~ 0.4108 n^2.  The table
    # row "m >= 0.4108 n^2" needs 0.4108 >= 1/(2 + 2 kappa).
    check(interval_inside(1 / (2 + 2 * KU), 1 / (2 + 2 * KL), "0.41075", "0.41085"),
          "1/(2 + 2 kappa) ~ 0.4108")
    check(1 / (2 + 2 * KL) <= Fraction("0.4108"), "0.4108 is on the safe side")
    # Corollary 4.5: kappa/(1 + kappa) ~ 0.1785.
    check(interval_inside(KL / (1 + KL), KU / (1 + KU), "0.17845", "0.17855"),
          "kappa/(1 + kappa) ~ 0.1785")
    # Corollary 4.4(b), Theorem 4.6: 1/kappa ~ 4.60.
    check(interval_inside(1 / KU, 1 / KL, "4.595", "4.605"), "1/kappa ~ 4.60")
    # Corollaries 4.9 and 4.11(f): 1 + 1/kappa ~ 5.603; Table 1 uses 5.61.
    check(interval_inside(1 + 1 / KU, 1 + 1 / KL, "5.6025", "5.6035"),
          "1 + 1/kappa ~ 5.603")
    check(1 + 1 / KL <= Fraction("5.61"), "5.61 is on the safe side")
    # Corollary 4.14(a): 2/kappa ~ 9.21, and 9.21 is on the safe side.
    check(interval_inside(2 / KU, 2 / KL, "9.205", "9.215"), "2/kappa ~ 9.21")
    check(2 / KL <= Fraction("9.21"), "9.21 is on the safe side")
    # Section 4.6: (1 + kappa)/2 ~ 0.6086.
    check(interval_inside((1 + KL) / 2, (1 + KU) / 2, "0.60855", "0.60865"),
          "(1 + kappa)/2 ~ 0.6086")
    # ...and since beta_m > 1 + kappa(2m+1), (2m + beta_m)/4 exceeds
    # (2m + 1 + kappa(2m+1))/4 = (1 + kappa) m/2 + (1 + kappa)/4.
    kappa, m = variables("kappa m")
    check((2 * m + 1 + kappa * (2 * m + 1)) / 4 - (1 + kappa) * m / 2 == (1 + kappa) / 4,
          "(2m + beta_m)/4 > (1 + kappa) m/2")


# ----------------------------------------------------------------------------
# Corollaries 4.4 and 4.5
# ----------------------------------------------------------------------------

def check_corollary_4_4():
    """Corollary 4.4: the certificate sum of J_Q over the cliques, with
    trace sigma + 2 e0, excludes (a) K_n for n >= 5, (b) windmills K_n^(t)
    and unions tK_n for n >= 6, (c) barbells B_n for n >= 6, and
    (d) K_n box P_r and K_n box C_r for n >= 13."""
    kappa = Poly.var("kappa")
    n, r = variables("n r")

    # (a) sigma = n, m = C(n,2).  Let slack(n) = 1 + kappa(n^2 - n + 1) - n.
    # It is >= 0 at n = 5, and slack(n+1) - slack(n) = 2 kappa n - 1, which is
    # positive from n = 5 on (since 10 kappa > 1).
    slack = 1 + kappa * (n * n - n + 1) - n
    check(slack.substitute("n", n + 1) - slack == 2 * kappa * n - 1, "(a) increment")
    check(criterion_holds(5, comb(5, 2)) and 10 * KAPPA_LOWER > 1, "(a) K_n, n >= 5")

    # (b) sigma = tn, e0 = 0, 2m = tn(n-1): tn <= kappa tn(n-1) iff
    # n - 1 >= 1/kappa, and kappa tn(n-1) = 2 kappa m < 1 + kappa(2m+1).
    check(5 * KAPPA_LOWER >= 1, "(b) n - 1 = 5 >= 1/kappa")

    # (c) sigma = 2n, e0 = 1, m = n(n-1) + 1.  slack(n) = 1 + kappa(2n^2 - 2n + 3)
    # - (2n + 2) has slack(n+1) - slack(n) = 4 kappa n - 2 > 0 for n >= 6.
    slack = 1 + kappa * (2 * n * n - 2 * n + 3) - (2 * n + 2)
    check(slack.substitute("n", n + 1) - slack == 4 * kappa * n - 2, "(c) increment")
    check(criterion_holds(2 * 6 + 2, 6 * 5 + 1) and 24 * KAPPA_LOWER > 2, "(c) B_n, n >= 6")

    # (d) The counts sigma + 2 e0 and 2m, confirmed on actual graphs:
    for size in range(2, 7):
        for length in range(3, 7):
            for cycle in (True, False):
                _, edges = cartesian_product_with_path_or_cycle(size, length, cycle)
                m = len(edges)
                sigma = length * size                    # the r column cliques
                e0 = m - length * comb(size, 2)          # the matching edges
                if cycle:
                    expected = (3 * length * size, length * size * (size + 1))
                else:
                    expected = (size * (3 * length - 2),
                                length * size * (size + 1) - 2 * size)
                check((sigma + 2 * e0, 2 * m) == expected, "(d) counts")
    # Cycle: sigma + 2 e0 = 3rn <= kappa rn(n+1) = 2 kappa m once kappa(n+1) >= 3.
    # Path: the slack is a sum of nonnegative terms once kappa(n+1) >= 3 (and
    # kappa < 1):
    slack = 1 + kappa * (r * n * (n + 1) - 2 * n + 1) - n * (3 * r - 2)
    check(slack == (kappa * (n + 1) - 3) * r * n + 2 * n * (1 - kappa) + 1 + kappa,
          "(d) path slack")
    check(14 * KAPPA_LOWER >= 3 and 13 * KAPPA_UPPER < 3,
          "(d) kappa(n+1) >= 3 exactly from n = 13")


def check_corollary_4_5():
    """Corollary 4.5: with trace n^2 - 2m, the criterion is equivalent to
    m >= (n^2 - 1 - kappa)/(2 + 2 kappa), and for K_{a_1..a_r} (2m = n^2 -
    sum a_i^2) to sum a_i^2 <= kappa/(1+kappa) n^2 + 1.  With r >= 6 equal
    parts, sum a_i^2 = n^2/r <= n^2/6, and 1/6 < kappa/(1+kappa)."""
    kappa, n, m, S = variables("kappa n m S")       # S stands for sum a_i^2
    # 1 + kappa(2m+1) - (n^2 - 2m) = (2 + 2 kappa) m - (n^2 - 1 - kappa):
    check(1 + kappa * (2 * m + 1) - (n * n - 2 * m)
          == (2 + 2 * kappa) * m - (n * n - 1 - kappa), "first form")
    # With 2m = n^2 - S, the same slack is (1 + kappa)(1 + kappa n^2/(1+kappa) - S):
    slack = (1 + kappa * (n * n - S + 1) - S)
    check(slack == (1 + kappa) - (1 + kappa) * S + kappa * n * n, "second form")
    check(Fraction(1, 6) < KAPPA_LOWER / (1 + KAPPA_LOWER), "1/6 < kappa/(1+kappa)")


# ----------------------------------------------------------------------------
# Theorem 4.6 and Section 4.4
# ----------------------------------------------------------------------------

def check_theorem_4_6():
    """Theorem 4.6: cliques with at least 6 vertices satisfy the displayed
    inequality, since |Q| - 1 >= 5 > 1/kappa; and 6 is the threshold, since
    5 - 1 < 1/kappa.  Systems of sizes (6,4) and (6,5,5) are excluded by the
    first inequality (trace = sum |Q| <= 1 + kappa(2m+1))."""
    check(5 > 1 / KAPPA_LOWER and 4 < 1 / KAPPA_UPPER, "the threshold 6")
    for sizes in ((6, 4), (6, 5, 5)):
        trace, m = sum(sizes), sum(comb(s, 2) for s in sizes)
        check(criterion_holds(trace, m), f"first inequality for {sizes}")
        # (Not claimed in the paper, but the reason the first inequality is
        # needed: the displayed second inequality fails for these sizes.
        # Its left side increases with kappa, so KAPPA_UPPER gives an upper bound.)
        check(sum(s * (s - 1 - 1 / KAPPA_UPPER) for s in sizes) < 0,
              f"the second inequality fails for {sizes}")


def check_two_or_three_K4():
    """Section 4.4 (after Theorem 4.6), following Bermond, Kotzig and Turgeon:
    if the edges split into two or three K_4's, then m = 12 or 18 and the
    odd-difference cut needs 6 or 9 edges.  Each K_4 contributes a(4-a), that
    is 0, 3 or 4, so every K_4 must contribute 3, i.e. be cut as K_{1,3},
    which leaves a triangle.  Then G_1 consists of triangles, so all its
    degrees are even, while m_1 = 6 or 9 = 2 or 1 (mod 4): Proposition 3.5."""
    contributions = sorted({a * (4 - a) for a in range(5)})
    check(contributions == [0, 3, 4], "cut contributions of K_4")
    for copies, m in ((2, 12), (3, 18)):
        need = (m + 1) // 2
        ways = [c for c in product(contributions, repeat=copies) if sum(c) == need]
        check(ways == [(3,) * copies], f"{copies} copies: every K_4 contributes 3")
        # A K_4 cut as K_{1,3} keeps a triangle, so G_1 has 3 * copies edges.
        check(3 * copies == m // 2 and bosak_excludes(m // 2),
              f"{copies} copies: level j = 1")


def snake_order(blocks):
    """An ordering of the blocks in which consecutive blocks share exactly one
    label and non-consecutive blocks share none (a snake), or None.  Brute
    force over all orderings; there are at most 6 blocks."""
    for order in permutations(blocks):
        def shared(i, j):
            return len(order[i] & order[j])
        if all(shared(i, j) == (1 if j == i + 1 else 0)
               for i, j in combinations(range(len(order)), 2)):
            return list(order)
    return None


def check_K4_snakes():
    """Section 4.4: labelings of K_4-snakes.  A snake of t K_4's has 3t + 1
    vertices and m = 6t edges.  Each block is the label set of one K_4, and
    a label shared by two blocks is their common vertex; so the labels serve
    as the vertices and the labeling is automatically injective.

    t = 4: the labeling printed in the paper (the snake is credited to
    Dore-Hall).  t = 6: the labeling printed in the paper, found by the
    author.  t = 5: an extra labeling found in this collaboration, not
    printed in the paper, confirming Dore-Hall's report for t = 5."""
    labelings = {
        4: [{2, 12, 17, 20}, {0, 11, 20, 24}, {0, 6, 22, 23}, {1, 3, 15, 22}],
        5: [{0, 7, 12, 30}, {0, 1, 21, 29}, {1, 14, 18, 28}, {2, 4, 13, 28},
            {2, 8, 24, 27}],
        6: [{0, 14, 18, 34}, {0, 1, 13, 36}, {1, 7, 22, 33}, {2, 9, 31, 33},
            {2, 5, 30, 35}, {3, 11, 20, 30}],
    }
    for t, blocks in labelings.items():
        check(snake_order(blocks) is not None, f"t = {t}: the blocks should form a snake")
        vertices = sorted(set().union(*blocks))
        edges = [e for block in blocks for e in clique_edges(sorted(block))]
        check(len(vertices) == 3 * t + 1 and len(set(edges)) == 6 * t, f"t = {t}: graph")
        labels = {v: v for v in vertices}
        check(is_graceful_labeling(vertices, edges, labels), f"t = {t}: graceful")
    check(labelings[6] == snake_order(labelings[6]), "t = 6 is listed in snake order")


def check_corollary_4_8c():
    """Corollary 4.8(c): with T copies of K_5, degrees are 4 r_v and m = 10T,
    which is 2 (mod 4) for T odd; with T triangles, degrees are 2 r_v and
    m = 3T, which is 1 or 2 (mod 4) exactly when T = 3 or 2 (mod 4).  Both
    depend only on T mod 4."""
    for T in range(4):
        if T % 2 == 1:
            check(bosak_excludes(10 * T), "odd number of K_5's")
        check(bosak_excludes(3 * T) == (T in (2, 3)), "triangles")


# ----------------------------------------------------------------------------
# Corollary 4.9 and Proposition 4.10: B(n, r, t)
# ----------------------------------------------------------------------------

def graph_B(n, r, t):
    """B(n,r,t): t copies of K_n sharing a common K_r.  The common vertices
    are ("core", i); the other vertices of copy j are (j, i)."""
    core = [("core", i) for i in range(r)]
    vertices, edges = list(core), clique_edges(core)
    for copy in range(t):
        petal = [(copy, i) for i in range(n - r)]
        vertices += petal
        edges += clique_edges(petal) + [(u, v) for u in core for v in petal]
    return vertices, edges


def check_corollary_4_9():
    """Corollary 4.9: with C = 1 + 1/kappa, B(n,r,t) is not graceful when
    n(n - C) >= C r(r-1); in particular for n >= 2.4 r + 6, and for
    n >= 6, 8, 10, 12, 14 when r = 1, ..., 5."""
    kappa, n, r, t = variables("kappa n r t")

    # The certificate M = sum_j J_{Q_j} - (t-1) J_R + (t-1) r I_R.  In general,
    #     x^T M x = sum_j (sigma_R + sigma_j)^2 + (t-1)(r sum_R x_v^2 - sigma_R^2),
    # and by Lagrange's identity r sum_R x_v^2 - sigma_R^2 = sum_{u<v in R}
    # (x_u - x_v)^2, so M is positive semidefinite.  As a sanity check we
    # confirm, on small cases with x a vector of variables, that M agrees with
    # the adjacency matrix off the diagonal and that x^T M x equals this sum
    # of squares; and the trace and edge count.
    for size, core_size, copies in [(4, 2, 3), (5, 3, 2), (6, 2, 2), (5, 1, 3)]:
        vertices, edges = graph_B(size, core_size, copies)
        core = [v for v in vertices if v[0] == "core"]
        petals = [[v for v in vertices if v[0] == j] for j in range(copies)]
        x = {v: Poly.var(str(v)) for v in vertices}

        def M(u, v):
            entry = sum(1 for j in range(copies) if u in core + petals[j] and v in core + petals[j])
            if u in core and v in core:
                entry += -(copies - 1) + ((copies - 1) * core_size if u == v else 0)
            return entry
        edge_set = {frozenset(e) for e in edges}
        check(all(M(u, v) == (frozenset((u, v)) in edge_set)
                  for u, v in combinations(vertices, 2)), "M agrees with A off the diagonal")
        quadratic_form = sum((M(u, v) * x[u] * x[v] for u in vertices for v in vertices), Poly(0))
        sigma_R = sum((x[v] for v in core), Poly(0))
        squares = sum(((sigma_R + sum((x[v] for v in petal), Poly(0))) ** 2 for petal in petals),
                      Poly(0))
        squares = squares + (copies - 1) * sum(((x[u] - x[v]) ** 2
                                                for u, v in combinations(core, 2)), Poly(0))
        check(quadratic_form == squares, "x^T M x as a sum of squares")
        trace = sum(M(v, v) for v in vertices)
        check(trace == copies * size + (copies - 1) * core_size * (core_size - 1), "tr M")
        check(2 * len(edges) + 1 == 1 + core_size * (core_size - 1)
              + copies * (size * (size - 1) - core_size * (core_size - 1)), "2m + 1")

    # The hypothesis, multiplied by kappa (using kappa C = kappa + 1), is
    # kappa(n(n-1) - r(r-1)) - (n + r(r-1)) >= 0:
    X = n * (n - 1) - r * (r - 1)
    check(kappa * n * n - (kappa + 1) * n - (kappa + 1) * r * (r - 1)
          == kappa * X - (n + r * (r - 1)), "the equivalent form of the hypothesis")
    # ...and then 1 + kappa(2m+1) - tr M = t(kappa X - (n + r(r-1))) + 1 + kappa
    # + (1 + kappa) r(r-1) > 0:
    two_m_plus_1 = 1 + r * (r - 1) + t * X
    trace = t * n + (t - 1) * r * (r - 1)
    check(1 + kappa * two_m_plus_1 - trace
          == t * (kappa * X - (n + r * (r - 1))) + 1 + kappa + (1 + kappa) * r * (r - 1),
          "the slack of the criterion")

    # The thresholds.  C lies between C_low and C_high.
    C_low, C_high = 1 + 1 / KAPPA_UPPER, 1 + 1 / KAPPA_LOWER

    def certainly_holds(n, r):
        return n * (n - C_high) >= C_high * r * (r - 1)

    def certainly_fails(n, r):
        return n * (n - C_low) < C_low * r * (r - 1)
    for r_value, threshold in zip(range(1, 6), (6, 8, 10, 12, 14)):
        check(certainly_holds(threshold, r_value) and certainly_fails(threshold - 1, r_value),
              f"r = {r_value}: the smallest n is {threshold}")
    # n(n - C) increases for n >= C/2, so all larger n work too.
    check(C_high / 2 < 6, "n(n - C) is increasing from n = 6")
    # Linear bound: sqrt(C) < 2.4 and C < 6, so n >= 2.4 r + 6 gives
    # n >= sqrt(C) r + C, hence n(n - C) >= (n - C)^2 >= C r^2 >= C r(r-1).
    check(C_high < Fraction(576, 100), "sqrt(C) < 2.4")
    check(C_high < 6, "C < 6")


def common_core_formula(n, r, t):
    """The value in Proposition 4.10, with c = n - r and v = r + tc."""
    c = n - r
    v = r + t * c
    if r <= c:
        return v + (t - 1) * r * r
    if r <= t * c:
        return v - r * r + 2 * t * c * r - t * c * c
    return v + t * (t - 1) * c * c


def unit_numbers_with_sum(k, length):
    """k complex numbers of modulus 1 whose sum is the real number `length`,
    where 0 <= length <= k (and length = 1 if k = 1); floating point.

    For k even, put half at angle +theta and half at -theta, so the sum is
    k cos(theta).  For k odd, put one at angle 0 and the rest at +-theta, so
    the sum is 1 + (k-1) cos(theta)."""
    if k == 1:
        return [complex(1, 0)]
    if k % 2 == 0:
        theta = math.acos(length / k)
        return [cmath.exp(1j * theta * (-1) ** i) for i in range(k)]
    theta = math.acos((length - 1) / (k - 1))
    return [complex(1, 0)] + [cmath.exp(1j * theta * (-1) ** i) for i in range(k - 1)]


def check_proposition_4_10():
    """Proposition 4.10.  The proof bounds the energy by
        g(s) = v + (t-1)s^2 - t (s - c)_+^2,      0 <= s <= r,
    and says the maximum is at s = min(r, tc).  For s <= c, g(s) = v + (t-1)s^2
    is increasing.  For s >= c, g(s) = v + t(t-1)c^2 - (s - tc)^2, which
    increases up to s = tc and decreases after it; the two formulas agree at
    s = c.  So the maximum over [0, r] is at min(r, tc), and its value is the
    formula, in each of the three cases.  Then the attainment in the plane is
    checked numerically on examples."""
    s, t, c, v = variables("s t c v")
    g_left = v + (t - 1) * s * s
    g_right = v + (t - 1) * s * s - t * (s - c) ** 2
    check(g_right == v + t * (t - 1) * c * c - (s - t * c) ** 2, "completing the square")
    check(g_left.substitute("s", c) == g_right.substitute("s", c), "agreement at s = c")
    # The three cases (with r for s, and r <= c, c <= r <= tc, r >= tc):
    # (For r <= c the value is g_left(r) = v + (t-1) r^2 directly.)
    r = Poly.var("r")
    check(g_right.substitute("s", r) == v - r * r + 2 * t * c * r - t * c * c, "case c <= r <= tc")
    check(g_right.substitute("s", t * c) == v + t * (t - 1) * c * c, "case r >= tc")
    # For n >= 2r (so r <= c), the value is tn + (t-1) r(r-1), the trace in
    # Corollary 4.9:
    n = Poly.var("n")
    check((r + t * (n - r)) + (t - 1) * r * r == t * n + (t - 1) * r * (r - 1),
          "the reduction for n >= 2r")

    # Attainment in the plane (floating point): unit complex numbers on the
    # common K_r with sum of length s = min(r, tc), and on each copy unit
    # numbers whose sum points the opposite way with length min(s, c).
    for n_value, r_value, t_value in [(5, 1, 3), (6, 2, 2), (7, 4, 2), (8, 6, 3),
                                      (6, 5, 4), (9, 3, 3)]:
        c_value = n_value - r_value
        s_value = min(r_value, t_value * c_value)
        z = {}
        for i, w in enumerate(unit_numbers_with_sum(r_value, s_value)):
            z[("core", i)] = w
        for copy in range(t_value):
            for i, w in enumerate(unit_numbers_with_sum(c_value, min(s_value, c_value))):
                z[(copy, i)] = -w
        _, edges = graph_B(n_value, r_value, t_value)
        energy = -sum(2 * (z[a] * z[b].conjugate()).real for a, b in edges)
        check(abs(energy - common_core_formula(n_value, r_value, t_value)) < 1e-9,
              f"planar attainment for B({n_value},{r_value},{t_value})")


# ----------------------------------------------------------------------------
# Corollary 4.11
# ----------------------------------------------------------------------------

def gf8_multiply(a, b):
    """Multiply in GF(8) = GF(2)[x]/(x^3 + x + 1).  An element is a 3-bit
    integer whose bit i is the coefficient of x^i; 0b1011 is x^3 + x + 1."""
    product_ = 0
    for i in range(3):
        if b >> i & 1:
            product_ ^= a << i
    for degree in (4, 3):                       # reduce modulo x^3 + x + 1
        if product_ >> degree & 1:
            product_ ^= 0b1011 << (degree - 3)
    return product_


def subspaces_meet_only_in_zero(subspaces):
    """Each set of pairs (x, y) of GF(8) elements is closed under addition
    (XOR), and any two meet only in (0, 0)."""
    def closed(S):
        return all((u[0] ^ w[0], u[1] ^ w[1]) in S for u in S for w in S)
    return (all(closed(S) for S in subspaces)
            and all(S & T == {(0, 0)} for S, T in combinations(subspaces, 2)))


def check_corollary_4_11():
    """Corollary 4.11 (a): line graphs, T(n) and rook's graphs; (b)-(e): the
    clique sizes; (g): the cliques K_9 used for q-Kneser graphs."""
    KL, KU = KAPPA_LOWER, KAPPA_UPPER        # kappa lies between these
    # (a) The sum is over the vertices of H.  T(n) = L(K_n): n vertices of
    # degree n - 1, so the sum is n(n-1)(n - 2 - 1/kappa).  K_a box K_b =
    # L(K_{a,b}): a vertices of degree b and b of degree a, so the sum is
    # ab(a + b - 2 - 2/kappa).
    check(7 - 2 >= 1 / KL and 6 - 2 < 1 / KU, "T(n): the sum is >= 0 exactly for n >= 7")
    check(12 - 2 >= 2 / KL and 11 - 2 < 2 / KU, "rook's graphs: exactly for a + b >= 12")
    # The first inequality of Theorem 4.6, with the b copies of K_a and the a
    # copies of K_b (trace 2ab), covers K_2 box K_9 and K_3 box K_8, but not
    # K_4 box K_7 and K_5 box K_6 (an open problem in Section 7).
    def rook(a, b):
        return 2 * a * b, b * comb(a, 2) + a * comb(b, 2)       # (trace, m)
    for a, b in ((2, 9), (3, 8)):
        check(criterion_holds(*rook(a, b)), f"K_{a} box K_{b} is excluded")
    for a, b in ((4, 7), (5, 6)):
        check(criterion_fails(*rook(a, b)), f"K_{a} box K_{b} is not covered")

    # (b)-(d): cliques of size >= 6.  Lines with s+1, n or q+1 points give
    # GQ(s,t) with s >= 5, nets of order n >= 6, polar spaces with q >= 5;
    # Hamming cliques have q vertices; Johnson cliques have n - k + 1, which
    # is >= 6 iff n >= k + 5, and k <= n/2 makes this automatic for k >= 5:
    check(all(2 * k >= k + 5 for k in range(5, 100)) and 2 * 4 < 4 + 5,
          "J(n,k) with k <= n/2: n >= k + 5 follows from k >= 5 (and not from k = 4)")
    # (e) A clique of k-spaces through a fixed (k-1)-space has
    # (q^e - 1)/(q - 1) = 1 + q + ... + q^(e-1) vertices, e = n - k + 1, which
    # increases with e and q.  For k <= n - 2, e >= 3, so the size is at least
    # 1 + q + q^2 >= 7.  For k = n - 1 the graph is complete on
    # 1 + q + ... + q^(n-1) vertices: q + 1 when n = 2 (at least 5 unless
    # q = 2, 3), and at least 7 when n >= 3.
    q = Poly.var("q")
    check((q ** 3 - 1) == (q - 1) * (1 + q + q * q), "(q^3 - 1)/(q - 1) = 1 + q + q^2")
    check(1 + 2 + 2 ** 2 == 7, "1 + q + q^2 >= 7 for q >= 2")
    check([q for q in (2, 3, 4) if q + 1 < 5] == [2, 3], "Grassmann exceptions J_2(2,1), J_3(2,1)")

    # (g) q^k >= 5 for all q, k >= 2 except q = k = 2, since 2^3 = 8 and 3^2 = 9.
    check(2 ** 2 < 5 <= min(2 ** 3, 3 ** 2), "q^k >= 5 except q = k = 2")
    # The K_{q^k + 1} in the proof, for q = 2, k = 3: inside GF(8)^2 the
    # subspaces {(x, ax) : x in GF(8)} (a in GF(8)) and {(0, x)} meet only in 0.
    field = range(8)
    subspaces = [frozenset((x, gf8_multiply(a, x)) for x in field) for a in field]
    subspaces.append(frozenset((0, y) for y in field))
    check(len(set(subspaces)) == 9 and all(len(S) == 8 for S in subspaces)
          and subspaces_meet_only_in_zero(subspaces), "a K_9 in K_2(6,3)")
    # The case q = k = 2, n >= 5: W a 2-dimensional subspace of GF(8); in
    # W + GF(8) the eight subspaces {(x, ax) : x in W} and one 2-dimensional
    # subspace of 0 + GF(8) form a K_9 in K_2(5,2).
    W = [0, 0b001, 0b010, 0b011]                # the span of 1 and x
    subspaces = [frozenset((x, gf8_multiply(a, x)) for x in W) for a in field]
    subspaces.append(frozenset((0, y) for y in W))
    check(len(set(subspaces)) == 9 and all(len(S) == 4 for S in subspaces)
          and subspaces_meet_only_in_zero(subspaces), "a K_9 in K_2(5,2)")


# ----------------------------------------------------------------------------
# Section 4.5: spectral families
# ----------------------------------------------------------------------------

def is_prime_power(q):
    p = next(d for d in range(2, q + 1) if q % d == 0)     # smallest prime factor
    while q % p == 0:
        q //= p
    return q == 1


def check_paley():
    """Corollary 4.12 and the remarks after it.  P(q) is (q-1)/2-regular with
    lambda_min = -(1 + sqrt q)/2, so |lambda_min|/degree = (1 + sqrt q)/(q-1)
    = 1/(sqrt q - 1), which decreases with q."""
    def ratio_upper(q):
        return 1 / (sqrt_lower(q) - 1)

    def ratio_lower(q):
        return 1 / (sqrt_upper(q) - 1)
    check(ratio_upper(37) <= KAPPA_LOWER, "P(37): the ratio is at most kappa")
    check(interval_inside(ratio_lower(37), ratio_upper(37), "0.1965", "0.1975"),
          "the ratio at q = 37 is about 0.197")
    # (Extra: the spectral criterion n |lambda_min| <= 1 + kappa(2m+1) fails
    # for the smaller prime powers q = 1 (mod 4), so 37 is the first it covers.)
    for q in (5, 9, 13, 17, 25, 29):
        check(q * (1 + sqrt_lower(q)) / 2 > 1 + KAPPA_UPPER * (q * (q - 1) // 2 + 1),
              f"P({q}) is not covered")

    # Bosak: all degrees are even and m = q(q-1)/4, which is 1 or 2 (mod 4)
    # exactly for q = 5, 9 (mod 16).  This depends only on q mod 16.
    excluded = [q for q in range(1, 17, 4) if bosak_excludes(q * (q - 1) // 4)]
    check(excluded == [5, 9], f"Paley graphs excluded by Bosak: q = {excluded} (mod 16)")
    check(25 % 16 == 9 and 37 % 16 == 5, "q = 25 and q = 37 are among them")
    new_cases = [q for q in range(37, 100, 4) if is_prime_power(q) and q % 16 in (1, 13)]
    check(new_cases[:2] == [49, 61], f"the first new cases are {new_cases[:2]}")

    # P(13) is graceful (nickgard): vertex i in the cyclic order 0, ..., 12
    # gets labels[i].
    labels = (0, 1, 5, 39, 23, 34, 13, 3, 21, 7, 38, 33, 24)
    squares = {x * x % 13 for x in range(1, 13)}
    vertices = list(range(13))
    edges = [(u, v) for u, v in combinations(vertices, 2) if (v - u) % 13 in squares]
    check(len(edges) == 39 and is_graceful_labeling(vertices, edges, dict(enumerate(labels))),
          "the labeling of P(13)")
    # The Petersen graph K(5,2) is 3-regular with A^2 + A - 2I = J, so its
    # eigenvalues other than 3 are 1 and -2: the ratio is 2/3.  (Hypercubes
    # are bipartite, so lambda_min = -degree and the ratio is 1.)
    petersen_vertices, petersen_edges = kneser_graph(5, 2)
    index = {v: i for i, v in enumerate(petersen_vertices)}
    A = [[0] * 10 for _ in range(10)]
    for u, v in petersen_edges:
        A[index[u]][index[v]] = A[index[v]][index[u]] = 1
    check(all(sum(row) == 3 for row in A), "the Petersen graph is 3-regular")
    check(all(sum(A[i][k] * A[k][j] for k in range(10)) + A[i][j] - 2 * (i == j) == 1
              for i in range(10) for j in range(10)), "A^2 + A - 2I = J")


def check_ramanujan_random_and_lambda_2():
    """Corollaries 4.13 and 4.14(a),(b).  2 sqrt(d-1) < kappa d, i.e.
    4(d-1) < kappa^2 d^2, holds at d = 84 and fails at d = 83; and
    kappa^2 d^2 - 4(d-1) increases for d >= 2/kappa^2 (about 42).
    For (a): n |lambda_min| <= 2n <= kappa 2m once 2m/n >= 2/kappa."""
    check(4 * (84 - 1) < KAPPA_LOWER ** 2 * 84 ** 2, "d = 84")
    check(4 * (83 - 1) > KAPPA_UPPER ** 2 * 83 ** 2, "d = 83 fails")
    check(2 / KAPPA_LOWER ** 2 <= 84, "increasing from d = 84")
    check(2 / KAPPA_LOWER <= Fraction("9.21"), "average degree 9.21 suffices")


def projective_plane_points(q):
    """The points of PG(2,q), q prime: nonzero vectors in GF(q)^3 whose first
    nonzero coordinate is 1."""
    return [v for v in product(range(q), repeat=3)
            if any(v) and next(x for x in v if x) == 1]


def check_polarity_graphs():
    """Corollary 4.14(c), the polarity graph ER_q: points of PG(2,q), with
    x ~ y when x != y and x.y = 0.  With P the diagonal indicator of the q+1
    absolute points (x.x = 0), A' = A + P satisfies A'^2 = J + qI, and
    2m = (q+1)(n-1) with n = q^2 + q + 1; we check these for q = 2, 3, 5, 7.
    Then we check each step of the final inequality, for all q >= 23."""
    for q in (2, 3, 5, 7):
        points = projective_plane_points(q)
        n = len(points)
        check(n == q * q + q + 1, "number of points")

        def orthogonal(x, y):
            return sum(a * b for a, b in zip(x, y)) % q == 0
        A_looped = [[int(orthogonal(x, y)) for y in points] for x in points]
        check(sum(A_looped[i][i] for i in range(n)) == q + 1, "q + 1 absolute points")
        square = [[sum(A_looped[i][k] * A_looped[k][j] for k in range(n)) for j in range(n)]
                  for i in range(n)]
        check(all(square[i][j] == 1 + q * (i == j) for i in range(n) for j in range(n)),
              f"A'^2 = J + qI for q = {q}")
        two_m = sum(map(sum, A_looped)) - (q + 1)            # remove the loops
        check(two_m == (q + 1) * (n - 1), f"2m = (q+1)(n-1) for q = {q}")

    # The certificate A + P + sqrt(q) I has trace n sqrt q + q + 1.  With
    # w = sqrt q and 2m = (q+1)(n-1), the slack of the criterion is
    #     kappa(2m+1) + 1 - (n w + q + 1) = n(kappa(q+1) - w) - q - kappa q:
    kappa, q, n, w = variables("kappa q n w")
    check(kappa * ((q + 1) * (n - 1) + 1) + 1 - (n * w + q + 1)
          == n * (kappa * (q + 1) - w) - q - kappa * q, "the slack")
    # kappa(q+1) - sqrt q > 0.41 at q = 23, and it increases for q >= 23,
    # since its derivative kappa - 1/(2 sqrt q) is positive there:
    check(KAPPA_LOWER * 24 - sqrt_upper(23) > Fraction(41, 100), "q = 23")
    check(KAPPA_LOWER > 1 / (2 * sqrt_lower(23)), "increasing from q = 23")
    # So the slack exceeds 0.41(q^2+q+1) - q - kappa q, and that minus
    # 0.41 q^2 - 1.22 q is (0.63 - kappa) q + 0.41 > 0:
    a = Fraction(41, 100)
    check(a * (q * q + q + 1) - q - kappa * q - (a * q * q - Fraction(122, 100) * q)
          == (Fraction(63, 100) - kappa) * q + a, "the last step")
    check(KAPPA_UPPER < Fraction(63, 100), "kappa < 0.63")
    check(a * 23 > Fraction(122, 100), "0.41 q^2 - 1.22 q > 0 for q >= 23")


# ----------------------------------------------------------------------------
# Section 4.3 and Section 7: values of mu for complete multipartite graphs
# ----------------------------------------------------------------------------

def mu_complete_multipartite(parts):
    """Proposition 4.15(c): mu = sum a_i^2 - (2 max a_i - n)_+^2."""
    n = sum(parts)
    return sum(a * a for a in parts) - max(2 * max(parts) - n, 0) ** 2


def check_multipartite_values():
    """Section 4.3: mu(K_{3,3,3}) = 27 and mu(K_{2,2,2,2,2}) = 20, 'both too
    large', i.e. larger than beta_m (m = 27 and 40), so positivity cannot
    exclude them.  Section 7: beta_40 is about 18.6, and mu(K_{1,1,1,1,N}) =
    8N - 12 > beta_m for N >= 4, so positivity cannot exclude K_{1,1,1,1,N}.  These evaluate the formula of Proposition 4.15(c);
    they do not re-prove it."""
    check(mu_complete_multipartite([3, 3, 3]) == 27, "mu(K_{3,3,3}) = 27")
    check(mu_complete_multipartite([2] * 5) == 20, "mu(K_{2,2,2,2,2}) = 20")
    check(27 > beta_upper(27), "27 > beta_27")
    check(20 > beta_upper(40), "20 > beta_40")
    check(interval_inside(beta_lower(40), beta_upper(40), "18.55", "18.65"),
          "beta_40 is about 18.6")
    # K_{1,1,1,1,N}: sum a_i^2 = N^2 + 4 and 2 max a_i - n = N - 4 >= 0.
    N = Poly.var("N")
    check((N * N + 4) - (2 * N - (N + 4)) ** 2 == 8 * N - 12, "8N - 12")
    check(all(mu_complete_multipartite([1, 1, 1, 1, k]) == 8 * k - 12 for k in range(4, 20)),
          "8N - 12, directly")
    # 'Positivity cannot help': 8N - 12 > beta_m with m = 4N + 6.  For
    # 4 <= N <= 9 use beta_upper; for N >= 10 (m >= 46) Lemma A.1 gives
    # beta_m <= 1 + 525(8N + 13)/2399, and the difference is positive for
    # N = 10 + u with u >= 0.
    check(all(8 * k - 12 > beta_upper(4 * k + 6) for k in range(4, 10)), "N = 4, ..., 9")
    u = Poly.var("u")
    difference = (8 * N - 12) - (1 + Fraction(525, 2399) * (8 * N + 13))
    check(all_coefficients_positive(difference.substitute("N", 10 + u)), "N >= 10")


CHECKS = [
    ("Sec. 4, Table 1", "decimal values of the constants", check_decimal_constants),
    ("Cor. 4.4", "K_n, windmills, barbells, K_n box P_r and C_r", check_corollary_4_4),
    ("Cor. 4.5", "the density bound; >= 6 equal parts", check_corollary_4_5),
    ("Thm. 4.6", "threshold 6; mixed systems (6,4) and (6,5,5)", check_theorem_4_6),
    ("Sec. 4.4", "two or three K_4's, by iterated parity", check_two_or_three_K4),
    ("Sec. 4.4", "graceful K_4-snakes for t = 4, 6 (and 5)", check_K4_snakes),
    ("Cor. 4.8(c)", "the parity companion", check_corollary_4_8c),
    ("Cor. 4.9", "B(n,r,t): the certificate, thresholds, n >= 2.4r + 6", check_corollary_4_9),
    ("Prop. 4.10", "exact values for B(n,r,t)", check_proposition_4_10),
    ("Cor. 4.11", "line graphs, rook's graphs, clique sizes, q-Kneser", check_corollary_4_11),
    ("Cor. 4.12", "Paley graphs, P(13), Bosak classes", check_paley),
    ("Cor. 4.13, 4.14", "d >= 84, average degree 9.21", check_ramanujan_random_and_lambda_2),
    ("Cor. 4.14(c)", "polarity graphs ER_q, q >= 23", check_polarity_graphs),
    ("Sec. 4.3, 7", "mu of K_{3,3,3}, K_{2,2,2,2,2}, K_{1,1,1,1,N}; beta_40",
     check_multipartite_values),
]
