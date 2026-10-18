"""Section 3 of the paper: parity and residues (Tool I).

Claims checked here
-------------------
* Section 3.1 and Example 3.4: the families excluded by Bosak's condition
  (cycles, complete graphs, windmills).
* Section 3.2: the cut sizes of K_8; Example 3.6 (K_9); and the list of
  complete graphs K_n, 4 <= n <= 30, that survive Golomb's condition and the
  iterated parity test of Proposition 3.5.
* Section 3.3 and Corollary 3.7: the cyclic difference set for K_6 modulo 31,
  and the modulus-3 obstruction for n = 6, 10, 11 (mod 12).
* Section 3.4 and Corollary 3.8: identity (2) on actual graceful labelings,
  the arithmetic of the proof of Corollary 3.8, and the remark on
  K_{1,1,1,1,N}.
* Corollary 3.9: each step of the proof (the identity at z = -1 and z = i),
  and, after it, that K_6 v complement(K_4) is not graceful although it
  passes the iterated parity test and the residue equations for q <= 16.
* Corollary 3.10: each step of the proof; the conclusion on small cases;
  that Golomb's condition does not exclude these graphs; and an exhaustive
  search showing that K_{1,1,1,1,2,2} is not graceful.
* Section 3.5: the windmill cut counts, and the archived residue maps showing
  that the residue equations, together with the capacities, are solvable for
  every modulus 2 <= q <= 12 for K_{3,3,3}, K_{2,2,2,2,2}, K_{4,4,4} and
  K_{3,4,5}.

Throughout, m is the number of edges and "Bosak's condition" is
Corollary 3.3: if every degree is even then m = 0 or 3 (mod 4).

Several claims below are "for all n" statements whose truth depends only on
n modulo some period (for example C(n,2) mod 4 depends only on n mod 8).
For those we check one full period, which proves the claim; the comments
say which period.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from math import comb, isqrt
from pathlib import Path
import json

from exact import check
from polynomial import Poly, variables
from graphs import (clique_edges, complete_multipartite, required_differences,
                    signed_differences)

DATA = Path(__file__).resolve().parent / "data"


def bosak_excludes(m):
    """True when Bosak's condition fails for m edges, i.e. m = 1 or 2 (mod 4),
    so that a graph with m edges and all degrees even is not graceful."""
    return m % 4 in (1, 2)


# ----------------------------------------------------------------------------
# Section 3.1 and Example 3.4: Bosak's condition
# ----------------------------------------------------------------------------

def check_bosak_examples():
    """Section 3.1: K_n is excluded when n = 5 or 7 (mod 8).  (For C_n, with
    all degrees 2 and m = n, the claim n = 1, 2 (mod 4) is Bosak's condition
    verbatim.)  Example 3.4: K_3^(t), with m = 3t, is excluded when
    t = 2, 3 (mod 4), and K_5^(t), with m = 10t, when t is odd."""
    # K_n with n odd has all degrees n - 1 even.  C(n,2) mod 4 depends only
    # on n mod 8, so one period proves the claim for all n; among odd n the
    # excluded classes are exactly 5 and 7.
    excluded = [n for n in range(1, 9, 2) if bosak_excludes(comb(n, 2))]
    check(excluded == [5, 7], f"K_n with n odd: excluded classes mod 8 are {excluded}")
    # Windmills: all degrees are even (n - 1, or t(n - 1) at the centre).
    # 3t mod 4 depends on t mod 4, and 10t mod 4 on t mod 2.
    excluded = [t for t in range(4) if bosak_excludes(3 * t)]
    check(excluded == [2, 3], f"K_3^(t): excluded classes mod 4 are {excluded}")
    check(bosak_excludes(10 * 1), "K_5^(t) with t odd: m = 10t = 2 (mod 4)")


# ----------------------------------------------------------------------------
# Section 3.2: Golomb's condition and iterated parity for complete graphs
# ----------------------------------------------------------------------------
#
# For K_n, the edges with odd difference form the cut between the vertices
# with even and with odd labels; if a vertices have even labels, the cut is
# K_{a,n-a} with a(n-a) edges.  Golomb's condition asks for a cut with exactly
# ceil(m/2) edges.
#
# Iterated parity (Proposition 3.5): after removing that cut, what remains,
# G_1, is a disjoint union of cliques (here K_a and K_{n-a}), and it must
# again have a cut with exactly ceil(m_1/2) edges, where m_1 = floor(m/2);
# and so on.  Splitting a clique K_s as K_a + K_{s-a} cuts a(s-a) of its
# edges and keeps C(a,2) + C(s-a,2).  A "state" below is the sorted tuple of
# clique sizes of the current G_j (cliques with fewer than 2 vertices are
# dropped, since they have no edges).  Removing a cut with ceil(m_j/2) edges
# is the same as keeping exactly floor(m_j/2) = m_(j+1) edges.

def golomb_cut_exists(n):
    """Does K_n have a cut K_{a,n-a} with exactly ceil(m/2) edges?"""
    m = comb(n, 2)
    return any(a * (n - a) == (m + 1) // 2 for a in range(n + 1))


@lru_cache(maxsize=None)
def next_levels(state):
    """All states G_(j+1) that can follow the state G_j: split every clique
    in two so that exactly floor(m_j/2) edges are kept."""
    m = sum(comb(s, 2) for s in state)
    target = m // 2
    # Treat the cliques one at a time, recording (edges kept so far, pieces).
    options = {(0, ())}
    for s in state:
        new_options = set()
        for kept, pieces in options:
            for a in range(s // 2 + 1):
                kept_now = kept + comb(a, 2) + comb(s - a, 2)
                if kept_now <= target:
                    new_pieces = pieces + tuple(x for x in (a, s - a) if x >= 2)
                    new_options.add((kept_now, tuple(sorted(new_pieces))))
        options = new_options
    return tuple(sorted({pieces for kept, pieces in options if kept == target}))


@lru_cache(maxsize=None)
def passes_iterated_parity(state):
    """True if some choice of splittings works at every level, until no
    edges are left."""
    if sum(comb(s, 2) for s in state) == 0:
        return True
    return any(passes_iterated_parity(following) for following in next_levels(state))


def check_K8_and_K9_examples():
    """Section 3.2: the cuts of K_8 have 7, 12, 15 or 16 edges (or none),
    never the required 14.  Example 3.6: K_9 passes Golomb's test only with
    a = 3, leaving K_3 + K_6; the K_6 must then be split 3 + 3; and the
    resulting three triangles have no cut with 5 edges."""
    check({a * (8 - a) for a in range(9)} == {0, 7, 12, 15, 16}, "cuts of K_8")
    check((comb(8, 2) + 1) // 2 == 14, "K_8 needs a cut of 14")
    check([a for a in range(5) if a * (9 - a) == 18] == [3], "K_9 level 0")
    check(next_levels((9,)) == ((3, 6),), "level 0 must leave K_3 + K_6")
    check(next_levels((3, 6)) == ((3, 3, 3),), "level 1 must leave three triangles")
    check(next_levels((3, 3, 3)) == (), "three triangles have no cut of 5 edges")
    check(golomb_cut_exists(9) and not passes_iterated_parity((9,)), "K_9")


def check_complete_graph_table():
    """Section 3.2: for 4 <= n <= 30, iterated parity excludes every K_n
    except n = 4, 6, 11, 18, 25, 27, and Golomb's condition alone also leaves
    n = 9 and 16.  As a finite sanity check of Golomb's criterion (quoted from
    his paper), a cut exists exactly when n or n - 2 is a square, n < 200."""
    golomb = [n for n in range(4, 31) if golomb_cut_exists(n)]
    iterated = [n for n in range(4, 31) if passes_iterated_parity((n,))]
    check(iterated == [4, 6, 11, 18, 25, 27], f"iterated parity survivors {iterated}")
    check(golomb == sorted(iterated + [9, 16]), f"Golomb survivors {golomb}")
    for n in range(4, 200):
        square = any(isqrt(x) ** 2 == x for x in (n, n - 2))
        check(golomb_cut_exists(n) == square, f"Golomb's criterion for K_{n}")


# ----------------------------------------------------------------------------
# Section 3.3: other roots of unity
# ----------------------------------------------------------------------------

def check_K6_modulo_31():
    """Section 3.3: {0,1,3,8,12,18} has every nonzero difference modulo 31
    exactly once, so it satisfies the residue counts for K_6 at q = 31; but
    18 > 15 = m, so it is not a graceful labeling."""
    marks = (0, 1, 3, 8, 12, 18)
    vertices = list(range(6))
    labels = dict(zip(vertices, marks))
    edges = clique_edges(vertices)
    check(signed_differences(edges, labels, 31) == required_differences(15, 31),
          "the residue counts for K_6 at q = 31")
    check(signed_differences(edges, labels, 31) == Counter(range(1, 31)),
          "each nonzero residue mod 31 exactly once")
    check(max(marks) > comb(6, 2), "the label 18 lies outside [0, 15]")


def check_corollary_3_7_modulus_3():
    """Corollary 3.7: the residue equations mod 3 exclude K_n for
    n = 6, 10, 11 (mod 12).  We check each step of the proof, and then, as an
    independent finite check, that the counting equation has no solution."""
    # Step 1.  With x0 + x1 + x2 = n and sum x_i(x_i - 1) = 2 floor(m/3),
    # where m = C(n,2) = 3 floor(m/3) + r:  u^2 - uv + v^2 = n - r for
    # u = x0 - x2, v = x1 - x2.  Two polynomial identities give this:
    x0, x1, x2 = (Poly.var(name) for name in ("x0", "x1", "x2"))
    u, v = x0 - x2, x1 - x2
    n_total = x0 + x1 + x2
    sum_of_squares = x0 * x0 + x1 * x1 + x2 * x2
    check(u * u - u * v + v * v == (3 * sum_of_squares - n_total ** 2) / 2,
          "u^2 - uv + v^2 = (3 sum x_i^2 - n^2)/2")
    # ...and, substituting sum x_i^2 = n + 2 floor(m/3) = n + 2(m - r)/3
    # with m = n(n-1)/2, the right side is n - r:
    n, r = Poly.var("n"), Poly.var("r")
    m = n * (n - 1) / 2
    check((3 * (n + 2 * (m - r) / 3) - n * n) / 2 == n - r, "(3 sum x_i^2 - n^2)/2 = n - r")

    # Step 2.  u^2 - uv + v^2 mod 4 depends on u, v mod 4: never 2.
    check({(a * a - a * b + b * b) % 4 for a in range(4) for b in range(4)} == {0, 1, 3},
          "values of u^2 - uv + v^2 mod 4")

    # Step 3.  n - r mod 4 depends only on n mod 12 (n mod 4, and r = C(n,2)
    # mod 3, which depends on n mod 3).  It is 2 exactly for these classes:
    classes = [n for n in range(12) if (n - comb(n, 2) % 3) % 4 == 2]
    check(classes == [6, 10, 11], f"classes with n - r = 2 (mod 4): {classes}")

    # Independent finite check: for n < 200 in these classes, no counts
    # x0 + x1 + x2 = n satisfy sum x_i(x_i - 1) = 2 floor(m/3).
    # (The corollary claims nothing about other n.)
    for n in range(2, 200):
        if n % 12 in (6, 10, 11):
            m = comb(n, 2)
            solvable = any(a * (a - 1) + b * (b - 1) + (n - a - b) * (n - a - b - 1)
                           == 2 * (m // 3)
                           for a in range(n + 1) for b in range(n + 1 - a))
            check(not solvable, f"modulus 3 should exclude K_{n}")

    # The remark after the corollary: K_6, K_11 and K_18 survive iterated parity.
    for n in (6, 11, 18):
        check(passes_iterated_parity((n,)) and n % 12 in (6, 10, 11), f"K_{n}")


# ----------------------------------------------------------------------------
# Section 3.4: complete split graphs K_s v complement(K_N)
# ----------------------------------------------------------------------------

def split_graph(s, N):
    """K_s v complement(K_N): a clique on s vertices, each joined to all N
    vertices of an independent set.  Returns (clique, independent set, edges)."""
    clique = [("c", i) for i in range(s)]
    independent = [("x", i) for i in range(N)]
    edges = clique_edges(clique) + [(u, x) for u in clique for x in independent]
    return clique, independent, edges


def graceful_labelings(vertices, edges, limit):
    """Up to `limit` graceful labelings, by straightforward backtracking:
    give the vertices labels in {0,...,m} one at a time, and reject a label
    as soon as it repeats an edge difference.  A complete labeling then has
    m distinct differences in {1,...,m}, which are therefore all of them."""
    m = len(edges)
    neighbours = {v: [] for v in vertices}
    for u, v in edges:
        neighbours[u].append(v)
        neighbours[v].append(u)
    found, labels, used_differences = [], {}, set()

    def extend(i):
        if len(found) >= limit:
            return
        if i == len(vertices):
            found.append(dict(labels))
            return
        v = vertices[i]
        for x in range(m + 1):
            if x in labels.values():
                continue
            new = [abs(x - labels[w]) for w in neighbours[v] if w in labels]
            if len(set(new)) == len(new) and not used_differences & set(new):
                labels[v] = x
                used_differences.update(new)
                extend(i + 1)
                used_differences.difference_update(new)
                del labels[v]

    extend(0)
    return found


def check_identity_2_on_examples():
    """Identity (2): S^2 + 2SY = s - 2 epsilon, where S and Y are the sums of
    (-1)^f(v) over the clique and over the independent set, and
    epsilon = m mod 2.  As a sanity check of the derivation we confirm it on
    graceful labelings of small split graphs."""
    tested = 0
    for s, N in [(1, 3), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]:
        clique, independent, edges = split_graph(s, N)
        m = len(edges)
        for labels in graceful_labelings(clique + independent, edges, limit=20):
            S = sum((-1) ** labels[v] for v in clique)
            Y = sum((-1) ** labels[v] for v in independent)
            check(S * S + 2 * S * Y == s - 2 * (m % 2), f"identity (2), s={s}, N={N}")
            tested += 1
    check(tested > 0, "no graceful split graphs were found to test")


def identity_2_solvable(s, N):
    """Is S^2 + 2SY = s - 2 epsilon solvable with S a sum of s signs and Y a
    sum of N signs?"""
    m = comb(s, 2) + s * N
    right_side = s - 2 * (m % 2)
    return any(S * S + 2 * S * Y == right_side
               for S in range(-s, s + 1, 2) for Y in range(-N, N + 1, 2))


def check_corollary_3_8():
    """Corollary 3.8: if s = 8 or 10 (mod 16), K_s v complement(K_2t) is not
    graceful.  We check the steps of the proof, then the remark on
    K_{1,1,1,1,N}."""
    # Steps 1-2.  For N even, epsilon = C(s,2) mod 2, which depends on s mod 4.
    # Writing s = 4k (s = 8 mod 16) or s = 4k + 2 (s = 10 mod 16), the right
    # side s - 2 epsilon is 4k with k = 2 (mod 4).  This depends on s mod 16:
    for s in (8, 10):
        epsilon = comb(s, 2) % 2
        k = s // 4
        check(s - 2 * epsilon == 4 * k and k % 4 == 2, f"s = {s} (mod 16)")
    # Step 3.  With S = 2h: h(h + Y) = k = 2 (mod 4) forces Y odd.  Whether
    # h(h+Y) = 2 (mod 4) depends only on h and Y mod 4:
    for h, Y in product(range(4), repeat=2):
        if h * (h + Y) % 4 == 2:
            check(Y % 2 == 1, "h(h + Y) = 2 (mod 4) should force Y odd")
    # But Y is a sum of N = 2t signs, hence even.

    # Finite sanity check of the conclusion: no solutions for s < 130, even N < 60.
    for s in range(1, 130):
        if s % 16 in (8, 10):
            check(not any(identity_2_solvable(s, N) for N in range(2, 60, 2)),
                  f"Corollary 3.8 for s = {s}")

    # The remark: for K_{1,1,1,1,N} = K_4 v complement(K_N), identity (2) forces
    # S = +-2 and Y = 0, so N is even.  For odd N, all degrees (3 + N and 4)
    # are even and m = 4N + 6 = 2 (mod 4), so Bosak's condition applies.
    # Finite check for N < 60 (the general statement is the same short argument).
    for N in range(1, 60):
        m = 6 + 4 * N
        solutions = {(S, Y) for S in range(-4, 5, 2) for Y in range(-N, N + 1, 2)
                     if S * S + 2 * S * Y == 4 - 2 * (m % 2)}
        check(solutions == ({(2, 0), (-2, 0)} if N % 2 == 0 else set()),
              f"K_(1,1,1,1,{N})")
        if N % 2 == 1:
            check((3 + N) % 2 == 0 and bosak_excludes(m), "odd N by Bosak")


# ----------------------------------------------------------------------------
# Section 3.4: Corollary 3.9 (the identity at z = -1 and z = i)
# ----------------------------------------------------------------------------
#
# Gaussian integers a + bi are represented as pairs (a, b).

def i_power(j):
    """i^j as a Gaussian integer (a, b)."""
    return [(1, 0), (0, 1), (-1, 0), (0, -1)][j % 4]


def right_side_at_i(m):
    """sum over 0 < |j| <= m of i^j, as a Gaussian integer."""
    total = [0, 0]
    for j in list(range(-m, 0)) + list(range(1, m + 1)):
        a, b = i_power(j)
        total[0] += a
        total[1] += b
    return tuple(total)


def check_corollary_3_9_gaussian():
    """Corollary 3.9: for k >= 0, t >= 1 with k + t odd, K_{8k+6} v
    complement(K_{2t}) is not graceful, and for k even neither is the graph
    with one clique edge deleted.  We check each step of the proof."""
    # m = C(s,2) + sN = 3 (mod 4) for s = 8k+6, N = 2t; this depends only on
    # s mod 8 and N mod 4.
    for k, t in product(range(2), range(1, 3)):
        s, N = 8 * k + 6, 2 * t
        check((comb(s, 2) + s * N) % 4 == 3, "m = 3 (mod 4)")
    # The right side of the identity: at z = -1 it is -2 for m odd and 0 for
    # m even; at z = i it is -2 for m = 2, 3 (mod 4).  Both depend on m mod 4.
    for m in range(4, 8):
        at_minus_one = sum((-1) ** j for j in range(-m, m + 1) if j != 0)
        check(at_minus_one == (-2 if m % 2 else 0), "right side at z = -1")
        check(right_side_at_i(m) == ((-2, 0) if m % 4 in (2, 3) else (0, 0)), "right side at z = i")

    # The identity at z = -1 and at z = i, with s = 8k + 6:
    #   |C|^2 - s + 2 Re(C conj(X)) = -2,
    # where C(-1) = 2p, X(-1) = 2q, and C(i) = 2u + 2vi, X(i) = x + yi.
    k, p, q, u, v, x, y = variables("k p q u v x y")
    s = 8 * k + 6
    check((2 * p) ** 2 - s + 2 * (2 * p) * (2 * q) + 2 == 4 * (p * p + 2 * p * q - (2 * k + 1)),
          "at z = -1: p^2 + 2pq = 2k + 1")
    # |2u + 2vi|^2 = 4u^2 + 4v^2 and Re((2u + 2vi)(x - yi)) = 2ux + 2vy:
    check(4 * u * u + 4 * v * v - s + 2 * (2 * u * x + 2 * v * y) + 2
          == 4 * (u * u + v * v + u * x + v * y - (2 * k + 1)),
          "at z = i: u^2 + v^2 + ux + vy = 2k + 1")
    # p^2 + 2pq = 2k + 1 forces p odd and q = k (mod 2); this depends on
    # p, q mod 4 and k mod 2.
    for p_, q_, k_ in product(range(4), range(4), range(2)):
        if (p_ * p_ + 2 * p_ * q_ - (2 * k_ + 1)) % 4 == 0:
            check(p_ % 2 == 1 and q_ % 2 == k_, "p odd and q = k (mod 2)")
    # With p odd, the numbers 4k + 3 +- p of even and odd clique labels are
    # even, so C(i) = (c_0 - c_2) + (c_1 - c_3) i has both parts even.  The
    # parts of X(i) have the parities of the numbers t +- q of even and odd
    # independent labels, which are t + k = 1 (mod 2).  Then u(u + x) and
    # v(v + y) are even, so the left side u^2 + v^2 + ux + vy is even:
    for u_, x_ in product(range(2), range(2)):
        if x_ == 1:
            check(u_ * (u_ + x_) % 2 == 0, "u(u + x) is even when x is odd")
    # Deleting a clique edge ab (k even): m - 1 = 2 (mod 4), so the right sides
    # are 0 at z = -1 and -2 at z = i.  If f(a), f(b) had the same parity, the
    # identity at z = -1 would give p^2 + 2pq = 2k + 2 = 2 (mod 4), which is
    # impossible (it depends on p, q mod 4):
    check(all((p_ * p_ + 2 * p_ * q_) % 4 != 2 for p_, q_ in product(range(4), repeat=2)),
          "p^2 + 2pq is never 2 (mod 4)")
    check((2 * p) ** 2 - s - 2 * (-1) + 2 * (2 * p) * (2 * q)
          == 4 * (p * p + 2 * p * q - (2 * k + 1)),
          "opposite parities give p^2 + 2pq = 2k + 1 again")

    # Finite sanity check of the conclusion: enumerate the residues mod 4 of
    # the clique and independent labels (counts c_r, x_r) and test the
    # identity at z = -1 and z = i directly.
    for s_, N_ in [(6, 2), (6, 6), (6, 10), (14, 4), (14, 8), (22, 2), (22, 6)]:
        m_ = comb(s_, 2) + s_ * N_
        check(not identity_solvable_at_minus_one_and_i(s_, N_, m_),
              f"K_{s_} v complement(K_{N_}) at z = -1 and z = i")


def identity_solvable_at_minus_one_and_i(s, N, m):
    """Are there residue counts mod 4 for the clique (c) and the independent
    set (x) satisfying the identity at z = -1 and at z = i?"""
    def value(counts, z_power):
        a = b = 0
        for r, count in enumerate(counts):
            pa, pb = z_power(r)
            a, b = a + count * pa, b + count * pb
        return a, b
    target_minus_one = sum((-1) ** j for j in range(-m, m + 1) if j != 0)
    target_i = right_side_at_i(m)
    for c in compositions(s, 4):
        for x in compositions(N, 4):
            for z_power, target in (((lambda r: ((-1) ** r, 0)), (target_minus_one, 0)),
                                    (i_power, target_i)):
                (ca, cb), (xa, xb) = value(c, z_power), value(x, z_power)
                # |C|^2 - s + 2 Re(C conj(X)), with C = ca + cb i, X = xa + xb i
                left = ca * ca + cb * cb - s + 2 * (ca * xa + cb * xb)
                if (left, 0) != target:
                    break
            else:
                return True
    return False


def compositions(total, parts):
    """All ways to write total as an ordered sum of `parts` nonnegative integers."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


# The remark after Corollary 3.9: K_6 v complement(K_4).

def graceful_labelings_of_K6_join(N):
    """All graceful labelings of K_6 v complement(K_N), as (clique labels,
    independent labels), with 0 among the clique labels.  (The edge with
    difference m joins the labels 0 and m, so one of them is on the clique;
    replacing f by m - f, we may assume it is 0.)  The clique labels form a
    Golomb ruler; the 6N cross differences must be exactly the differences
    1, ..., m that the ruler does not use."""
    s = 6
    m = comb(s, 2) + s * N
    found = []

    def rulers(prefix, used):
        if len(prefix) == s:
            yield prefix, used
            return
        for a in range(prefix[-1] + 1, m + 1):
            new = {a - b for b in prefix}
            if len(new) == len(prefix) and not new & used:
                yield from rulers(prefix + [a], used | new)

    for clique, used in rulers([0], set()):
        missing = frozenset(range(1, m + 1)) - used
        candidates = {}
        for x in range(m + 1):
            differences = frozenset(abs(x - c) for c in clique)
            if x not in clique and len(differences) == s and differences <= missing:
                candidates[x] = differences

        def cover(left, chosen):
            if not left:
                if len(chosen) == N:
                    found.append((clique, sorted(chosen)))
                return
            largest = max(left)          # some independent label must produce it
            for x, differences in candidates.items():
                if largest in differences and differences <= left and x not in chosen:
                    cover(left - differences, chosen + [x])
        cover(missing, [])
    return found


@lru_cache(maxsize=None)
def split_next_levels(state):
    """Iterated parity for disjoint unions of split graphs.  A state is a
    sorted tuple of pieces (a, b) = K_a v complement(K_b).  Splitting a piece
    into (x, y) and (a - x, b - y) cuts x(a-x) + x(b-y) + (a-x)y edges; as in
    next_levels, we keep exactly floor(m_j/2) edges."""
    def edges(piece):
        return comb(piece[0], 2) + piece[0] * piece[1]
    target = sum(edges(p) for p in state) // 2
    options = {(0, ())}
    for a, b in state:
        new_options = set()
        for kept, pieces in options:
            for x, y in product(range(a + 1), range(b + 1)):
                halves = ((x, y), (a - x, b - y))
                kept_now = kept + edges(halves[0]) + edges(halves[1])
                if kept_now <= target:
                    new_pieces = pieces + tuple(h for h in halves if edges(h) > 0)
                    new_options.add((kept_now, tuple(sorted(new_pieces))))
        options = new_options
    return tuple(sorted({pieces for kept, pieces in options if kept == target}))


@lru_cache(maxsize=None)
def split_passes_iterated_parity(state):
    if not state:
        return True
    return any(split_passes_iterated_parity(following) for following in split_next_levels(state))


def check_K6_join_4():
    """The remark after Corollary 3.9: K_6 v complement(K_4) (m = 39) is not
    graceful, by exhaustive search; it passes the iterated parity test; and
    its residue equations with capacities are solvable for every q <= 16
    (the maps in data/residue_maps_K6_join_4.json)."""
    check(graceful_labelings_of_K6_join(4) == [], "K_6 v complement(K_4) should not be graceful")
    check(split_passes_iterated_parity(((6, 4),)), "it passes the iterated parity test")
    records = json.loads((DATA / "residue_maps_K6_join_4.json").read_text(encoding="utf-8"))
    check(sorted(record["modulus"] for record in records) == list(range(2, 17)),
          "one map for each 2 <= q <= 16")
    for record in records:
        check(record["parts"] == [1] * 6 + [4], "the graph K_{1,1,1,1,1,1,4}")
        check_one_residue_map(record)


# ----------------------------------------------------------------------------
# Section 3.4: Corollary 3.10, K_{1,1,1,1,a,b} with a = b = 2 (mod 4)
# ----------------------------------------------------------------------------

def check_corollary_3_10():
    """Corollary 3.10: K_{1,1,1,1,a,b} is not graceful when a = b = 2 (mod 4).
    We check each step of the proof, then the conclusion on small cases."""
    # m = 6 + 4(a+b) + ab = 2 (mod 8); this depends on a, b mod 8.
    for a, b in product((2, 6), repeat=2):
        check((6 + 4 * (a + b) + a * b) % 8 == 2, "m = 2 (mod 8)")
    # At z = -1 (right side 0): (2 tau)^2 - (2 alpha)^2 - (2 beta)^2 - 4 = 0.
    tau, alpha, beta = variables("tau alpha beta")
    check((2 * tau) ** 2 - (2 * alpha) ** 2 - (2 * beta) ** 2 - 4
          == 4 * (tau * tau - 1 - alpha * alpha - beta * beta), "tau^2 = 1 + alpha^2 + beta^2")
    # Modulo 4 this forces alpha, beta even and tau odd (depends on residues mod 4).
    for t_, a_, b_ in product(range(4), repeat=3):
        if (t_ * t_ - 1 - a_ * a_ - b_ * b_) % 4 == 0:
            check(a_ % 2 == 0 and b_ % 2 == 0 and t_ % 2 == 1, "alpha, beta even, tau odd")
    # A(-1) = 2 alpha = 0 (mod 4) and a = 2 (mod 4) make the numbers (a +- A(-1))/2
    # of even and odd labels in that part odd; C(-1) = T - A - B = 2 (mod 4)
    # means the four singletons split 3 + 1.  So A(i), B(i), C(i), and T(i),
    # have odd real and imaginary parts, and x^2 + y^2 = 2 (mod 8) for x, y odd:
    check(all((x * x + y * y) % 8 == 2 for x, y in product(range(1, 8, 2), repeat=2)),
          "odd real and imaginary parts give squared modulus 2 (mod 8)")
    # At z = i the right side is -2 (m = 2 mod 4), so |T|^2 - |A|^2 - |B|^2 = 2,
    # while the left side is 2 - 2 - 2 = 6 (mod 8):
    check(right_side_at_i(2) == (-2, 0) and (2 - 2 - 2) % 8 == 6 != 2, "the contradiction")

    # Finite check of the conclusion: no residue counts mod 4 satisfy the
    # identity at z = -1 and z = i, for small a, b.
    for a, b in [(2, 2), (2, 6), (6, 6), (2, 10)]:
        check(not multipartite_identity_solvable_at_minus_one_and_i(a, b),
              f"K_(1,1,1,1,{a},{b}) at z = -1 and z = i")
    # Golomb's condition does not exclude these graphs: a parity split with
    # the required ceil(m/2) cut edges exists.
    for a, b in [(2, 2), (2, 6), (6, 6), (6, 10)]:
        check(golomb_cut_exists_multipartite([1, 1, 1, 1, a, b]),
              f"Golomb's condition holds for K_(1,1,1,1,{a},{b})")
    # And the smallest member, K_{1,1,1,1,2,2} (m = 26), is not graceful:
    check(not K_1_1_1_1_2_2_is_graceful(), "K_{1,1,1,1,2,2} should not be graceful")


def multipartite_identity_solvable_at_minus_one_and_i(a, b):
    """Residue counts mod 4: s for the four singletons, x and y for the parts
    of sizes a and b.  Test |T|^2 - |A|^2 - |B|^2 - 4 = right side at z = -1, i."""
    m = 6 + 4 * (a + b) + a * b
    targets = [(sum((-1) ** j for j in range(-m, m + 1) if j != 0), 0), right_side_at_i(m)]
    powers = [lambda r: ((-1) ** r, 0), i_power]

    def value(counts, power):
        re = im = 0
        for r, count in enumerate(counts):
            pr, pi = power(r)
            re, im = re + count * pr, im + count * pi
        return re, im

    for s in compositions(4, 4):
        for x in compositions(a, 4):
            for y in compositions(b, 4):
                ok = True
                for power, target in zip(powers, targets):
                    A, B, S = value(x, power), value(y, power), value(s, power)
                    T = (A[0] + B[0] + S[0], A[1] + B[1] + S[1])
                    left = (T[0] ** 2 + T[1] ** 2) - (A[0] ** 2 + A[1] ** 2) - (B[0] ** 2 + B[1] ** 2) - 4
                    if (left, 0) != target:
                        ok = False
                        break
                if ok:
                    return True
    return False


def golomb_cut_exists_multipartite(parts):
    """Is there a choice of odd_i in [0, a_i] (odd labels in part i) whose cut,
    the number of edges between odd and even labels, is ceil(m/2)?"""
    n = sum(parts)
    m = (n * n - sum(p * p for p in parts)) // 2
    for odd in product(*(range(p + 1) for p in parts)):
        total_odd = sum(odd)
        cut = sum(o * ((n - total_odd) - (p - o)) for o, p in zip(odd, parts))
        if cut == (m + 1) // 2:
            return True
    return False


def K_1_1_1_1_2_2_is_graceful():
    """K_{1,1,1,1,2,2} is K_8 minus two disjoint edges, with m = 26.  It is
    graceful iff some 8 labels in [0, 26] (including 0 and 26) have 28
    pairwise differences from which two DISJOINT pairs can be removed to
    leave exactly 1, ..., 26."""
    m = 26
    for middle in combinations(range(1, m), 6):
        labels = (0,) + middle + (m,)
        by_difference = {}
        for x, y in combinations(labels, 2):
            by_difference.setdefault(y - x, []).append((x, y))
        if len(by_difference) != m:
            continue
        repeated = [pairs for pairs in by_difference.values() if len(pairs) > 1]
        if len(repeated) == 2:
            removals = [(p, q) for p in repeated[0] for q in repeated[1]]
        else:                                    # one difference occurring three times
            removals = list(combinations(repeated[0], 2))
        if any(not set(p) & set(q) for p, q in removals):
            return True
    return False


# ----------------------------------------------------------------------------
# Section 3.5: limits of parity
# ----------------------------------------------------------------------------

def check_windmill_cut_counts():
    """Section 3.5: each K_5 blade of K_5^(t) contributes a(5-a), that is
    0, 4 or 6 edges, to Golomb's cut, and these can add up to the required
    ceil(10t/2) = 5t for every even t: give half the blades 4 and half 6."""
    blade = sorted({a * (5 - a) for a in range(6)})
    check(blade == [0, 4, 6], "cut contributions of a K_5 blade")
    # With t even, (t/2) * 4 + (t/2) * 6 = 5t.


def check_one_residue_map(record):
    """One archived map for Section 3.5: residues r(v) mod q of the vertices
    of K_{parts} such that
      (a) the residue equations hold: for each j, the number of ordered pairs
          (u, v), uv an edge, with r(u) - r(v) = j (mod q) equals the number
          of k in [-m, m], k != 0, with k = j (mod q); and
      (b) the capacities hold: at most floor((m - j)/q) + 1 vertices have
          residue j."""
    parts, q, residues = record["parts"], record["modulus"], record["residues"]
    vertices, edges = complete_multipartite(parts)
    check(len(residues) == len(vertices) and all(0 <= x < q for x in residues),
          "malformed record")
    residue_of = dict(zip(vertices, residues))     # both are listed part by part
    m = len(edges)
    check(signed_differences(edges, residue_of, q) == required_differences(m, q),
          f"residue equations for {parts}, q = {q}")
    occupancy = Counter(residues)
    check(all(occupancy[j] <= (m - j) // q + 1 for j in range(q)),
          f"capacities for {parts}, q = {q}")


def check_residue_equations_up_to_12():
    """Section 3.5: for each of K_{3,3,3}, K_{2,2,2,2,2}, K_{4,4,4}, K_{3,4,5}
    and each 2 <= q <= 12, the archive data/residue_witnesses.json holds a map
    satisfying the residue equations and the capacities (4 x 11 = 44 maps)."""
    records = json.loads((DATA / "residue_witnesses.json").read_text(encoding="utf-8"))
    expected = {(parts, q) for parts in [(3, 3, 3), (2, 2, 2, 2, 2), (4, 4, 4), (3, 4, 5)]
                for q in range(2, 13)}
    found = [(tuple(record["parts"]), record["modulus"]) for record in records]
    check(len(found) == len(set(found)) and set(found) == expected,
          "the archive should contain one map for each graph and each q <= 12")
    for record in records:
        check_one_residue_map(record)


CHECKS = [
    ("Sec. 3.1, Ex. 3.4", "families excluded by Bosak's condition", check_bosak_examples),
    ("Sec. 3.2, Ex. 3.6", "cut sizes of K_8; iterated parity for K_9", check_K8_and_K9_examples),
    ("Sec. 3.2", "K_n surviving Golomb / iterated parity, 4 <= n <= 30", check_complete_graph_table),
    ("Sec. 3.3", "K_6 residues modulo 31", check_K6_modulo_31),
    ("Cor. 3.7", "modulus-3 obstruction for n = 6, 10, 11 (mod 12)", check_corollary_3_7_modulus_3),
    ("Sec. 3.4, eq. (2)", "identity (2) on graceful split graphs", check_identity_2_on_examples),
    ("Cor. 3.8", "the parity family of split graphs; K_(1,1,1,1,N)", check_corollary_3_8),
    ("Cor. 3.9", "the Gaussian-integer obstruction", check_corollary_3_9_gaussian),
    ("Sec. 3.4", "K_6 v complement(K_4): not graceful, yet passes parity and residues",
     check_K6_join_4),
    ("Cor. 3.10", "K_(1,1,1,1,a,b) with a = b = 2 (mod 4)", check_corollary_3_10),
    ("Sec. 3.5", "cut counts for K_5 windmills", check_windmill_cut_counts),
    ("Sec. 3.5", "residue maps with capacities for four graphs, q <= 12",
     check_residue_equations_up_to_12),
]
