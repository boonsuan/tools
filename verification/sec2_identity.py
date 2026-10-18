"""Section 2 of the paper: the master identity, Lemma 2.1, and the dictionary.

Claims checked here
-------------------
* Figure 1: the labels 0, 1, 4, 6 form a graceful labeling of K_4, and both
  sides of the master identity (1) are z^-6 + ... + z^-1 + z + ... + z^6.
* Introduction: on a path with three edges, the labels 0, 1, 3, 0 also satisfy
  the identity, although they are not a graceful labeling.
* Lemma 2.1: the stated decimals of alpha and kappa, and the Redei-Renyi
  constant 2/(3 pi) = 0.2122... < kappa.
* Section 2.1: the rho-labeling of K_{4,4,4} in Z_97 printed in the paper,
  and one of K_{5,5,5} in Z_151, two graphs that are not graceful.
"""
from collections import Counter
from fractions import Fraction

from exact import check, KAPPA_LOWER, KAPPA_UPPER, PI_LOWER, PI_UPPER, ALPHA_TRIAL
from graphs import (clique_edges, complete_multipartite, is_graceful_labeling,
                    required_differences, signed_differences)


# ----------------------------------------------------------------------------
# Figure 1 and the identity
# ----------------------------------------------------------------------------

def check_figure_1_and_identity():
    """Figure 1: 0, 1, 4, 6 is a graceful labeling of K_4, and the identity
    (1) holds for it.  The identity does not see that labels are distinct:
    the labels 0, 1, 3, 0 on a path with three edges satisfy it too."""
    vertices = [0, 1, 2, 3]
    edges = clique_edges(vertices)
    labels = {0: 0, 1: 1, 2: 4, 3: 6}
    check(is_graceful_labeling(vertices, edges, labels),
          "0,1,4,6 should be a graceful labeling of K_4")
    check(signed_differences(edges, labels) == required_differences(6),
          "both sides of (1) should be z^-6 + ... + z^6 without z^0")

    path_edges = [("a", "b"), ("b", "c"), ("c", "d")]
    path_labels = {"a": 0, "b": 1, "c": 3, "d": 0}
    check(signed_differences(path_edges, path_labels) == required_differences(3),
          "0,1,3,0 on a path with three edges should satisfy the identity")
    check(len(set(path_labels.values())) < 4, "the labels 0,1,3,0 repeat 0")


# ----------------------------------------------------------------------------
# Lemma 2.1
# ----------------------------------------------------------------------------

def check_lemma_2_1_decimals():
    """Lemma 2.1: alpha = 4.4934..., kappa = 0.21723362821..., and
    2/(3 pi) = 0.2122... is smaller than kappa."""
    # ALPHA_TRIAL < alpha was certified in exact.py.  For an upper bound use
    # kappa = 1/sqrt(1 + alpha^2), i.e. alpha^2 = 1/kappa^2 - 1 < 1/KAPPA_LOWER^2 - 1.
    check(Fraction(44934, 10000) <= ALPHA_TRIAL, "alpha should be at least 4.4934")
    check(1 / KAPPA_LOWER ** 2 - 1 < Fraction(44935, 10000) ** 2,
          "alpha should be below 4.4935")
    check(Fraction(21723362821, 10 ** 11) <= KAPPA_LOWER
          and KAPPA_UPPER < Fraction(21723362822, 10 ** 11),
          "kappa should begin 0.21723362821")
    check(Fraction(2122, 10000) < 2 / (3 * PI_UPPER)
          and 2 / (3 * PI_LOWER) < Fraction(2123, 10000),
          "2/(3 pi) should begin 0.2122")
    check(2 / (3 * PI_LOWER) < KAPPA_LOWER, "2/(3 pi) should be below kappa")


# ----------------------------------------------------------------------------
# Section 2.1: rho-labelings
# ----------------------------------------------------------------------------

def is_rho_labeling(part_residues, modulus):
    """A rho-labeling of K_{n_1,...,n_r} with m edges is a choice of distinct
    residues mod 2m+1 such that the signed differences along the edges are
    all the nonzero residues, each once."""
    sizes = [len(part) for part in part_residues]
    vertices, edges = complete_multipartite(sizes)
    residues = dict(zip(vertices, [x for part in part_residues for x in part]))
    return (modulus == 2 * len(edges) + 1
            and len(set(residues.values())) == len(vertices)
            and signed_differences(edges, residues, modulus)
            == Counter(range(1, modulus)))


def check_rho_labelings_of_K444_and_K555():
    """Section 2.1: K_{4,4,4} (m = 48) has a rho-labeling in Z_97, and
    K_{5,5,5} (m = 75) has one in Z_151.

    Both were found by computer search in this collaboration.  The K_{4,4,4}
    one (printed in the paper) was found among maps invariant under the
    multiplier 35, which has order 3 mod 97 and permutes the three parts;
    the K_{5,5,5} one (not printed) has the interval {0,...,4} as a part."""
    k444 = [(1, 3, 44, 57), (8, 35, 55, 85), (61, 65, 82, 86)]
    k555 = [(0, 1, 2, 3, 4), (5, 13, 59, 105, 118), (28, 67, 73, 112, 134)]
    check(is_rho_labeling(k444, 97), "K_{4,4,4} modulo 97")
    check(is_rho_labeling(k555, 151), "K_{5,5,5} modulo 151")

    check(pow(35, 3, 97) == 1, "35 should have order 3 modulo 97")
    check({tuple(sorted(35 * x % 97 for x in part)) for part in k444}
          == {tuple(sorted(part)) for part in k444},
          "multiplication by 35 should permute the parts of the K_{4,4,4} labeling")


CHECKS = [
    ("Fig. 1, eq. (1)", "graceful K_4 and the master identity", check_figure_1_and_identity),
    ("Lemma 2.1", "decimals of alpha, kappa and 2/(3 pi)", check_lemma_2_1_decimals),
    ("Sec. 2.1", "rho-labelings of K_{4,4,4} (Z_97) and K_{5,5,5} (Z_151)",
     check_rho_labelings_of_K444_and_K555),
]
