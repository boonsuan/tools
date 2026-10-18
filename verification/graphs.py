"""Small graph constructions, and the multisets of differences that appear in
the master identity.

Graphs are given as a list of vertices and a list of edges (pairs of
vertices).  Labelings are dictionaries {vertex: label}.  Nothing here is
optimized; the graphs in this package have at most a few hundred edges.

The master identity (1) of the paper says, for a graceful labeling f of a
graph with m edges,

    sum over edges uv of  z^(f(u)-f(v)) + z^(f(v)-f(u))  =  sum over 0<|k|<=m of z^k.

Comparing coefficients, the multiset of SIGNED differences f(u) - f(v),
f(v) - f(u) over the edges equals the multiset {k : 0 < |k| <= m}.  Reading
the identity modulo z^q - 1 means comparing these multisets modulo q.  The
functions signed_differences and required_differences compute the two sides.
"""
from collections import Counter
from itertools import combinations


# ----------------------------------------------------------------------------
# Labelings and the two sides of the identity
# ----------------------------------------------------------------------------

def signed_differences(edges, labels, modulus=None):
    """The exponents on the left of the identity: f(u) - f(v) and f(v) - f(u)
    for each edge uv, as a multiset (reduced mod `modulus` if given)."""
    result = Counter()
    for u, v in edges:
        for d in (labels[u] - labels[v], labels[v] - labels[u]):
            result[d if modulus is None else d % modulus] += 1
    return result


def required_differences(m, modulus=None):
    """The exponents on the right of the identity: every k with 0 < |k| <= m,
    as a multiset (reduced mod `modulus` if given)."""
    return Counter(k if modulus is None else k % modulus
                   for k in range(-m, m + 1) if k != 0)


def is_graceful_labeling(vertices, edges, labels):
    """The definition: distinct labels in {0,...,m} whose edge differences
    |f(u) - f(v)| are exactly 1, 2, ..., m."""
    m = len(edges)
    values = [labels[v] for v in vertices]
    return (len(set(values)) == len(values)
            and all(0 <= x <= m for x in values)
            and Counter(abs(labels[u] - labels[v]) for u, v in edges)
            == Counter(range(1, m + 1)))


# ----------------------------------------------------------------------------
# Graphs
# ----------------------------------------------------------------------------

def clique_edges(vertices):
    """All pairs of the given vertices: the edges of a complete graph on them."""
    return list(combinations(vertices, 2))


def complete_multipartite(part_sizes):
    """K_{part_sizes}.  Vertices are (i, k) for k = 0, ..., part_sizes[i] - 1,
    listed part by part; edges join vertices in different parts."""
    vertices = [(i, k) for i, size in enumerate(part_sizes) for k in range(size)]
    edges = [(u, v) for u, v in combinations(vertices, 2) if u[0] != v[0]]
    return vertices, edges


def cartesian_product_with_path_or_cycle(n, r, cycle):
    """K_n box P_r (cycle=False) or K_n box C_r (cycle=True, r >= 3).

    Vertices are (column j, position i) with 0 <= j < r and 0 <= i < n.  Each
    column is a K_n, and vertex i of column j is joined to vertex i of
    column j+1 (and of column 0, from the last column, for the cycle).
    """
    vertices = [(j, i) for j in range(r) for i in range(n)]
    edges = [((j, a), (j, b)) for j in range(r) for a, b in combinations(range(n), 2)]
    links = range(r) if cycle else range(r - 1)
    for j in links:
        edges += [((j, i), ((j + 1) % r, i)) for i in range(n)]
    return vertices, edges


def kneser_graph(n, k):
    """K(n,k): the k-subsets of {0,...,n-1}, adjacent when disjoint."""
    vertices = list(combinations(range(n), k))
    edges = [(a, b) for a, b in combinations(vertices, 2) if not set(a) & set(b)]
    return vertices, edges
