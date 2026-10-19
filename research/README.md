# Research after the paper

This folder holds two results found after version 2 of the paper. Neither
appears in the paper on Hexagon. Both are computer proofs, and nothing here
has been refereed. The programs and the text were written by Claude Opus 5.5
(Anthropic).

| Folder | Result |
| --- | --- |
| [`b_n_r_t/`](b_n_r_t/) | Which graphs B(n, r, t) are graceful, for 2 ≤ r ≤ 5 and 2 ≤ t ≤ 5 (all n). |
| [`k6_join_4/`](k6_join_4/) | K₆ ∨ K̄₄ is not graceful: a certificate that combines Tools I, II and III. |

The two parts can be read independently. Part 1 is about a method of proof
that we think deserves to be better known. Part 2 shows that the paper's tools
are stronger together than apart.

## Part 1. Proof by computation: the end-game search

### The graphs

**B(n, r, t)** is t copies of the complete graph K_n that share a common
K_r. So it has r *shared* vertices, adjacent to all others, and t *copies* of
n − r further vertices, each adjacent to everything in its own copy. It has

  m = C(r, 2) + t (C(n, 2) − C(r, 2))

edges. B(n, 2, 2) is two cliques sharing an edge, and B(n, n − 1, t) is
K_{n−1} ∨ K̄_t. Bermond asked which B(n, r, t) are graceful. Gallian's survey
(25th edition, 2022) lists the following answers:

- B(3, 2, t), B(4, 2, t) and B(4, 3, t) are graceful for all t.
- B(n, 2, 2) is graceful exactly for n ≤ 5 (Bermond and Farhi; Smith and Puget).
- B(n, 3, 2) is not graceful for 6 ≤ n ≤ 10, B(6, 3, 3) and B(7, 3, 3) are
  not graceful, and B(5, 3, 3) is graceful (Smith and Puget).

### The result

For 2 ≤ r ≤ 5 and 2 ≤ t ≤ 5, B(n, r, t) is graceful exactly for these n, and
for no other n > r:

| | t = 2 | t = 3 | t = 4 | t = 5 |
|---|---|---|---|---|
| r = 2 | 3, 4, 5 | 3, 4 | 3, 4, 5 | 3, 4, 6 |
| r = 3 | 4 | 4, 5 | 4, 5 | 4 |
| r = 4 | none | none | none | none |
| r = 5 | none | none | none | none |

The graceful labelings of B(5, 2, 4), B(6, 2, 5) and B(5, 3, 4) are new, as
far as we can tell (they are not in Gallian's survey). Beyond the table,
B(5, 2, 6) and B(5, 2, 7) are graceful too. So B(5, 2, t) is graceful for
t = 2, 4, 6, 7 but not for t = 3, 5, and gracefulness is not monotone in t.
The rows r = 4 and r = 5 suggest a conjecture: for t ≥ 2, B(n, 4, t) and
B(n, 5, t) are never graceful.

Each entry is proved in two parts. A complete search settles each small n,
which is finite work. The interesting part is the proof for all large n at
once, by a single finite search. Below we explain how it works, why it works,
and when it cannot.

### The end-game lemma

Take a graceful labeling of a graph with m edges. Some edge has difference
m − j. Its labels are a and a + (m − j), both in [0, m], so a ≤ j, and the
other label is m − (j − a). Fix L, call the labels 0, 1, …, L *low* and the
labels m, m − 1, …, m − L *high*, and write *high k* for the label m − k. We
have shown:

> The L + 1 largest differences m, m − 1, …, m − L are realized only by edges
> from a low label a to a high label k, with difference m − (a + k).

When m ≥ 2L + 1 the low and high labels are 2L + 2 different numbers.
Describe a low–high edge by its *sum* a + k (its difference is m − (a + k)),
and an edge between two low or two high labels by its difference, which is
at most L. The vertices on these labels must then form an *L-end-game*:

- the sums of the low–high edges are distinct, and each of 0, 1, …, L is
  one of them;
- the differences of the other edges are distinct.

Nothing here mentions m. A graceful labeling satisfies one more condition:
a difference m − (a + k) must not equal a difference |a − a′|. This can
happen only when m ≤ 3L, and we do not use it. So the search for
L-end-games is the same search for every m ≥ 2L + 1. If it fails, no member
of the family with that many edges is graceful. We state the results for
m ≥ 2L + 2, slightly more than needed; the complete searches cover the
remaining n anyway.

### Why the search does not depend on n

The search places vertices on low and high labels one at a time. In B(n, r, t),
two vertices are adjacent according to their *kinds* only: shared, or in copy
g. So a new vertex is described by its kind, and n enters only as a cap on
how many vertices a copy has. The search ignores the cap. For a particular
n, this offers more choices than really exist. So a failure of the
search with no cap is a failure for every n at once.

Knuth discovered this idea for K_n □ P_2 and K_n □ P_3, in his note *Coups
de grâceful graphs* (2020, revised 2026). He noticed that, for every large
n, his program performed essentially the same computation. Our program reproduces
his K_n □ P_2 case: its search fails at depth L = 23, which covers
m = n² ≥ 48, that is, n ≥ 7.

### A small example: one clique

Let G = K_n. All vertices are adjacent, so all labels lie on a single Golomb
ruler (all pairwise differences distinct). Let A be the set of low labels in
use and K the set of high positions k. An L-end-game says:

- the sums a + k with a in A and k in K are all different, and they
  include 0, 1, …, L;
- A ∪ {m − k : k in K} is a Golomb ruler.

Already at L = 5 the search fails, after 8 nodes. So K_n is not graceful
when C(n, 2) ≥ 12, that is, for n ≥ 6. With a direct check of K_5, this is
Golomb's theorem that K_n is graceful only for n ≤ 4.

For B(n, r, t) the same structure is repeated once per copy. Each copy g
contributes a sumset A_g + K_g. These sumsets, together with the sums
involving shared vertices, must be disjoint and must cover 0, …, L, while
every ruler inside them stays a ruler. Such covers are rare, and the
conflicts pile up as L grows. We believe this is why the search dies.

### When the method cannot work

The method fails as soon as a family has large *graceful pieces* that can sit
at the extreme labels. The simplest such piece is a star. Put its centre on
label 0 and its leaves on m, m − 1, …, m − L. This realizes every top
difference, and the leaves, being independent, impose no further
constraints. So the search survives at every depth for a family with induced
stars K_{1,s} for all s.

This rules out several families. In B(n, r, t) with t growing, a shared
vertex and one vertex from each copy form an induced K_{1,t}. That is why the
method needs t fixed, and why the depth grows with t:

| L | t = 2 | t = 3 | t = 4 | t = 5 |
|---|---|---|---|---|
| r = 2 | 13 | 26 | 39 | 54 |
| r = 3 | 16 | 26 | 45 | 63 |
| r = 4 | 16 | 27 | 45 | 66 |
| r = 5 | 16 | 27 | 47 | 66 |

The same applies to windmills with many blades and to complete multipartite
graphs with one large part. Long induced paths are just as bad: the zigzag
labeling 0, m, 1, m − 1, 2, … realizes the top differences one after
another. In the families we tried, the method works when every
neighbourhood is covered by a bounded number of cliques and there are no
large induced stars or long induced paths. Then the rigidity of Golomb
rulers takes over.

### From large n to all n

Let L be the depth at which the search fails and n0 the smallest n with
m ≥ 2L + 2. The end-game search covers n ≥ n0. A complete search, with
symmetry reduction, covers each r < n < n0. It is also run at n = n0, as a
cross-check.

### What makes the proof sound

Each shortcut in the programs is a step of the proof, so we list them.

1. **The lemma.** For m ≥ 2L + 1 the low and high labels are distinct, and
   only low–high edges realize the top L + 1 differences.
2. **Two kinds of differences.** The program keeps the sums a + k and the
   differences |a − a′| apart. It checks that the sums are distinct and that
   the differences are distinct, but not that a difference differs from
   every m − (a + k). So it may miss a conflict, when m ≤ 3L. It never
   reports a conflict that is not there.
3. **Symmetry.** A new vertex is chosen from one representative of each
   class of vertices that an automorphism of the graph, fixing the vertices
   already placed, can interchange. Interchangeable choices give identical
   subtrees.
4. **The cap on copies.** It is ignored, as explained above, and this only
   adds options.
5. **Order of work.** The search always realizes next the difference with the
   fewest remaining options. Every one of these differences must be realized,
   so any order is valid.

The complete search for one graph is complete for a simple reason. When all
m differences are realized, all m edges join placed vertices. Every vertex has
an edge, so every vertex is placed.

The programs, data and checker are in [`b_n_r_t/`](b_n_r_t/). The checker
verifies every graceful labeling from scratch and confirms that the depths
and complete searches together decide every n > r.

## Part 2. Combining the tools: K₆ ∨ K̄₄

The graph K₆ ∨ K̄₄ is a clique on six vertices joined to four independent
vertices, with 10 vertices and m = 39 edges. An exhaustive search shows
that it is not graceful. Each tool of the paper fails on it separately:

- Tool I: it passes the iterated parity test, and its residue equations,
  with capacities, are solvable for every q ≤ 16;
- Tool II: positivity misses it;
- Tool III: it satisfies the interval bounds.

Used together, the tools succeed. They enter in the order I, III, II:
residues split the problem into cases, positions give the variables of each
case, and positivity gives constraints on those variables. Without the
residue split, steps 2 and 3 alone have a solution.

1. **Residues (Tool I).** Reduce a graceful labeling mod 8. The residue
   classes of the clique and of the independent vertices then satisfy the
   residue equations and the capacities. There are 768 such residue maps,
   and a short brute-force enumeration finds them all.
2. **Positions in [0, m] (Tool III).** Fix one residue map. Model "vertex class g has a
   vertex on label a" by numbers p_{g,a} in [0, 1], and pairs of such events
   by numbers y. These satisfy linear constraints that every graceful
   labeling satisfies: the right number of vertices per class, at most one
   vertex per label, and exactly one edge of each difference 1, …, 39.
3. **Positivity (Tool II).** For a genuine labeling, certain matrices P
   built from p and y are positive semidefinite (PSD). One of them is
   (1, p)(1, p)ᵀ. For any rational PSD matrix Z, the inequality
   ⟨Z, P⟩ ≥ 0 is then a valid *linear* constraint.

For each residue map, the certificate gives rational multipliers that combine
these constraints into an inequality w·v ≤ d, where v is the vector of all
the variables. But the minimum of w·v, with every variable in [0, 1],
exceeds d. This is the Farkas form of "the constraints have no solution". For 740 maps the linear constraints suffice. The other 28 need
the PSD cuts. The verifier checks all of this in exact arithmetic in about 20
seconds.

The certificates were found with floating-point LP and SDP solvers. Only
their output, rounded to rationals, is checked. See
[`k6_join_4/`](k6_join_4/).
