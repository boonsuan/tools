/*
 * complete_search.c -- decide whether one graph B(n, r, t) is graceful.
 *
 * B(n, r, t) consists of t copies of K_n that share a common K_r.  It has
 *   r shared vertices, adjacent to everything,
 *   t copies of n - r further vertices, adjacent within their own copy,
 * and m = C(r,2) + t (C(n,2) - C(r,2)) edges.
 *
 * THE SEARCH
 * A graceful labeling puts distinct labels from 0..m on the vertices so that
 * the m edge differences are exactly 1..m.  We repeatedly pick a difference d
 * that is not yet realized and branch over the ways to realize it: a pair of
 * labels (x, x + d) that are not both used, with new vertices placed on
 * whichever of the two labels is still free, such that the two vertices are
 * adjacent.  Placing a vertex creates its differences with all adjacent
 * vertices already placed; a branch dies as soon as a difference repeats.
 * We pick the difference with the fewest open pairs (a pair is closed when
 * both labels are used and, d being unrealized, not joined by an edge), and
 * a branch dies when some difference has no open pair left.
 *
 * When every difference is realized, all m edges join placed vertices; since
 * every vertex has an edge, every vertex is placed, and the labeling is
 * graceful.  So the search is complete: it finds a graceful labeling if one
 * exists, and otherwise proves that none does.
 *
 * SYMMETRY
 * A new vertex can be any vertex not yet used.  The automorphisms of B(n,r,t)
 * permute the shared vertices arbitrarily, permute the vertices inside each
 * copy arbitrarily, and permute the copies; vertices that one of these maps
 * onto each other (fixing the vertices already placed) give identical
 * subtrees.  So the candidates for a new vertex are
 *   one more shared vertex, if fewer than r are placed;
 *   one more vertex of each copy in use, if it has fewer than n - r placed;
 *   one vertex of a new copy, if fewer than t copies are in use.
 * Copies come into use in the order 0, 1, 2, ..., so "a new copy" is always
 * the next index.  Each labeling is thus found once up to automorphisms, not
 * once per automorphism.  (We do not use the symmetry x -> m - x of graceful
 * labelings.)
 *
 * PARALLELISM
 * The tree is expanded sequentially to a fixed depth (default 8); the subtrees
 * below are then searched by several threads (OpenMP), and all threads stop
 * when one finds a labeling.  If there are more than MAX_SUBTREES subtrees,
 * the depth is reduced.
 *
 * USAGE
 *   complete_search n r t [split] [threads]
 * prints one line, either
 *   B(n,r,t) m=..: graceful; shared: x x | copy 0: x x x | copy 1: ...
 * or
 *   B(n,r,t) m=..: not graceful
 * followed by the number of search nodes and the running time.
 *
 * Build: gcc -O3 -march=native -fopenmp -o complete_search complete_search.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define MAX_M 1023
#define MAX_VERTICES 256
#define MAX_SUBTREES (1 << 14)        /* states saved for the parallel phase */

static int N, R, T, M;

typedef struct {
    int vertex_on[MAX_M + 1];           /* vertex with label x, or -1 */

    /* vertices, in the order they were created */
    int is_shared[MAX_VERTICES], copy[MAX_VERTICES], label[MAX_VERTICES];
    int vertices;

    uint64_t used[(MAX_M >> 6) + 1];    /* bit d: difference d is realized */

    int shared_used;                    /* shared vertices placed */
    int copy_size[MAX_VERTICES];        /* vertices placed in each copy */
    int copies_used;                    /* copies 0..copies_used-1 are in use */

    long long nodes;
} State;

static int is_used(const State *s, int d) { return (s->used[d >> 6] >> (d & 63)) & 1; }
static void mark(State *s, int d) { s->used[d >> 6] |= 1ULL << (d & 63); }
static void unmark(State *s, int d) { s->used[d >> 6] &= ~(1ULL << (d & 63)); }

static int adjacent(const State *s, int u, int v) {
    return s->is_shared[u] || s->is_shared[v] || s->copy[u] == s->copy[v];
}

/* The candidate vertices for a new label, one per symmetry class.  A
   candidate is a copy index, or -1 for a shared vertex. */
static int candidates(const State *s, int *copies) {
    int count = 0;
    if (s->shared_used < R) copies[count++] = -1;
    for (int g = 0; g < s->copies_used; g++)
        if (s->copy_size[g] < N - R) copies[count++] = g;
    if (s->copies_used < T) copies[count++] = s->copies_used;
    return count;
}

/* Create a new vertex (shared if c == -1, else in copy c) on label x.
   Returns 1 and updates the state, or returns 0 (state unchanged) if one of
   its differences is already realized. */
static int place(State *s, int x, int c) {
    int v = s->vertices;
    s->is_shared[v] = c < 0; s->copy[v] = c;
    int created[MAX_VERTICES], count = 0;
    for (int w = 0; w < v; w++) {
        if (!adjacent(s, v, w)) continue;
        int d = abs(s->label[w] - x);
        if (is_used(s, d)) {                         /* d > 0: labels are distinct */
            while (count > 0) unmark(s, created[--count]);
            return 0;
        }
        mark(s, d); created[count++] = d;
    }
    s->label[v] = x; s->vertex_on[x] = v; s->vertices++;
    if (c < 0) s->shared_used++;
    else if (s->copy_size[c]++ == 0) s->copies_used++;
    return 1;
}

/* Undo the most recent place() (calls are strictly nested). */
static void unplace(State *s) {
    int v = --s->vertices;
    for (int w = 0; w < v; w++)
        if (adjacent(s, v, w)) unmark(s, abs(s->label[w] - s->label[v]));
    s->vertex_on[s->label[v]] = -1;
    if (s->is_shared[v]) s->shared_used--;
    else if (--s->copy_size[s->copy[v]] == 0) s->copies_used--;
}

/* The unrealized difference with the fewest open pairs.  Returns it, or 0 if
   every difference is realized, or -1 if some difference has no open pair. */
static int next_difference(const State *s) {
    int best = 0, fewest = 1 << 30;
    for (int d = M; d >= 1; d--) {
        if (is_used(s, d)) continue;
        int open = 0;
        for (int x = 0; x + d <= M; x++)
            if (s->vertex_on[x] < 0 || s->vertex_on[x + d] < 0) open++;
        if (open == 0) return -1;
        if (open < fewest) { fewest = open; best = d; if (open == 1) break; }
    }
    return best;
}

/* --------------------------------------------------------------- search */

static State *subtrees;
static int subtree_count, subtree_capacity, split_depth = 8, too_many_subtrees;
static int found;                       /* set by the thread that finds one */
static State answer;

static int labeling_was_found(void) {
    int value;
    #pragma omp atomic read
    value = found;
    return value;
}

/* Save a state at the split depth (the first phase runs on one thread).  If
   there are too many, give up; run() then retries with a smaller depth. */
static void save_subtree(const State *s) {
    if (subtree_count == MAX_SUBTREES) { too_many_subtrees = 1; return; }
    if (subtree_count == subtree_capacity) {
        subtree_capacity = subtree_capacity ? 2 * subtree_capacity : 1024;
        subtrees = realloc(subtrees, sizeof(State) * subtree_capacity);
        if (!subtrees) { fprintf(stderr, "out of memory\n"); exit(1); }
    }
    subtrees[subtree_count++] = *s;
}

static int search(State *s, int depth, int collecting);

/* Realize difference y - x by an edge between labels x and y: place new
   vertices on whichever of the two labels are free (at least one is), in
   every candidate way, keep the ways in which the two vertices are adjacent,
   and search on.  Returns 1 if a graceful labeling was found. */
static int realize(State *s, int x, int y, int depth, int collecting) {
    int u = s->vertex_on[x], w = s->vertex_on[y];
    if (u >= 0 && w >= 0) return adjacent(s, u, w) && search(s, depth + 1, collecting);
    int free_label = u < 0 ? x : y, options[MAX_VERTICES];
    int count = candidates(s, options);
    for (int i = 0; i < count; i++) {
        if (!place(s, free_label, options[i])) continue;
        if (realize(s, x, y, depth, collecting)) return 1;
        unplace(s);
    }
    return 0;
}

/* Returns 1 if a graceful labeling was found (it is stored in `answer`). */
static int search(State *s, int depth, int collecting) {
    s->nodes++;
    if (labeling_was_found()) return 1;
    if (too_many_subtrees) return 0;
    int d = next_difference(s);
    if (d < 0) return 0;
    if (d == 0) {
        #pragma omp critical
        if (!labeling_was_found()) {
            answer = *s;
            #pragma omp atomic write
            found = 1;
        }
        return 1;
    }
    if (collecting && depth == split_depth) {
        s->nodes--;                     /* counted when the subtree is searched */
        save_subtree(s);
        return 0;
    }
    for (int x = 0; x + d <= M; x++) {
        if (s->vertex_on[x] >= 0 && s->vertex_on[x + d] >= 0) continue;   /* closed pair */
        if (realize(s, x, x + d, depth, collecting)) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: complete_search n r t [split] [threads]\n"); return 1; }
    N = atoi(argv[1]); R = atoi(argv[2]); T = atoi(argv[3]);
    if (argc > 4) split_depth = atoi(argv[4]);
    if (argc > 5) omp_set_num_threads(atoi(argv[5]));
    M = R * (R - 1) / 2 + T * (N * (N - 1) / 2 - R * (R - 1) / 2);
    if (R < 1 || N <= R || T < 1 || M > MAX_M || R + T * (N - R) > MAX_VERTICES) {
        fprintf(stderr, "need 1 <= r < n, t >= 1, at most %d edges and %d vertices\n", MAX_M, MAX_VERTICES);
        return 1;
    }

    State *root = malloc(sizeof(State));
    double start = omp_get_wtime();
    for (;;) {                          /* first phase: expand to the split depth */
        memset(root, 0, sizeof *root);
        memset(root->vertex_on, -1, sizeof root->vertex_on);
        subtree_count = too_many_subtrees = 0;
        if (search(root, 0, 1) || !too_many_subtrees) break;
        split_depth--;
    }
    long long nodes = root->nodes;
    if (!found) {
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:nodes)
        for (int i = 0; i < subtree_count; i++) {
            if (labeling_was_found()) continue;
            State *s = malloc(sizeof(State));
            *s = subtrees[i];
            s->nodes = 0;
            search(s, split_depth, 0);
            nodes += s->nodes;
            free(s);
        }
    }

    printf("B(%d,%d,%d) m=%d: ", N, R, T, M);
    if (found) {
        printf("graceful; shared:");
        for (int v = 0; v < answer.vertices; v++) if (answer.is_shared[v]) printf(" %d", answer.label[v]);
        for (int g = 0; g < T; g++) {
            printf(" | copy %d:", g);
            for (int v = 0; v < answer.vertices; v++)
                if (!answer.is_shared[v] && answer.copy[v] == g) printf(" %d", answer.label[v]);
        }
    } else printf("not graceful");
    printf("  [nodes %lld, %.0fs]\n", nodes, omp_get_wtime() - start);
    return 0;
}
