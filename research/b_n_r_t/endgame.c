/*
 * endgame.c -- the end-game search: a finite computation that proves a whole
 * family of graphs ungraceful.
 *
 * THE IDEA
 * In a graceful labeling of a graph with m edges, the edge whose difference is
 * m - j joins two labels a and a + (m - j), both in [0, m], so a <= j and the
 * other label is m - (j - a).  Hence the largest differences m, m-1, ..., m-L
 * are realized only by edges between the LOW labels 0..L and the HIGH labels
 * m-L..m.  When m >= 2L + 1 these two ranges are disjoint, and nothing in the
 * search below depends on m.
 *
 * We try to place vertices on low and high labels so that every difference
 * m - j, 0 <= j <= L, is realized by exactly one edge, while all realized
 * differences stay distinct.  If every attempt fails, then no graph of the
 * family with m >= 2L + 1 edges is graceful.  (The results are stated for
 * m >= 2L + 2, slightly more than needed.)
 *
 * NOTATION USED IN THE CODE
 *   low label a          the label a           (0 <= a <= L)
 *   high label k         the label m - k       (0 <= k <= L)
 *   cross difference     between low a and high k: m - (a + k), recorded as the
 *                        "sum" a + k (0 .. 2L); each sum may occur at most once
 *   inner difference     between two low labels or two high labels: |a - a'|
 *                        (1 .. L); each may occur at most once
 * The search keeps these two pools separately.  If some cross difference
 * happened to equal some inner difference (possible only when m <= 3L) the
 * search could miss that conflict; it never reports a conflict that is not
 * real.  So a failed search is a valid proof.
 *
 * WHICH DIFFERENCE TO REALIZE NEXT
 * Each difference m - j still to be realized has j + 1 "splits" (a, k) with
 * a + k = j.  A split is closed when both labels already carry vertices (and
 * then, since m - j is not yet realized, those vertices are not adjacent).
 * We always work on the difference with the fewest open splits; if some
 * difference has none, the branch is dead.  Any order is valid: every one of
 * these differences must be realized in a graceful labeling.
 *
 * FAMILIES AND SYMMETRY
 * Vertices are created only when a label needs one.  A vertex is described by
 * a (type, group) pair, and adjacency depends only on these:
 *
 *   B r t     B(n, r, t): t copies of K_n sharing a K_r, with n arbitrary.
 *             type 0 = a shared vertex, type 1 = a vertex of copy `group`.
 *             Shared vertices are adjacent to everything; two copy vertices
 *             are adjacent iff they are in the same copy.
 *   kp R      K_n box P_R (Knuth's KP graphs), n arbitrary.
 *             type = column 0..R-1, group = row.  Same column: adjacent;
 *             same row and neighbouring columns: adjacent.
 *
 * A new vertex can be any vertex not yet used.  Vertices that are
 * interchangeable by an automorphism of the graph give identical subtrees, so
 * we offer one representative of each kind:
 *   B: one more shared vertex (if fewer than r are used); one more vertex of
 *      each copy already used; and one vertex of a new copy (copies are
 *      interchangeable, so the new copy is the next unused index).
 *   kp: for each column, a vertex in each row that already has vertices but
 *      not in that column, and a vertex in one new row (rows are
 *      interchangeable).  The reflection of the path swaps columns c and
 *      R-1-c, so the very first vertex (on label 0) may be taken in the left
 *      half.
 * n never appears: a copy (or a column) may receive as many vertices as the
 * search wants.  For a particular n this only offers MORE options than
 * really exist, so a search that fails for "n arbitrary" fails for every n.
 *
 * PARALLELISM
 * The tree is expanded sequentially to a fixed depth (default 7); the subtrees
 * below are then searched independently by several threads (OpenMP).  If
 * there are more than MAX_SUBTREES of them, the depth is reduced.
 *
 * USAGE
 *   endgame L B r t [split] [threads]      search with depth L
 *   endgame scan L0 B r t [split] [threads] smallest L >= L0 at which the
 *                                           search fails (prints each L tried)
 *   (and the same with "kp R" in place of "B r t")
 * Output: "no branch survives" (a proof for m >= 2L + 2) or "survives".
 *
 * Build: gcc -O3 -march=native -fopenmp -o endgame endgame.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>

#define MAX_L 127                       /* bitmasks below hold labels 0..127 */
#define MAX_VERTICES 260
#define MAX_CANDIDATES 512             /* candidates for one new vertex */
#define MAX_SUBTREES (1 << 14)        /* states saved for the parallel phase */

typedef unsigned __int128 u128;

/* ------------------------------------------------------------------ family */

enum { FAMILY_B, FAMILY_KP };
static int family;
static int R;                 /* B: size of the shared clique; kp: number of columns */
static int T;                 /* B: number of copies */
static int L;                 /* depth: differences m, m-1, ..., m-L */

/* -------------------------------------------------------------- the state */

typedef struct {
    /* labels: vertex index, or -1 if the label is not (yet) used */
    int low[MAX_L + 1];                 /* low[a]: vertex with label a */
    int high[MAX_L + 1];                /* high[k]: vertex with label m - k */

    /* vertices, in the order they were created */
    int type[MAX_VERTICES], group[MAX_VERTICES];
    int is_high[MAX_VERTICES], position[MAX_VERTICES];   /* its label: low a or high k */
    int vertices;

    /* realized differences */
    u128 inner_used;                    /* bit d: inner difference d is realized */
    uint64_t sum_used[4];               /* bit s: cross difference m - s is realized */

    /* bitmasks of used labels, for counting closed splits quickly */
    u128 low_mask;                      /* bit a: low label a used */
    u128 high_mask_reversed;            /* bit L-k: high label k used */

    /* counters describing which vertices exist (for the candidate lists) */
    int shared_used;                    /* B: shared vertices used */
    int copy_size[MAX_VERTICES];        /* B: vertices used in each copy */
    int copies_used;                    /* B: copies 0..copies_used-1 are in use */
    uint32_t row_columns[MAX_VERTICES]; /* kp: bitmask of columns used in each row */
    int rows_used;                      /* kp: rows 0..rows_used-1 are in use */

    long long nodes;
} State;

static int sum_is_used(const State *s, int sum) { return (s->sum_used[sum >> 6] >> (sum & 63)) & 1; }

static int adjacent(const State *s, int u, int v) {
    if (family == FAMILY_B) {
        if (s->type[u] == 0 || s->type[v] == 0) return 1;        /* shared vertex */
        return s->group[u] == s->group[v];                       /* same copy */
    }
    if (s->type[u] == s->type[v]) return s->group[u] != s->group[v];   /* same column */
    return s->group[u] == s->group[v] && abs(s->type[u] - s->type[v]) == 1;   /* same row, next column */
}

/* The candidate vertices for a label that is not yet used, one per symmetry
   class (see the header).  Each candidate is a (type, group) pair. */
static int candidates(const State *s, int *types, int *groups) {
    int count = 0;
    if (family == FAMILY_B) {
        if (s->shared_used < R) { types[count] = 0; groups[count] = -1; count++; }
        for (int g = 0; g < s->copies_used && g < T; g++) { types[count] = 1; groups[count] = g; count++; }
        if (s->copies_used < T) { types[count] = 1; groups[count] = s->copies_used; count++; }
    } else {
        for (int column = 0; column < R; column++) {
            if (s->vertices == 0 && column > (R - 1) / 2) continue;      /* reflection */
            for (int row = 0; row <= s->rows_used; row++)                /* existing rows and one new row */
                if (!((s->row_columns[row] >> column) & 1)) {
                    if (count == MAX_CANDIDATES) { fprintf(stderr, "too many candidates\n"); exit(1); }
                    types[count] = column; groups[count] = row; count++;
                }
        }
    }
    return count;
}

/* Create a new vertex (type, group) on a label.  Returns 1 and updates the
   state, or returns 0 (state unchanged) if some difference would repeat. */
static int place(State *s, int is_high, int position, int type, int group) {
    int v = s->vertices;
    s->type[v] = type; s->group[v] = group;
    u128 new_inner = 0;
    uint64_t new_sums[4] = {0, 0, 0, 0};
    for (int w = 0; w < v; w++) {
        if (!adjacent(s, v, w)) continue;
        if (is_high == s->is_high[w]) {                          /* inner difference */
            int d = abs(position - s->position[w]);
            u128 bit = (u128)1 << d;
            if (d == 0 || (s->inner_used & bit) || (new_inner & bit)) return 0;
            new_inner |= bit;
        } else {                                                 /* cross difference m - sum */
            int sum = position + s->position[w];
            if (sum_is_used(s, sum) || ((new_sums[sum >> 6] >> (sum & 63)) & 1)) return 0;
            new_sums[sum >> 6] |= 1ULL << (sum & 63);
        }
    }
    s->inner_used |= new_inner;
    for (int i = 0; i < 4; i++) s->sum_used[i] |= new_sums[i];
    s->is_high[v] = is_high; s->position[v] = position; s->vertices++;
    if (is_high) { s->high[position] = v; s->high_mask_reversed |= (u128)1 << (L - position); }
    else { s->low[position] = v; s->low_mask |= (u128)1 << position; }
    if (family == FAMILY_B) {
        if (type == 0) s->shared_used++;
        else if (s->copy_size[group]++ == 0) s->copies_used++;   /* a new copy is always the next index */
    } else {
        if (s->row_columns[group] == 0) s->rows_used++;          /* likewise for rows */
        s->row_columns[group] |= 1u << type;
    }
    return 1;
}

/* Undo the most recent place() (calls are strictly nested). */
static void unplace(State *s) {
    int v = --s->vertices;
    for (int w = 0; w < v; w++) {
        if (!adjacent(s, v, w)) continue;
        if (s->is_high[v] == s->is_high[w]) s->inner_used &= ~((u128)1 << abs(s->position[v] - s->position[w]));
        else { int sum = s->position[v] + s->position[w]; s->sum_used[sum >> 6] &= ~(1ULL << (sum & 63)); }
    }
    if (s->is_high[v]) { s->high[s->position[v]] = -1; s->high_mask_reversed &= ~((u128)1 << (L - s->position[v])); }
    else { s->low[s->position[v]] = -1; s->low_mask &= ~((u128)1 << s->position[v]); }
    if (family == FAMILY_B) {
        if (s->type[v] == 0) s->shared_used--;
        else if (--s->copy_size[s->group[v]] == 0) s->copies_used--;
    } else {
        s->row_columns[s->group[v]] &= ~(1u << s->type[v]);
        if (s->row_columns[s->group[v]] == 0) s->rows_used--;
    }
}

static int popcount128(u128 x) { return __builtin_popcountll((uint64_t)x) + __builtin_popcountll((uint64_t)(x >> 64)); }

/* The difference m - j to realize next: the one with fewest open splits.
   Returns j, or -1 if all are realized (the branch survives), or -2 if some
   difference has no open split (the branch is dead).  The split (a, j - a)
   is closed iff low a and high j - a are both used: bit a of low_mask and bit
   L - (j - a) of high_mask_reversed, i.e. bit a of (high_mask_reversed >> (L - j)). */
static int next_difference(const State *s) {
    int best = -1, fewest = 1 << 30;
    for (int j = 0; j <= L; j++) {
        if (sum_is_used(s, j)) continue;
        u128 window = j >= 127 ? ~(u128)0 : (((u128)1 << (j + 1)) - 1);
        int closed = popcount128(s->low_mask & (s->high_mask_reversed >> (L - j)) & window);
        int open = j + 1 - closed;
        if (open == 0) return -2;
        if (open < fewest) { fewest = open; best = j; if (open == 1) break; }
    }
    return best;
}

/* --------------------------------------------------------------- search */

static State *subtrees;                 /* states saved at the split depth */
static int subtree_count, subtree_capacity, split_depth, too_many_subtrees;
static int survivor_found;              /* set by the thread that finds one */

static int survivor_was_found(void) {
    int value;
    #pragma omp atomic read
    value = survivor_found;
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

/* Realize difference m - (a + k) by an edge between low label a and high
   label k: place new vertices on whichever of the two labels are free (at
   least one is), in every candidate way, keep the ways in which the two
   vertices are adjacent, and search on.  Returns 1 if a branch survives. */
static int realize(State *s, int a, int k, int depth, int collecting) {
    int u = s->low[a], w = s->high[k];
    if (u >= 0 && w >= 0) return adjacent(s, u, w) && search(s, depth + 1, collecting);
    int types[MAX_CANDIDATES], groups[MAX_CANDIDATES];
    int count = candidates(s, types, groups);
    for (int i = 0; i < count; i++) {
        if (u < 0 ? !place(s, 0, a, types[i], groups[i]) : !place(s, 1, k, types[i], groups[i])) continue;
        if (realize(s, a, k, depth, collecting)) return 1;
        unplace(s);
    }
    return 0;
}

/* Returns 1 if some branch below survives (realizes every difference). */
static int search(State *s, int depth, int collecting) {
    s->nodes++;
    if (survivor_was_found()) return 1;
    if (too_many_subtrees) return 0;
    int j = next_difference(s);
    if (j == -2) return 0;
    if (j == -1) return 1;
    if (collecting && depth == split_depth) {
        s->nodes--;                     /* counted when the subtree is searched */
        save_subtree(s);
        return 0;
    }
    for (int a = 0; a <= j; a++) {      /* realize m - j by low a and high j - a */
        if (s->low[a] >= 0 && s->high[j - a] >= 0) continue;   /* closed split */
        if (realize(s, a, j - a, depth, collecting)) return 1;
    }
    return 0;
}

static void empty_state(State *s) {
    memset(s, 0, sizeof *s);
    memset(s->low, -1, sizeof s->low);
    memset(s->high, -1, sizeof s->high);
}

/* One search with the current L.  Returns 1 if a branch survives. */
static int run(long long *nodes) {
    State *root = malloc(sizeof(State));
    int survives;
    for (;;) {                          /* first phase: expand to the split depth */
        empty_state(root);
        subtree_count = too_many_subtrees = survivor_found = 0;
        survives = search(root, 0, 1);
        if (survives || !too_many_subtrees) break;
        split_depth--;
    }
    long long total = root->nodes;
    if (!survives) {
        #pragma omp parallel for schedule(dynamic, 1) reduction(+:total)
        for (int i = 0; i < subtree_count; i++) {
            if (survivor_was_found()) continue;
            State *s = malloc(sizeof(State));
            *s = subtrees[i];
            s->nodes = 0;
            if (search(s, split_depth, 0)) {
                #pragma omp atomic write
                survivor_found = 1;
            }
            total += s->nodes;
            free(s);
        }
        survives = survivor_found;
    }
    free(root);
    *nodes = total;
    return survives;
}

static void usage(void) {
    fprintf(stderr, "usage: endgame L B r t [split] [threads]\n"
                    "       endgame L kp R [split] [threads]\n"
                    "       endgame scan L0 (B r t | kp R) [split] [threads]\n");
    exit(1);
}

int main(int argc, char **argv) {
    if (argc < 2) usage();
    int scan = strcmp(argv[1], "scan") == 0, arg = 1 + scan;
    if (argc < arg + 3) usage();
    L = atoi(argv[arg++]);
    if (strcmp(argv[arg], "B") == 0 && argc >= arg + 3) {
        family = FAMILY_B; R = atoi(argv[arg + 1]); T = atoi(argv[arg + 2]); arg += 3;
    } else if (strcmp(argv[arg], "kp") == 0) {
        family = FAMILY_KP; R = atoi(argv[arg + 1]); arg += 2;
    } else usage();
    split_depth = argc > arg ? atoi(argv[arg]) : 7;
    if (argc > arg + 1) omp_set_num_threads(atoi(argv[arg + 1]));
    if (L < 0 || L > MAX_L) { fprintf(stderr, "L must be between 0 and %d\n", MAX_L); return 1; }
    if (family == FAMILY_B && (R < 0 || T < 1 || T > MAX_CANDIDATES - 2)) {
        fprintf(stderr, "B r t needs r >= 0 and 1 <= t <= %d\n", MAX_CANDIDATES - 2); return 1;
    }
    if (family == FAMILY_KP && (R < 1 || R > 32)) { fprintf(stderr, "kp R needs 1 <= R <= 32\n"); return 1; }
    for (;;) {
        long long nodes;
        double start = omp_get_wtime();
        int survives = run(&nodes);
        printf("L=%d: %s (nodes %lld, %.1fs)\n", L,
               survives ? "survives" : "no branch survives", nodes, omp_get_wtime() - start);
        fflush(stdout);
        if (!scan || !survives || L == MAX_L) break;
        L++;
    }
    return 0;
}
