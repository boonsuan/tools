// Search for residue maps of complete multipartite graphs (Section 3.5).
//
// This program is how the archived maps in ../data/residue_witnesses.json
// were FOUND.  Nothing in the paper depends on trusting it: every archived
// map is checked exactly by sec3_parity.py.  It is included so that readers
// can reproduce or extend the search.
//
// The problem.  Let G = K_{parts} have n vertices and m edges, and fix q.
// We want residues r(v) in Z/q, one per vertex, such that for every class d
// the number of edges uv with r(u) - r(v) = +-d (mod q) equals the number
// of integers k in [1, m] with k = +-d (mod q).  Here "the class of d" is
// min(d, q - d), so that both signs are counted together; for an edge this is
// the same as counting both ordered pairs (u, v) and (v, u), which is how the
// paper states the residue equations.
//
// The method is simulated annealing on the squared error between observed and
// required class counts.  Vertex 0 is fixed at residue 0 (translation
// invariance).  Capacities are not imposed here; archive_residue_witnesses.py
// translates each solution until the capacities hold.
//
// Output: one line per solved (parts, q), in the form
//     3,3,3, 5 0 1 4 ...
// i.e. the part sizes, the modulus, then the residues of the vertices listed
// part by part.  Failures are reported on stderr.
//
// Build and run (see ../README.md):
//     g++ -O2 -o residue_search discovery/find_residue_witnesses.cpp
//     ./residue_search > search_output.txt

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>

using std::vector;

int main() {
    std::mt19937 rng(20261018);
    const vector<vector<int>> families = {{3, 3, 3}, {2, 2, 2, 2, 2}, {4, 4, 4}, {3, 4, 5}};
    const int restarts = 1000, steps = 20000;

    for (const vector<int>& parts : families) {
        for (int q = 2; q <= 12; q++) {
            // Vertices are numbered part by part; part_of[v] is v's part.
            vector<int> part_of;
            for (int i = 0; i < (int)parts.size(); i++)
                for (int k = 0; k < parts[i]; k++) part_of.push_back(i);
            const int n = part_of.size();

            // Edges join vertices in different parts.
            vector<vector<int>> neighbours(n);
            int m = 0;
            for (int u = 0; u < n; u++)
                for (int v = u + 1; v < n; v++)
                    if (part_of[u] != part_of[v]) {
                        neighbours[u].push_back(v);
                        neighbours[v].push_back(u);
                        m++;
                    }

            auto difference_class = [q](int x, int y) {
                int a = std::abs(x - y);
                return std::min(a, q - a);
            };
            auto error = [](const vector<int>& count, const vector<int>& target) {
                int total = 0;
                for (size_t c = 0; c < count.size(); c++)
                    total += (count[c] - target[c]) * (count[c] - target[c]);
                return total;
            };

            // Required counts: how many of 1, ..., m fall in each class.
            vector<int> target(q / 2 + 1, 0);
            for (int k = 1; k <= m; k++) target[std::min(k % q, q - k % q)]++;

            bool solved = false;
            int best = 1 << 30;
            for (int restart = 0; restart < restarts && !solved; restart++) {
                vector<int> residue(n, 0), count(q / 2 + 1, 0);
                for (int v = 1; v < n; v++) residue[v] = rng() % q;
                for (int u = 0; u < n; u++)
                    for (int v : neighbours[u])
                        if (u < v) count[difference_class(residue[u], residue[v])]++;
                int score = error(count, target);

                for (int step = 0; step < steps; step++) {
                    if (score == 0) {
                        for (int s : parts) std::cout << s << ',';
                        std::cout << ' ' << q;
                        for (int x : residue) std::cout << ' ' << x;
                        std::cout << '\n';
                        solved = true;
                        break;
                    }
                    // Propose moving one vertex (not vertex 0) to a new residue.
                    int v = 1 + rng() % (n - 1), from = residue[v], to = rng() % q;
                    if (to == from) continue;
                    vector<int> proposal = count;
                    for (int u : neighbours[v]) {
                        proposal[difference_class(from, residue[u])]--;
                        proposal[difference_class(to, residue[u])]++;
                    }
                    int new_score = error(proposal, target);
                    double temperature = 0.2 + 3.0 * (steps - step) / steps;
                    double coin = std::generate_canonical<double, 53>(rng);
                    if (new_score <= score || coin < std::exp((score - new_score) / temperature)) {
                        residue[v] = to;
                        count = proposal;
                        score = new_score;
                    }
                    best = std::min(best, score);
                }
            }
            if (!solved) {
                std::cerr << "FAILED q=" << q << " parts=";
                for (int s : parts) std::cerr << s << ',';
                std::cerr << " best error " << best << '\n';
            }
        }
    }
}
