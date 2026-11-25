#include <Accelerate/Accelerate.h>
#include <algorithm>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <mutex>
#include <numeric>
#include <random>
#include <string>
#include <thread>
#include <vector>

// Fast multi-threaded Simulated Annealing + Structured Family search
// for ALL 13 open spectral graph conjectures in arXiv:2611.03879v1 (Cazenave, Nov 2026).

struct Graph {
    int n;
    std::vector<uint8_t> adj; // n*n symmetric 0/1
    std::vector<int> deg;
    int m = 0;

    explicit Graph(int n_) : n(n_), adj(n_ * n_, 0), deg(n_, 0), m(0) {}

    inline bool has_edge(int u, int v) const { return adj[u * n + v] != 0; }

    inline void add_edge(int u, int v) {
        if (u == v || adj[u * n + v]) return;
        adj[u * n + v] = adj[v * n + u] = 1;
        deg[u]++; deg[v]++;
        m++;
    }

    inline void rem_edge(int u, int v) {
        if (u == v || !adj[u * n + v]) return;
        adj[u * n + v] = adj[v * n + u] = 0;
        deg[u]--; deg[v]--;
        m--;
    }

    bool is_connected() const {
        std::vector<uint8_t> vis(n, 0);
        std::vector<int> q;
        q.reserve(n);
        q.push_back(0);
        vis[0] = 1;
        for (size_t head = 0; head < q.size(); ++head) {
            int u = q[head];
            const uint8_t* row = &adj[u * n];
            for (int v = 0; v < n; ++v) {
                if (row[v] && !vis[v]) {
                    vis[v] = 1;
                    q.push_back(v);
                }
            }
        }
        return (int)q.size() == n;
    }
};

struct Invariants {
    int n, m, rk, rad;
    double R, l1, l2, mu1, mu2;
};

struct Workspace {
    std::vector<double> A, L, eA, eL, work;
    std::vector<int> dist, q;
    explicit Workspace(int maxn)
        : A(maxn * maxn), L(maxn * maxn), eA(maxn), eL(maxn),
          work(std::max(1, 6 * maxn)), dist(maxn), q(maxn) {}
};

static Invariants compute_invariants(const Graph& g, Workspace& ws, bool need_rad) {
    int n = g.n;
    double R = 0.0;
    for (int i = 0; i < n; ++i) {
        ws.L[i * n + i] = (double)g.deg[i];
        ws.A[i * n + i] = 0.0;
        for (int j = i + 1; j < n; ++j) {
            if (g.adj[i * n + j]) {
                ws.A[i * n + j] = ws.A[j * n + i] = 1.0;
                ws.L[i * n + j] = ws.L[j * n + i] = -1.0;
                R += 1.0 / std::sqrt((double)g.deg[i] * (double)g.deg[j]);
            } else {
                ws.A[i * n + j] = ws.A[j * n + i] = 0.0;
                ws.L[i * n + j] = ws.L[j * n + i] = 0.0;
            }
        }
    }

    char jobz = 'N', uplo = 'U';
    __LAPACK_int N = n, lda = n, lwork = (int)ws.work.size(), info = 0;
    dsyev_(&jobz, &uplo, &N, ws.A.data(), &lda, ws.eA.data(), ws.work.data(), &lwork, &info);
    dsyev_(&jobz, &uplo, &N, ws.L.data(), &lda, ws.eL.data(), ws.work.data(), &lwork, &info);

    int rk = 0;
    for (int i = 0; i < n; ++i) {
        if (std::fabs(ws.eA[i]) > 1e-7) rk++;
    }

    int rad = 0;
    if (need_rad) {
        rad = n;
        for (int s = 0; s < n; ++s) {
            std::fill(ws.dist.begin(), ws.dist.begin() + n, -1);
            ws.dist[s] = 0;
            int head = 0, tail = 0;
            ws.q[tail++] = s;
            int ecc = 0;
            while (head < tail) {
                int u = ws.q[head++];
                int du = ws.dist[u];
                if (du > ecc) ecc = du;
                const uint8_t* row = &g.adj[u * n];
                for (int v = 0; v < n; ++v) {
                    if (row[v] && ws.dist[v] == -1) {
                        ws.dist[v] = du + 1;
                        ws.q[tail++] = v;
                    }
                }
            }
            if (ecc < rad) rad = ecc;
        }
    }

    return {n, g.m, rk, rad, R, ws.eA[n - 1], ws.eA[n - 2], ws.eL[n - 1], ws.eL[n - 2]};
}

enum ConjId {
    C1 = 0, C1_S1, C1_S2, C2, C3, C4, C5, C6_1, C6_2, C6_3, C6_4A, C6_4B, C7, NUM_CONJ
};

static const char* CONJ_NAMES[NUM_CONJ] = {
    "C1", "C1_s1", "C1_s2", "C2", "C3", "C4", "C5",
    "C6_1", "C6_2", "C6_3", "C6_4a", "C6_4b", "C7"
};

static inline double margin(int cid, const Invariants& inv) {
    switch (cid) {
        case C1:    return inv.R - (inv.l2 + 1.0);
        case C1_S1: return (double)inv.m - inv.l1 * (inv.l2 + 1.0);
        case C1_S2: return 2.0 * inv.m - (inv.l1 * inv.l1 + (inv.l2 + 1.0) * (inv.l2 + 1.0));
        case C2:    return (inv.mu1 - 2.0) - inv.l2;
        case C3:    return (double)inv.rk * inv.l1 - 2.0 * inv.R;
        case C4:    return (inv.R + inv.mu2) - inv.l1;
        case C5:    return 2.0 * inv.m - (inv.mu2 + (double)inv.rk);
        case C6_1:  return inv.R * inv.R - 0.5 * (inv.m + 1.0);
        case C6_2:  return inv.mu2 * inv.mu2 - (4.0 * inv.l2 + 1.0);
        case C6_3:  return inv.mu1 * inv.mu1 - (4.0 * inv.l2 + 8.0);
        case C6_4A: return inv.R - ((2.0 / 3.0) * std::sqrt((double)inv.m) + 1.0 / 3.0);
        case C6_4B: return inv.R - (1.5 * std::sqrt((double)inv.rk) + 1.0 - 1.5 * std::sqrt(2.0));
        case C7:    return inv.R - ((double)inv.rad + std::sqrt(2.0) - 1.5);
        default:    return 1e9;
    }
}

static Graph make_init_graph(int n, int kind, std::mt19937_64& rng) {
    Graph g(n);
    if (kind == 0) {
        // Random connected spanning tree + random edges
        for (int i = 1; i < n; ++i) g.add_edge(i, (int)(rng() % i));
        double p = 0.05 + 0.85 * ((double)(rng() % 1000) / 1000.0);
        for (int i = 0; i < n; ++i)
            for (int j = i + 1; j < n; ++j)
                if ((double)(rng() % 10000) / 10000.0 < p) g.add_edge(i, j);
    } else if (kind == 1) {
        // Two cliques joined by a few edges or a path
        int a = std::max(2, n / 2 + (int)(rng() % 5) - 2);
        if (a >= n - 1) a = n / 2;
        for (int i = 0; i < a; ++i)
            for (int j = i + 1; j < a; ++j) g.add_edge(i, j);
        for (int i = a; i < n; ++i)
            for (int j = i + 1; j < n; ++j) g.add_edge(i, j);
        int bridges = 1 + (int)(rng() % 4);
        for (int b = 0; b < bridges; ++b)
            g.add_edge((int)(rng() % a), a + (int)(rng() % (n - a)));
    } else if (kind == 2) {
        // Complete split / windmill / clique + independent set / pineapple
        int a = 2 + (int)(rng() % (n - 2));
        for (int i = 0; i < a; ++i)
            for (int j = i + 1; j < a; ++j) g.add_edge(i, j);
        int mode = rng() % 3;
        for (int i = a; i < n; ++i) {
            if (mode == 0) {
                for (int j = 0; j < a; ++j) g.add_edge(i, j);
            } else if (mode == 1) {
                g.add_edge(i, (int)(rng() % a));
            } else {
                int d = 1 + (int)(rng() % a);
                for (int k = 0; k < d; ++k) g.add_edge(i, (int)(rng() % a));
            }
        }
    } else {
        // Sparse / tree / broom / spider + small cycles
        int spine = 2 + (int)(rng() % (n - 1));
        for (int i = 1; i < spine; ++i) g.add_edge(i - 1, i);
        for (int i = spine; i < n; ++i) g.add_edge(i, (int)(rng() % spine));
        int extra = rng() % (n / 2 + 1);
        for (int e = 0; e < extra; ++e) g.add_edge((int)(rng() % n), (int)(rng() % n));
    }
    return g;
}

static void save_witness(const std::string& path, const char* cname, const Graph& g, double val) {
    std::ofstream out(path);
    out << "{\n  \"conjecture\": \"" << cname << "\",\n  \"n\": " << g.n
        << ",\n  \"m\": " << g.m << ",\n  \"margin_float64\": " << std::setprecision(15) << val
        << ",\n  \"edges\": [";
    bool first = true;
    for (int i = 0; i < g.n; ++i) {
        for (int j = i + 1; j < g.n; ++j) {
            if (g.has_edge(i, j)) {
                if (!first) out << ", ";
                out << "[" << i << "," << j << "]";
                first = false;
            }
        }
    }
    out << "]\n}\n";
}

int main() {
    std::mutex io_mtx;
    std::vector<double> global_best(NUM_CONJ, 1e9);
    std::vector<int> global_best_n(NUM_CONJ, 0);
    std::vector<int> global_best_m(NUM_CONJ, 0);

    // One thread per conjecture! All 13 conjectures searched in parallel on 13 of 14 cores!
    std::vector<std::thread> threads;
    for (int cid = 0; cid < NUM_CONJ; ++cid) {
        threads.emplace_back([&, cid]() {
            std::mt19937_64 rng(20261124ULL * 1000ULL + cid * 97ULL);
            bool need_rad = (cid == C7);
            std::vector<int> sizes = {11, 13, 16, 20, 25, 32, 42, 55};
            Workspace ws(60);

            double best_val = 1e9;
            Graph best_g(2);

            for (int n : sizes) {
                int restarts = (n <= 20) ? 40 : ((n <= 32) ? 24 : 10);
                int steps = (n <= 20) ? 2500 : ((n <= 32) ? 1500 : 800);

                for (int r = 0; r < restarts; ++r) {
                    Graph g = make_init_graph(n, r % 4, rng);
                    if (!g.is_connected()) continue;
                    Invariants cur_inv = compute_invariants(g, ws, need_rad);
                    double cur_val = margin(cid, cur_inv);

                    if (cur_val < best_val) {
                        best_val = cur_val;
                        best_g = g;
                    }

                    double T0 = std::max(0.05, std::fabs(cur_val) * 0.15 + 0.05);
                    double T1 = 1e-4;
                    for (int st = 0; st < steps; ++st) {
                        double frac = (double)st / (double)steps;
                        double T = T0 * std::pow(T1 / T0, frac);

                        // Move: single edge toggle (80%) or edge swap / 2-edge toggle (20%)
                        int move_type = rng() % 10;
                        int u1 = rng() % n, v1 = rng() % n;
                        while (v1 == u1) v1 = rng() % n;
                        bool had1 = g.has_edge(u1, v1);
                        int u2 = -1, v2 = -1;
                        bool had2 = false;

                        if (had1) g.rem_edge(u1, v1);
                        else g.add_edge(u1, v1);

                        if (move_type >= 8) {
                            u2 = rng() % n; v2 = rng() % n;
                            while (v2 == u2 || (u2 == u1 && v2 == v1) || (u2 == v1 && v2 == u1)) {
                                u2 = rng() % n; v2 = rng() % n;
                            }
                            had2 = g.has_edge(u2, v2);
                            if (had2) g.rem_edge(u2, v2);
                            else g.add_edge(u2, v2);
                        }

                        bool ok = (!had1 && (!had2 || u2 == -1)) ? true : g.is_connected();
                        if (!ok) {
                            // Undo
                            if (u2 != -1) { if (had2) g.add_edge(u2, v2); else g.rem_edge(u2, v2); }
                            if (had1) g.add_edge(u1, v1); else g.rem_edge(u1, v1);
                            continue;
                        }

                        Invariants nxt_inv = compute_invariants(g, ws, need_rad);
                        double nxt_val = margin(cid, nxt_inv);
                        double delta = nxt_val - cur_val;

                        bool accept = (delta <= 0.0) ||
                                      ((double)(rng() % 1000000) / 1000000.0 < std::exp(-delta / T));
                        if (accept) {
                            cur_val = nxt_val;
                            if (cur_val < best_val) {
                                best_val = cur_val;
                                best_g = g;
                                if (best_val < -1e-6) {
                                    std::lock_guard<std::mutex> lk(io_mtx);
                                    std::string path = std::string("witnesses/conj_2611_03879_") + CONJ_NAMES[cid] + ".json";
                                    save_witness(path, CONJ_NAMES[cid], best_g, best_val);
                                    std::cout << ">>> FOUND CANDIDATE FOR " << CONJ_NAMES[cid]
                                              << ": margin=" << best_val << " n=" << best_g.n
                                              << " m=" << best_g.m << " saved to " << path << " <<<\n" << std::flush;
                                }
                            }
                        } else {
                            if (u2 != -1) { if (had2) g.add_edge(u2, v2); else g.rem_edge(u2, v2); }
                            if (had1) g.add_edge(u1, v1); else g.rem_edge(u1, v1);
                        }
                    }
                    if (best_val < -1e-6) break;
                }
                if (best_val < -1e-6) break;
            }

            {
                std::lock_guard<std::mutex> lk(io_mtx);
                global_best[cid] = best_val;
                global_best_n[cid] = best_g.n;
                global_best_m[cid] = best_g.m;
                std::cout << "[" << std::setw(6) << CONJ_NAMES[cid] << "] best margin = "
                          << std::fixed << std::setprecision(6) << best_val
                          << " (n=" << best_g.n << ", m=" << best_g.m << ")\n" << std::flush;
                // Also save closest graph if very close (< 0.1)
                if (best_val < 0.05) {
                    std::string path = std::string("witnesses/closest_2611_03879_") + CONJ_NAMES[cid] + ".json";
                    save_witness(path, CONJ_NAMES[cid], best_g, best_val);
                }
            }
        });
    }

    for (auto& t : threads) t.join();
    return 0;
}
