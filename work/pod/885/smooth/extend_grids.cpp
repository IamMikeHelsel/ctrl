#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <mutex>
#include <numeric>
#include <sstream>
#include <string>
#include <thread>
#include <utility>
#include <vector>

using u64 = uint64_t;
using u128 = __uint128_t;

static std::string str128(u128 n) {
    if (!n) return "0";
    std::string s;
    while (n) { s.push_back(char('0' + n % 10)); n /= 10; }
    std::reverse(s.begin(), s.end());
    return s;
}

static std::string str128s(__int128_t n) {
    if (n < 0) return "-" + str128((u128)(-n));
    return str128((u128)n);
}

static u128 isqrt128(u128 n) {
    u128 lo = 0, hi = (u128(1) << 64);
    while (lo + 1 < hi) {
        u128 m = (lo + hi) / 2;
        if (m <= n / m) lo = m; else hi = m;
    }
    return lo;
}

static bool square128(u128 n, u128* root = nullptr) {
    u128 s = isqrt128(n);
    if (root) *root = s;
    return s * s == n;
}

using Fac = std::vector<std::pair<u64,int>>;

static Fac factor(u64 n) {
    Fac f;
    for (u64 p = 2; p <= n / p; p += (p == 2 ? 1 : 2)) {
        if (n % p) continue;
        int e = 0;
        do { n /= p; ++e; } while (n % p == 0);
        f.push_back({p, e});
    }
    if (n > 1) f.push_back({n, 1});
    return f;
}

static void merge_q(Fac& f, const Fac& fq) {
    for (auto [p,e] : fq) {
        auto it = std::lower_bound(f.begin(), f.end(), p,
            [](const auto& x, u64 v){ return x.first < v; });
        if (it != f.end() && it->first == p) it->second += 2 * e;
        else f.insert(it, {p, 2 * e});
    }
}

static void divisors_rec(const Fac& f, size_t i, u128 cur,
                         std::vector<u128>& out) {
    if (i == f.size()) { out.push_back(cur); return; }
    u128 v = cur;
    for (int e = 0; e <= f[i].second; ++e) {
        divisors_rec(f, i + 1, v, out);
        v *= f[i].first;
    }
}

static u64 tau(const Fac& f) {
    u64 t = 1;
    for (auto [p,e] : f) t *= e + 1;
    return t;
}

struct K36 {
    std::vector<u64> ns, ds;
    std::string source;
};

static std::vector<u64> numbers_after(const std::string& line,
                                      const std::string& marker,
                                      const std::string& stop = "") {
    size_t p = line.find(marker);
    if (p == std::string::npos) return {};
    p += marker.size();
    size_t e = stop.empty() ? line.size() : line.find(stop, p);
    std::istringstream in(line.substr(p, e - p));
    std::vector<u64> v;
    u64 x;
    while (in >> x) v.push_back(x);
    return v;
}

static std::vector<K36> read_k36(const std::string& path) {
    std::ifstream in(path);
    std::vector<K36> out;
    std::string line;
    while (std::getline(in, line)) {
        if (line.rfind("K_3,", 0) != 0) continue;
        auto ns = numbers_after(line, " N:", " d:");
        auto ds = numbers_after(line, " d:");
        if (ns.size() == 3 && ds.size() >= 6)
            out.push_back({std::move(ns), std::move(ds), line});
    }
    return out;
}

static void choose6_rec(const K36& k, size_t at, std::vector<u64>& chosen,
                        std::vector<std::vector<u64>>& out) {
    if (chosen.size() == 6) { out.push_back(chosen); return; }
    if (k.ds.size() - at < 6 - chosen.size()) return;
    for (size_t i = at; i < k.ds.size(); ++i) {
        chosen.push_back(k.ds[i]);
        choose6_rec(k, i + 1, chosen, out);
        chosen.pop_back();
    }
}

struct Grid {
    std::vector<u64> ns, ds;
    std::string id;
};

static bool transpose(const K36& k, const std::vector<u64>& oldd,
                      size_t serial, Grid& g) {
    const u64 d0 = oldd[0];
    bool divide4 = true;
    for (size_t i = 1; i < oldd.size(); ++i)
        if (((u128)oldd[i] * oldd[i] - (u128)d0 * d0) % 4)
            divide4 = false;
    const u64 scale = divide4 ? 1 : 2;
    for (size_t i = 1; i < oldd.size(); ++i) {
        u128 v = (u128)oldd[i] * oldd[i] - (u128)d0 * d0;
        if (divide4) v /= 4;
        if (v > UINT64_MAX) return false;
        g.ns.push_back((u64)v);
    }
    std::vector<u64> anchored{0};
    anchored.insert(anchored.end(), k.ns.begin(), k.ns.end());
    for (u64 n : anchored) {
        u128 r;
        if (!square128((u128)d0*d0 + (u128)4*n, &r) ||
            r * scale > UINT64_MAX) return false;
        g.ds.push_back((u64)(r * scale));
    }
    std::sort(g.ns.begin(), g.ns.end());
    std::sort(g.ds.begin(), g.ds.end());
    std::ostringstream id;
    id << "grid_" << serial << "_old_d";
    for (u64 d : oldd) id << "_" << d;
    g.id = id.str();
    return true;
}

static u64 test_column(const Grid& g, u64 qmax, unsigned nthreads,
                       std::ofstream& hits, std::mutex& hit_mu) {
    size_t bi = 0;
    Fac bf = factor(g.ns[0]);
    u64 bt = tau(bf);
    for (size_t i = 1; i < g.ns.size(); ++i) {
        Fac f = factor(g.ns[i]);
        if (tau(f) < bt) { bi = i; bf = std::move(f); bt = tau(bf); }
    }
    const u64 base = g.ns[bi];
    std::vector<u64> others;
    for (size_t i = 0; i < g.ns.size(); ++i)
        if (i != bi) others.push_back(g.ns[i]);
    std::atomic<u64> next{1}, found{0};
    auto worker = [&]() {
        while (true) {
            u64 q = next.fetch_add(1, std::memory_order_relaxed);
            if (q > qmax) break;
            Fac f = bf;
            merge_q(f, factor(q));
            std::vector<u128> divs;
            divs.reserve(tau(f));
            divisors_rec(f, 0, 1, divs);
            const u128 M = (u128)base * q * q;
            for (u128 a : divs) {
                const u128 b = M / a;
                if (a >= b) continue;
                const u128 p = b - a;
                bool known = false;
                for (u64 d : g.ds) if (p == (u128)q * d) known = true;
                if (known || std::gcd((u64)(p % q), q) != 1) continue;
                bool ok = true;
                for (u64 n : others)
                    if (!square128((u128)4*n*q*q + p*p)) {
                        ok = false; break;
                    }
                if (!ok) continue;
                found.fetch_add(1);
                std::lock_guard<std::mutex> lock(hit_mu);
                hits << "COLUMN_HIT " << g.id << " q=" << q
                     << " p=" << str128(p) << " N:";
                for (u64 n : g.ns) hits << " " << str128((u128)n*q*q);
                hits << " d:";
                for (u64 d : g.ds) hits << " " << str128((u128)d*q);
                hits << " " << str128(p) << "\n";
                hits.flush();
            }
        }
    };
    std::vector<std::thread> ts;
    for (unsigned i = 0; i < nthreads; ++i) ts.emplace_back(worker);
    for (auto& t : ts) t.join();
    return found.load();
}

static u64 test_row(const Grid& g, u64 qmax, unsigned nthreads,
                    std::ofstream& hits, std::mutex& hit_mu) {
    const u64 d0 = g.ds[0];
    size_t second = 1;
    u64 delta = g.ds[1]*g.ds[1] - d0*d0;
    u64 best_tau = tau(factor(delta));
    for (size_t i = 2; i < g.ds.size(); ++i) {
        u64 v = g.ds[i]*g.ds[i] - d0*d0;
        u64 tv = tau(factor(v));
        if (tv < best_tau) { second = i; delta = v; best_tau = tv; }
    }
    const Fac basef = factor(delta);
    std::atomic<u64> next{1}, found{0};
    auto worker = [&]() {
        while (true) {
            u64 q = next.fetch_add(1, std::memory_order_relaxed);
            if (q > qmax) break;
            Fac f = basef;
            merge_q(f, factor(q));
            std::vector<u128> divs;
            divs.reserve(tau(f));
            divisors_rec(f, 0, 1, divs);
            const u128 C = (u128)delta*q*q;
            for (u128 a : divs) {
                const u128 b = C / a;
                if (a >= b || ((a ^ b) & 1)) continue;
                const u128 y = (b - a) / 2;
                if (std::gcd((u64)(y % q), q) != 1) continue;
                const __int128_t unum =
                    (__int128_t)(y*y) - (__int128_t)((u128)d0*d0*q*q);
                bool known = (unum == 0);
                for (u64 n : g.ns)
                    if (unum == (__int128_t)((u128)4*n*q*q)) known = true;
                if (known) continue;
                bool ok = true;
                for (u64 d : g.ds) {
                    __int128_t z2 = unum +
                        (__int128_t)((u128)d*d*q*q);
                    if (z2 < 0 || !square128((u128)z2)) {
                        ok = false; break;
                    }
                }
                if (!ok) continue;

                std::vector<__int128_t> rv{0, unum};
                for (u64 n : g.ns)
                    rv.push_back((__int128_t)((u128)4*n*q*q));
                __int128_t rmin = *std::min_element(rv.begin(), rv.end());
                std::vector<u128> positive;
                bool div4 = true;
                for (__int128_t r : rv) if (r != rmin) {
                    u128 v = (u128)(r-rmin);
                    if (v % 4) div4 = false;
                    positive.push_back(v);
                }
                std::vector<u128> newn, newd;
                for (u128 v : positive) newn.push_back(div4 ? v/4 : v);
                for (u64 d : g.ds) {
                    __int128_t c = (__int128_t)((u128)d*d*q*q) + rmin;
                    u128 root;
                    if (c < 0 || !square128((u128)c, &root)) {
                        ok = false; break;
                    }
                    newd.push_back(div4 ? root : 2*root);
                }
                if (!ok) continue;
                std::sort(newn.begin(), newn.end());
                std::sort(newd.begin(), newd.end());
                found.fetch_add(1);
                std::lock_guard<std::mutex> lock(hit_mu);
                hits << "ROW_HIT " << g.id << " q=" << q
                     << " y=" << str128(y) << " u=" << str128s(unum)
                     << "/" << q << "^2 N:";
                for (u128 n : newn) hits << " " << str128(n);
                hits << " d:";
                for (u128 d : newd) hits << " " << str128(d);
                hits << "\n";
                hits.flush();
            }
        }
    };
    std::vector<std::thread> ts;
    for (unsigned i = 0; i < nthreads; ++i) ts.emplace_back(worker);
    for (auto& t : ts) t.join();
    return found.load();
}

int main(int argc, char** argv) {
    if (argc != 6) {
        std::cerr << "usage: extend_grids k36.txt qmax threads hits.txt coverage.txt\n";
        return 2;
    }
    const u64 qmax = std::stoull(argv[2]);
    const unsigned nthreads = std::min(10u, (unsigned)std::stoul(argv[3]));
    auto ks = read_k36(argv[1]);
    std::ofstream hits(argv[4], std::ios::app);
    std::ofstream coverage(argv[5], std::ios::app);
    std::mutex hit_mu;
    size_t serial = 0, tested = 0;
    u64 total_hits = 0;
    for (const auto& k : ks) {
        std::vector<std::vector<u64>> subsets;
        std::vector<u64> chosen;
        choose6_rec(k, 0, chosen, subsets);
        for (const auto& ds : subsets) {
            Grid g;
            if (!transpose(k, ds, serial++, g)) {
                coverage << "SKIP_OVERFLOW source=" << k.source << "\n";
                continue;
            }
            auto t0 = std::chrono::steady_clock::now();
            std::cerr << "testing columns " << g.id << " q<= " << qmax << "\n";
            u64 hc = test_column(g, qmax, nthreads, hits, hit_mu);
            auto t1 = std::chrono::steady_clock::now();
            std::cerr << "testing rows " << g.id << " q<= " << qmax << "\n";
            u64 hr = test_row(g, qmax, nthreads, hits, hit_mu);
            auto t2 = std::chrono::steady_clock::now();
            coverage << "DONE " << g.id << " q=1.." << qmax
                     << " column_hits=" << hc << " row_hits=" << hr
                     << " column_seconds="
                     << std::chrono::duration<double>(t1-t0).count()
                     << " row_seconds="
                     << std::chrono::duration<double>(t2-t1).count() << " N:";
            for (u64 n : g.ns) coverage << " " << n;
            coverage << " d:";
            for (u64 d : g.ds) coverage << " " << d;
            coverage << "\n";
            coverage.flush();
            total_hits += hc + hr;
            ++tested;
        }
    }
    std::cerr << "done source_k36=" << ks.size() << " grids=" << tested
              << " hits=" << total_hits << "\n";
}
