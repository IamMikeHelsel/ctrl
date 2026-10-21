#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <sstream>
#include <string>
#include <thread>
#include <unordered_set>
#include <utility>
#include <vector>

using u64 = uint64_t;
using u128 = __uint128_t;

struct Row {
    u64 n;
    std::vector<u64> d;
};

static u64 isqrt_u64(u64 n) {
    u64 x = (u64)std::sqrt((long double)n);
    while ((u128)(x + 1) * (x + 1) <= n) ++x;
    while ((u128)x * x > n) --x;
    return x;
}

static std::vector<int> primes_to(int y) {
    std::vector<int> ps;
    for (int n = 2; n <= y; ++n) {
        bool prime = true;
        for (int p : ps) {
            if (p * p > n) break;
            if (n % p == 0) { prime = false; break; }
        }
        if (prime) ps.push_back(n);
    }
    return ps;
}

static void make_divisors(const std::vector<std::pair<int,int>>& fac, size_t i,
                          u64 cur, std::vector<u64>& out) {
    if (i == fac.size()) { out.push_back(cur); return; }
    u64 q = 1;
    for (int e = 0; e <= fac[i].second; ++e) {
        make_divisors(fac, i + 1, cur * q, out);
        q *= (u64)fac[i].first;
    }
}

static std::vector<u64> differences(u64 n,
                                    const std::vector<std::pair<int,int>>& fac) {
    std::vector<u64> divs, ds;
    make_divisors(fac, 0, 1, divs);
    u64 root = isqrt_u64(n);
    for (u64 a : divs) {
        if (a > root || n % a) continue;
        u64 b = n / a;
        if (a < b) ds.push_back(b - a);
    }
    std::sort(ds.begin(), ds.end());
    ds.erase(std::unique(ds.begin(), ds.end()), ds.end());
    return ds;
}

static void gen_rec(const std::vector<int>& ps, size_t i, u64 x, u64 cur,
                    std::vector<std::pair<int,int>>& fac, int min_d,
                    std::vector<Row>& rows, u64& generated) {
    if (i == ps.size()) {
        ++generated;
        if (cur <= 1) return;
        auto ds = differences(cur, fac);
        if ((int)ds.size() >= min_d) rows.push_back({cur, std::move(ds)});
        return;
    }
    int p = ps[i], e = 0;
    u64 v = cur;
    while (true) {
        if (e) fac.push_back({p, e});
        gen_rec(ps, i + 1, x, v, fac, min_d, rows, generated);
        if (e) fac.pop_back();
        if (v > x / (u64)p) break;
        v *= (u64)p;
        ++e;
    }
}

static void gen_oneprime_rec(const std::vector<int>& ps, size_t i, u64 limit,
                             u64 cur, u64 large_p,
                             std::vector<std::pair<int,int>>& fac, int min_d,
                             std::vector<Row>& rows, u64& generated) {
    if (i == ps.size()) {
        ++generated;
        if (cur <= 1) return;
        fac.push_back({(int)large_p, 1});
        auto ds = differences(cur * large_p, fac);
        fac.pop_back();
        if ((int)ds.size() >= min_d)
            rows.push_back({cur * large_p, std::move(ds)});
        return;
    }
    int p = ps[i], e = 0;
    u64 v = cur;
    while (true) {
        if (e) fac.push_back({p, e});
        gen_oneprime_rec(ps, i + 1, limit, v, large_p, fac, min_d,
                         rows, generated);
        if (e) fac.pop_back();
        if (v > limit / (u64)p) break;
        v *= (u64)p;
        ++e;
    }
}

static std::vector<u64> intersect_ds(const std::vector<u64>& a,
                                     const std::vector<u64>& b) {
    std::vector<u64> c;
    c.reserve(std::min(a.size(), b.size()));
    std::set_intersection(a.begin(), a.end(), b.begin(), b.end(),
                          std::back_inserter(c));
    return c;
}

struct Best {
    size_t b = 0;
    std::vector<uint32_t> ids;
    std::vector<u64> ds;
};

struct AllHits {
    std::ofstream out;
    std::unordered_set<std::string> seen;
    u64 added = 0;

    explicit AllHits(const std::string& path) {
        std::ifstream in(path);
        std::string line;
        while (std::getline(in, line))
            if (!line.empty()) seen.insert(line);
        out.open(path, std::ios::app);
    }

    void record(const std::vector<Row>& rows,
                const std::vector<uint32_t>& chosen,
                const std::vector<u64>& common) {
        const size_t a = chosen.size(), b = common.size();
        if (!((a == 3 && b >= 6) || (a == 4 && b >= 5) ||
              (a == 5 && b >= 5))) return;
        std::ostringstream s;
        s << "K_" << a << "," << b << " N:";
        for (uint32_t id : chosen) s << " " << rows[id].n;
        s << " d:";
        for (u64 d : common) s << " " << d;
        const std::string line = s.str();
        if (seen.insert(line).second) {
            out << line << "\n";
            out.flush();
            ++added;
            std::cerr << "ALL_HIT " << line << "\n";
        }
    }
};

static void record_best(const std::vector<uint32_t>& chosen,
                        const std::vector<u64>& common,
                        std::vector<Best>& best) {
    size_t a = chosen.size();
    if (a >= 2 && a < best.size() && common.size() > best[a].b) {
        best[a] = {common.size(), chosen, common};
        std::cerr << "BEST K_" << a << "," << common.size() << "\n";
    }
}

static void extend(const std::vector<Row>& rows,
                   const std::vector<std::vector<uint32_t>>& adj,
                   std::vector<uint32_t>& chosen, std::vector<uint32_t> cand,
                   const std::vector<u64>& common, std::vector<Best>& best,
                   AllHits& all, unsigned max_a, unsigned min_common) {
    record_best(chosen, common, best);
    all.record(rows, chosen, common);
    if (chosen.size() >= max_a) return;
    for (size_t pos = 0; pos < cand.size(); ++pos) {
        uint32_t v = cand[pos];
        auto next_common = intersect_ds(common, rows[v].d);
        if (next_common.size() < min_common) continue;
        std::vector<uint32_t> next;
        std::set_intersection(cand.begin() + pos + 1, cand.end(),
                              adj[v].begin(), adj[v].end(),
                              std::back_inserter(next));
        chosen.push_back(v);
        extend(rows, adj, chosen, std::move(next), next_common, best, all,
               max_a, min_common);
        chosen.pop_back();
    }
}

static void mine(const std::vector<Row>& rows, unsigned max_a,
                 unsigned min_common, const std::string& hits_path) {
    unsigned row_bits = 1;
    while ((u64(1) << row_bits) < rows.size()) ++row_bits;
    const u64 row_mask = (u64(1) << row_bits) - 1;
    u64 occurrence_count = 0;
    for (const auto& row : rows) occurrence_count += row.d.size();
    std::vector<u64> occ;
    occ.reserve(occurrence_count);
    for (uint32_t i = 0; i < rows.size(); ++i) for (u64 d : rows[i].d) {
        if (d > (UINT64_MAX >> row_bits)) {
            std::cerr << "difference too large for packed index\n";
            std::exit(3);
        }
        occ.push_back((d << row_bits) | i);
    }
    std::sort(occ.begin(), occ.end());

    std::vector<u64> group_values;
    std::vector<uint64_t> group_begin, group_end;
    u64 distinct_d = 0;
    for (size_t i = 0; i < occ.size();) {
        size_t j = i + 1;
        const u64 d = occ[i] >> row_bits;
        while (j < occ.size() && (occ[j] >> row_bits) == d) ++j;
        ++distinct_d;
        if (j - i >= 2) {
            uint32_t gid = (uint32_t)group_begin.size();
            group_values.push_back(d);
            group_begin.push_back(i);
            group_end.push_back(j);
        }
        i = j;
    }
    std::vector<int32_t> direct_gid;
    if (!group_values.empty() && group_values.back() <= 50000000) {
        direct_gid.assign(group_values.back() + 1, -1);
        for (uint32_t gid = 0; gid < group_values.size(); ++gid)
            direct_gid[group_values[gid]] = (int32_t)gid;
    }
    std::vector<std::vector<uint32_t>> adj(rows.size());
    std::atomic<uint32_t> next_root{0};
    unsigned nt = std::min(10u, std::max(1u, std::thread::hardware_concurrency()));
    auto worker = [&]() {
        std::vector<uint8_t> count(rows.size(), 0);
        std::vector<uint32_t> touched;
        while (true) {
            uint32_t root = next_root.fetch_add(1, std::memory_order_relaxed);
            if (root >= rows.size()) break;
            touched.clear();
            for (u64 d : rows[root].d) {
                int64_t gid = -1;
                if (!direct_gid.empty()) {
                    if (d < direct_gid.size()) gid = direct_gid[d];
                } else {
                    auto it = std::lower_bound(group_values.begin(),
                                               group_values.end(), d);
                    if (it != group_values.end() && *it == d)
                        gid = it - group_values.begin();
                }
                if (gid < 0) continue;
                for (u64 pos = group_begin[gid]; pos < group_end[gid]; ++pos) {
                    const uint32_t v = (uint32_t)(occ[pos] & row_mask);
                    if (v <= root) continue;
                    if (count[v] == 0) touched.push_back(v);
                    if (count[v] < min_common) ++count[v];
                }
            }
            auto& a = adj[root];
            for (uint32_t v : touched) {
                if (count[v] >= min_common) a.push_back(v);
                count[v] = 0;
            }
            std::sort(a.begin(), a.end());
            if (root && root % 100000 == 0)
                std::cerr << "paired_roots=" << root << "\n";
        }
    };
    std::vector<std::thread> threads;
    for (unsigned i = 0; i < nt; ++i) threads.emplace_back(worker);
    for (auto& t : threads) t.join();
    u64 candidate_pairs = 0;
    for (const auto& a : adj) candidate_pairs += a.size();
    std::vector<u64>().swap(group_values);
    std::vector<uint64_t>().swap(group_begin);
    std::vector<uint64_t>().swap(group_end);
    std::vector<int32_t>().swap(direct_gid);
    std::vector<u64>().swap(occ);
    std::cerr << "rows=" << rows.size() << " occurrences=" << occurrence_count
              << " distinct_d=" << distinct_d
              << " packed_row_bits=" << row_bits
              << " candidate_pairs_ge_" << min_common << "="
              << candidate_pairs << " threads=" << nt << "\n";

    std::vector<Best> best(max_a + 1);
    std::string all_path = "all_k36.txt";
    auto slash = hits_path.find_last_of('/');
    if (slash != std::string::npos)
        all_path = hits_path.substr(0, slash + 1) + "all_k36.txt";
    AllHits all(all_path);
    for (uint32_t root = 0; root < rows.size(); ++root) {
        std::vector<uint32_t> chosen{root};
        extend(rows, adj, chosen, adj[root], rows[root].d, best, all,
               max_a, min_common);
    }
    std::cerr << "new_target_hits=" << all.added << "\n";
    std::ofstream out(hits_path, std::ios::app);
    for (unsigned a = 2; a <= max_a; ++a) {
        out << "K_" << a << "," << best[a].b << " N:";
        for (auto id : best[a].ids) out << " " << rows[id].n;
        out << " d:";
        for (u64 d : best[a].ds) out << " " << d;
        out << "\n";
    }
}

static void add_known(std::vector<Row>& rows) {
    const u64 known[] = {79200, 227205, 1258560, 515504, 3542528, 6010004,
                         19523504};
    for (u64 n : known) {
        std::vector<std::pair<int,int>> fac;
        u64 q = n;
        for (u64 p = 2; p * p <= q; ++p) if (q % p == 0) {
            int e = 0; while (q % p == 0) { q /= p; ++e; }
            fac.push_back({(int)p,e});
        }
        if (q > 1) fac.push_back({(int)q,1});
        rows.push_back({n, differences(n, fac)});
    }
}

static void gen_values_rec(const std::vector<int>& ps, size_t i, u64 limit,
                           u64 cur, std::vector<u64>& out) {
    if (i == ps.size()) { out.push_back(cur); return; }
    u64 v = cur;
    while (true) {
        gen_values_rec(ps, i + 1, limit, v, out);
        if (v > limit / (u64)ps[i]) break;
        v *= (u64)ps[i];
    }
}

struct Occ {
    u64 n;
    u64 d;
    bool operator<(const Occ& o) const {
        return n < o.n || (n == o.n && d < o.d);
    }
};

static std::vector<Row> nonsmooth_rows(u64 x, int y, u64 dmax, u64 bmax,
                                       int min_d, u64& records) {
    auto ps = primes_to(y);
    std::vector<u64> ds;
    gen_values_rec(ps, 0, dmax, 1, ds);
    std::sort(ds.begin(), ds.end());
    std::vector<Occ> occ;
    for (u64 d : ds) {
        for (u64 b = 1; b <= bmax && (u128)b * (b + d) <= x; ++b)
            occ.push_back({b * (b + d), d});
    }
    records = occ.size();
    std::sort(occ.begin(), occ.end());
    std::vector<Row> rows;
    for (size_t i = 0; i < occ.size();) {
        size_t j = i + 1;
        while (j < occ.size() && occ[j].n == occ[i].n) ++j;
        std::vector<u64> got;
        for (size_t k = i; k < j; ++k)
            if (got.empty() || got.back() != occ[k].d) got.push_back(occ[k].d);
        if ((int)got.size() >= min_d) rows.push_back({occ[i].n, std::move(got)});
        i = j;
    }
    return rows;
}

int main(int argc, char** argv) {
    if (argc >= 2 && std::string(argv[1]) == "oneprime") {
        if (argc != 9) {
            std::cerr << "usage: search oneprime X smooth_bound pmin pmax "
                         "min_D max_a hits_file\n";
            return 2;
        }
        const u64 x = std::stoull(argv[2]);
        const int y = std::stoi(argv[3]), pmin = std::stoi(argv[4]);
        const int pmax = std::stoi(argv[5]), min_d = std::stoi(argv[6]);
        const unsigned max_a = (unsigned)std::stoul(argv[7]);
        auto t0 = std::chrono::steady_clock::now();
        auto small = primes_to(y), all = primes_to(pmax);
        std::vector<Row> rows;
        std::vector<std::pair<int,int>> fac;
        u64 generated = 0;
        for (int p : all) if (p > y && p >= pmin && (u64)p <= x)
            gen_oneprime_rec(small, 0, x / p, 1, p, fac, min_d,
                             rows, generated);
        std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
            return a.n < b.n;
        });
        auto t1 = std::chrono::steady_clock::now();
        std::cerr << "oneprime_generated=" << generated
                  << " retained=" << rows.size() << " gen_seconds="
                  << std::chrono::duration<double>(t1-t0).count() << "\n";
        mine(rows, max_a, 5, argv[8]);
        auto t2 = std::chrono::steady_clock::now();
        std::cerr << "total_seconds="
                  << std::chrono::duration<double>(t2-t0).count() << "\n";
        return 0;
    }
    if (argc >= 2 && std::string(argv[1]) == "nonsmooth") {
        if (argc != 9) {
            std::cerr << "usage: search nonsmooth X smooth_d_bound Dmax Bmax "
                         "min_D max_a hits_file\n";
            return 2;
        }
        u64 x = std::stoull(argv[2]), dmax = std::stoull(argv[4]);
        u64 bmax = std::stoull(argv[5]), records = 0;
        int y = std::stoi(argv[3]), min_d = std::stoi(argv[6]);
        unsigned max_a = (unsigned)std::stoul(argv[7]);
        auto t0 = std::chrono::steady_clock::now();
        auto rows = nonsmooth_rows(x, y, dmax, bmax, min_d, records);
        auto t1 = std::chrono::steady_clock::now();
        std::cerr << "records=" << records << " retained=" << rows.size()
                  << " gen_seconds="
                  << std::chrono::duration<double>(t1-t0).count() << "\n";
        mine(rows, max_a, 5, argv[8]);
        auto t2 = std::chrono::steady_clock::now();
        std::cerr << "total_seconds="
                  << std::chrono::duration<double>(t2-t0).count() << "\n";
        return 0;
    }
    if (argc < 6) {
        std::cerr << "usage: search X smooth_bound min_D max_a hits_file "
                     "[--known | --dmax D]\n";
        return 2;
    }
    u64 x = std::stoull(argv[1]);
    int y = std::stoi(argv[2]), min_d = std::stoi(argv[3]);
    unsigned max_a = (unsigned)std::stoul(argv[4]);
    std::string hits = argv[5];
    u64 dmax = UINT64_MAX;
    if (argc > 7 && std::string(argv[6]) == "--dmax")
        dmax = std::stoull(argv[7]);
    auto t0 = std::chrono::steady_clock::now();
    std::vector<Row> rows;
    u64 generated = 0;
    std::vector<std::pair<int,int>> fac;
    auto ps = primes_to(y);
    gen_rec(ps, 0, x, 1, fac, min_d, rows, generated);
    if (argc > 6 && std::string(argv[6]) == "--known") add_known(rows);
    if (dmax != UINT64_MAX) {
        for (auto& row : rows) {
            auto it = std::upper_bound(row.d.begin(), row.d.end(), dmax);
            row.d.erase(it, row.d.end());
            row.d.shrink_to_fit();
        }
        rows.erase(std::remove_if(rows.begin(), rows.end(),
            [min_d](const Row& r){ return (int)r.d.size() < min_d; }),
            rows.end());
        std::cerr << "applied_dmax=" << dmax
                  << " bounded_rows=" << rows.size() << "\n";
    }
    std::sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
        return a.n < b.n;
    });
    rows.erase(std::unique(rows.begin(), rows.end(),
                           [](const Row& a, const Row& b){return a.n==b.n;}),
               rows.end());
    auto t1 = std::chrono::steady_clock::now();
    std::cerr << "generated=" << generated << " retained=" << rows.size()
              << " gen_seconds="
              << std::chrono::duration<double>(t1-t0).count() << "\n";
    mine(rows, max_a, 5, hits);
    auto t2 = std::chrono::steady_clock::now();
    std::cerr << "total_seconds="
              << std::chrono::duration<double>(t2-t0).count() << "\n";
}
