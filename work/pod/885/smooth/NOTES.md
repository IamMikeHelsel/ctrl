# Erdős 885 smooth / retrieval search

## Result

On 2026-10-18 this search found the target shape T4, an exact `K_{3,6}`:

```
N = 349102656, 1034586000, 4883112000
d = 6720, 15855, 26880, 45440, 69510, 129290
```

All three `N` are 59-smooth:

```
349102656  = 2^6 * 3^3 * 7^3 * 19 * 31
1034586000 = 2^4 * 3^3 * 5^3 * 7^2 * 17 * 23
4883112000 = 2^6 * 3^3 * 5^3 * 13 * 37 * 47
```

Factor-pair certificate (each tuple is `d:a*b`):

```
349102656:
  6720:15624*22344   15855:12369*28224  26880:9576*36456
  45440:6696*52136   69510:4704*74214   129290:2646*131936
1034586000:
  6720:28980*35700   15855:25200*41055  26880:21420*48300
  45440:16660*62100  69510:12600*82110  129290:7560*136850
4883112000:
  6720:66600*73320   15855:62400*78255  26880:57720*84600
  45440:50760*96200  69510:43290*112800 129290:30550*159840
```

`verify_hit.py` independently enumerates every divisor through `isqrt(N)` and
also checks `isqrt(4*N+d*d)^2 == 4*N+d*d`, parity, reconstructed factors, and
distinctness. It was run successfully:

```
PASS: exact K_{3,6}; 18 edges checked two ways
```

Transposing the associated 4x6 square grid and scaling by 4 gives the
equivalent other T4 form, an exact `K_{5,4}`:

```
N = 206222625, 677376000, 2019635200, 4786481700, 16670745700
d = 13440, 75936, 129360, 279840
PASS: exact K_{5,4}; 20 edges checked two ways
```

Concretely, with `d0=6720`, the new numbers are `d_j^2-d0^2` for the other
five old differences. The new differences are twice the four square roots of
`d0^2+4*N_i`, including the anchored row `N_0=0`. The factor 2 is the
square-grid scaling needed because the old differences have mixed parity.

This is a T4 / 6x4-grid stepping stone, not a solution of k=5. It appears new
relative to the Erdős Problems #885 forum as read on 2026-10-18, where the
reported 6x4 search was negative.

## Method

`search.cpp` recursively enumerates every y-smooth integer through `X`, derives
`D(N)` from its exact prime factorization, and retains rows with at least four
positive differences. It builds an inverted index `d -> N`, counts pair
co-occurrences with per-root byte counters on 16 threads, and recursively
extends candidate row sets while maintaining the exact sorted intersection of
their differences. Candidate edges require at least four common differences,
which is sufficient for all requested T1--T4 shapes.

The alternate `nonsmooth` mode enumerates exact records
`N=b(b+d)` for smooth `d`, sorts by `N`, forms transactions, then uses the same
miner. This admits arbitrary prime factors in `N`.

The first implementation used one global pair hash. At `y=31, X=10^10` it
exceeded 4 GB before finishing, so it was stopped and replaced by bounded
per-root counters. No search result was inferred from the stopped run.

## Completed searches and negative results

All bounds below are inclusive. "No" means no listed target in the stated
finite search, not a global nonexistence claim.

| generator | range | retained rows | total time | strongest shapes | target result |
|---|---:|---:|---:|---|---|
| smooth | `y=31, X=10^7` plus known sanity rows | 48,145 | 0.33 s | recovered injected Aleksanndr `K4,4` | sanity only |
| smooth | `y=31, X=10^10` plus known sanity rows | 581,044 | 65.88 s | `K2,15`, `K3,5`, injected `K4,4` | no T1--T4 |
| smooth | `y=43, X=10^10` | 1,408,107 | 168.65 s | `K2,17`, `K3,5`, `K4,4` | no T1--T4 |
| smooth | `y=59, X=10^10` | 2,728,140 | 577.43 s | `K2,17`, **`K3,6`**, `K4,4` | **T4 hit** |
| `b(b+d)` | 13-smooth `d<=5000`, `b<=20000`, `N<=10^10` | 47,216 | 0.59 s | `K2,6`, `K3,4` | no target |
| `b(b+d)` | 31-smooth `d<=20000`, `b<=50000`, `N<=10^10` | 1,162,725 | 10.50 s | `K2,7`, `K3,4` | no target |
| `b(b+d)` | 31-smooth `d<=50000`, `b<=50000`, `N<=10^10` | 2,760,028 | 26.82 s | `K2,7`, `K3,5` | no target |

The largest nonsmooth run sorted 213,050,000 generated `(N,d)` records, about
7.94 million records/second end-to-end. Smooth generation itself produced
2,728,648 values in 10.02 s at `y=59`; the full inverted-index and biclique
mining pass dominated the 577.43 s total.

## Best bicliques by number of N rows

Overall (including exact grid transposition of the T4 hit):

```
a=2: K_2,17
  N = 1705374000, 4437342000
  d = 4296, 13510, 21560, 27720, 48015, 49110, 56520, 77880,
      164199, 209970, 227640, 265986, 304568, 339570, 441672,
      643335, 1893960
a=3: K_3,6
  N = 349102656, 1034586000, 4883112000
  d = 6720, 15855, 26880, 45440, 69510, 129290
a=4: K_4,4
  N = 274833, 1225728, 3368448, 30159360
  d = 432, 2232, 3312, 9448
a=5: K_5,4
  N = 206222625, 677376000, 2019635200, 4786481700, 16670745700
  d = 13440, 75936, 129360, 279840
a=6: no K_6,b with b>=4
```

The direct `y=59, X=10^10` row search had no `K_5,b` with `b>=4`; the
displayed `K_5,4` is the independently verified transpose of its `K_3,6`.

The `y=43` run also rediscovered Mausberg's five square-sum columns in integer
factor-difference normalization:

```
N = 189000, 3992800, 11282544
d = 330, 870, 2445, 4155, 10482
```

This confirms the convention: Mausberg's posted `Y(756000,15971200,45130176)`
uses those values as square abscissae `z`; dividing the three offsets by four
gives the `N` above with factor differences `d=z`. This is different from the
separate smooth packet `79200,227205,1258560`, whose common differences are
`36,468,692,1028` (1029 is a known typo).

## Next scaling step

The promising direction is to keep `X=10^10` and raise the smoothness bound
from 59 to about 100, because the first T4 appeared only when primes 47--59
were admitted. Before doing that, replace the `unordered_map` posting store
with sorted packed `(d,row)` occurrences and discard singleton postings; at
`y=59`, 72,750,247 distinct differences and 54,951,586 candidate pairs made
index construction/mining memory-bound. After that representation change,
run `y=101, X=10^10`, then raise `X` toward `10^12`. For the alternate
generator, expand `b` before `d`; the `d<=50000` run already covered 213
million records cheaply but remained at `K3,5`.

## Wave 2: extension through q=10^6 and trillion-range search

The miner now writes every requested shape (`K_3,b` for `b>=6`, `K_4,b` for
`b>=5`, and `K_5,b` for `b>=5`) to `all_k36.txt`, deduplicated by its exact
row set and full common-difference set. Its inverted index uses sorted packed
64-bit `(d,row)` keys and at most 10 threads.

There are seven literal `K_3,6` records and three primitive square-scaling
classes. Five records are the `t=1,2,3,4,5` square scalings of class 2.
`analyze_grids.py` and `structures.txt` give the exact ratio invariants.

The third primitive class, found in the bounded trillion-range run, is:

```
N = 381244500, 1117839744, 31512096000
d = 14280, 26760, 31640, 67368, 100065, 136920
```

It passed `verify_hit.py`. Its factorizations are:

```
381244500   = 2^2 * 3^2 * 5^3 * 7^3 * 13 * 19
1117839744  = 2^7 * 3^3 * 7^3 * 23 * 41
31512096000 = 2^8 * 3^2 * 5^3 * 7^3 * 11 * 29
```

Thus it is actually 43-smooth; the larger `X`, not the larger prime bound,
made it visible. Its transposed `K_5,4`, also checked exactly, is:

```
N = 512179200, 797171200, 4334529024, 9809085825, 18543168000
d = 28560, 83160, 136752, 710640
```

The three primitive classes are not square scalings of one another. Their
`gcd(N), gcd(d)` pairs are respectively `(432,5)`, `(1440,1)`, and
`(12348,1)`. No simple equality of their normalized `N/N0` or `d/d0` ratios
appears; only class 2 produced a scaling family in the searched range.

### Exhaustive rational extensions

`extend_grids.cpp` uses 10 threads and tests reduced rational denominators.
For a new column it enumerates `D(q^2*N_min)` exactly. For a new row it
factors `q^2*(d_j^2-d_0^2)` for a selected column pair, enumerates every
difference-of-squares factorization, and checks the other two columns. Thus
the row test is exhaustive for rational square roots of reduced denominator
`q` as well.

All three primitive grids were completed for every `1 <= q <= 1,000,000`:

| primitive class | new-column hits (6x5) | seconds | new-row hits (7x4) | seconds |
|---|---:|---:|---:|---:|
| class 1 | 0 | 112.93 | 0 | 392.32 |
| class 2 | 0 | 48.57 | 0 | 173.83 |
| class 3 | 0 | 1029.41 | 0 | 1807.53 |

Consequently there is no k=5 witness and no new 7x4 stepping stone in this
denominator range. Exact coverage is recorded in
`extension_q1e6_coverage.txt` and `extension_class3_q1e6_coverage.txt`.

### Larger-range index searches

The completed large run was exhaustive for:

```
59-smooth N <= 10^12
common differences d <= 250000
rows having at least five such differences
```

It generated 15,397,414 smooth values, retained 13,802,365 rows, indexed
381,453,344 occurrences, and finished in 4,507.43 seconds. It found class 3
and no `K_4,5`, `K_4,6`, or `K_5,5`.

Important negative-coverage qualifications:

- The earlier `43-smooth, X=10^12` attempt completed generation
  (6,799,519 values) but ended before index mining, so it is not a negative
  result.
- Full-difference `59-smooth, X=10^12` and a `d<=10^7` retry reached the
  memory ceiling and were stopped without results.
- `73-smooth, X=10^12, d<=250000` was killed during generation before any
  mining; it provides no negative coverage.
