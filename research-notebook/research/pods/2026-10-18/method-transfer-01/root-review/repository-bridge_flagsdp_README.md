# Flag-SDP machine — 2-colored max-cut switching SDP for Erdős #23 Step 2

Goal: prove `β(G)=e−MaxCut(G) ≤ n²` for triangle-free `G` on `N=5n` vertices in the band
`x=e/N²∈[0.1243,0.16]`, via GPT Q15's route: a **2-vertex-colored (max-cut A/B) triangle-free
flag-algebra SDP** with **macroscopic switching constraints**. Asymptotic certificate suffices
(audited blow-up transfer ⟹ exact). Target in flag terms: `d_mono ≤ 2/25 = 0.08` where
`d_mono` = monochromatic-edge density and `β/N² → d_mono/2`.

## Modules (built + validated from scratch, Python + cvxpy/CLARABEL/SCS)
- `flag_engine.py` — uncolored engine: bitmask graphs, brute canonical form, geng enumeration,
  induced subgraph densities. SELF-TEST: triangle-free counts = OEIS A006785 (1..107); densities OK.
- `flag_sdp.py` — flag enumeration, `P^σ(H)` product-matrix counts, dual SDP. **VALIDATED: reproduces
  Mantel (max triangle-free edge density) = 0.500000 exactly at N=3,4,5.**
- `flag_engine_col.py` — 2-colored engine: color-preserving canonical form, colored enumeration,
  colored densities (mono00/mono11/cut). SELF-TEST: counts + density identities OK.
- `flag_sdp_col.py` — colored flags, colored `P^σ`, **primal** SDP: maximize `d_mono` s.t. moment
  matrices `M^σ(x)⪰0`, edge-band, switching. The optimum is a certified upper bound on `d_mono`.
- `flag_switch.py` — max-cut SWITCHING constraints as colored-density limit functionals:
  general rooted switch `g(H)=Σ_R Σ_{uv∉R, edge} χ(uv)(p_u+p_v−2p_up_v) ≤ 0`, `p` a function of
  (color, adjacency to k roots), `p∈{0,½,1}`. SW1 (GPT's verified 1-root switch) is a special case;
  SW1-limit confirmed ≤0 on max cuts. `gen_rooted_switches` / `gen_switches` enumerate the families.
- `run_beta_sdp.py`, `run_beta_sdp2.py` — drivers; print the bound vs #switching-roots.

## Bound progression (max d_mono; β/N² = d_mono/2; target d_mono=0.08)
| roots | N=5 | meaning |
|------|------|---------|
| band only | 0.320 | nothing forces a good cut |
| +0-root  | 0.160 | d_mono ≤ d_cut |
| +1-root  | 0.118 | local cut optimality |
| +2-root  | 0.101 | β/N² ≤ 0.0503 |

Decreasing toward the target. Remaining: higher flag order (N=6,7), more switching roots (k=2 fractional /
k=3 via a SEPARATION ORACLE per GPT), color refinement by max-cut margin `h(v)=d_C(v)−d_M(v)`. If the
bound reaches ≤ 0.08, extract an exact rational PSD certificate (Phase D) — only then is it a proof.

## Status: Phase A,B DONE (engine validated); Phase C in progress (bound ~0.10, target 0.08); Phase D pending.
NOT a proof yet. CF/Step-2 still UNPROVEN.
