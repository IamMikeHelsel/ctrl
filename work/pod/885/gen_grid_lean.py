"""Emit Lean theorems: given integers Ns sharing factor differences Ds, prove the inclusion and
the ncard bound against FC's `Erdos885.factorDifferenceSet`.

usage: python3 gen_grid_lean.py OUT.lean NAME "N1,N2,..." "d1,d2,..." [NAME "Ns" "Ds" ...]
"""

import sys
from math import isqrt


def fs(xs):
    return "{" + ", ".join(map(str, xs)) + "}"


def emit(name: str, Ns: list[int], Ds: list[int]) -> str:
    Ns, Ds = sorted(Ns), sorted(Ds)
    bs = []
    for n in Ns:
        for d in Ds:
            s = isqrt(4 * n + d * d)
            assert s * s == 4 * n + d * d and (s - d) % 2 == 0, (n, d)
            b = (s - d) // 2
            assert n == b * (b + d)
            bs.append(b)
    pn = " | ".join(["rfl"] * len(Ns))
    pd = " | ".join(["rfl"] * len(Ds))
    ex = ",\n      ".join(f"mem_factorDifferenceSet_of_eq (b := {b}) (by norm_num)" for b in bs)
    return f"""
/-- {len(Ns)} integers whose factor-difference sets share {len(Ds)} elements. -/
theorem {name} :
    (↑({fs(Ds)} : Finset ℕ) : Set ℕ) ⊆ ⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n ∧
    {len(Ds)} ≤ (⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n).ncard := by
  have hsub : (↑({fs(Ds)} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n ({pn}) <;> rcases hd with {pd}
    exacts [{ex}]
  have hfin : (⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ {Ns[0]})).subset
      (Set.iInter₂_subset {Ns[0]} (by simp))
  refine ⟨hsub, ?_⟩
  calc {len(Ds)} = (↑({fs(Ds)} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms {name}
"""


HEADER = """import FormalConjectures.ErdosProblems.«885»

/-!
# Erdős 885: square-sum grids found by the ctrl pod (AI-generated, 2026-10-18)

Each theorem is one integer reading of a rational grid `U + V ⊆ squares`.
-/

open Erdos885 Set Finset
"""


def main() -> None:
    out, rest = sys.argv[1], sys.argv[2:]
    src = HEADER
    for i in range(0, len(rest), 3):
        name, ns, ds = rest[i : i + 3]
        src += emit(name, [int(x) for x in ns.split(",")], [int(x) for x in ds.split(",")])
    with open(out, "w") as f:
        f.write(src)


if __name__ == "__main__":
    main()
