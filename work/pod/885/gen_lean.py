"""Emit a Lean proof of the Erdős 885 statement at level k from integers Ns sharing differences Ds.

usage: python3 gen_lean.py K "N1,N2,..." "d1,d2,..." > out.lean
Mirrors the in-file proof of `erdos_885.variants.k_eq_4` (formal-conjectures @ d9ce556).
"""

import sys
from math import isqrt


def b_for(n: int, d: int) -> int:
    s2 = 4 * n + d * d
    s = isqrt(s2)
    assert s * s == s2 and (s - d) % 2 == 0, (n, d)
    b = (s - d) // 2
    assert n == b * (b + d)
    return b


def fs(xs):
    return "{" + ", ".join(map(str, xs)) + "}"


def main() -> None:
    k = int(sys.argv[1])
    Ns = sorted(int(x) for x in sys.argv[2].split(","))
    Ds = sorted(int(x) for x in sys.argv[3].split(","))
    assert len(set(Ns)) == len(Ns) == k and len(set(Ds)) == len(Ds) >= k and min(Ns) >= 1
    Ds = Ds[:k]
    bs = [b_for(n, d) for n in Ns for d in Ds]
    pats = " | ".join(["rfl"] * k)
    exacts = ",\n      ".join(
        f"mem_factorDifferenceSet_of_eq (b := {b}) (by norm_num)" for b in bs
    )
    print(f"""import FormalConjectures.ErdosProblems.«885»

open Erdos885 Set Finset

theorem erdos_885_level_{k} :
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = {k} ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ {k} := by
  refine ⟨{fs(Ns)}, by simp, by decide, ?_⟩
  have hsub : (↑({fs(Ds)} : Finset ℕ) : Set ℕ) ⊆
      ⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n := by
    intro d hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hd
    simp only [Set.mem_iInter, Finset.mem_insert, Finset.mem_singleton]
    rintro n ({pats}) <;> rcases hd with {pats}
    exacts [{exacts}]
  have hfin : (⋂ n ∈ ({fs(Ns)} : Finset ℕ), factorDifferenceSet n).Finite :=
    (factorDifferenceSet_finite (by norm_num : 1 ≤ {Ns[0]})).subset
      (Set.iInter₂_subset {Ns[0]} (by simp))
  calc {k} = (↑({fs(Ds)} : Finset ℕ) : Set ℕ).ncard := by
        rw [Set.ncard_coe_finset]; decide
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

#print axioms erdos_885_level_{k}
""")


if __name__ == "__main__":
    main()
