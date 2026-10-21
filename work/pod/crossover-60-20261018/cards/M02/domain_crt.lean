import Research.CoveringCRT
import Mathlib.Tactic
/-! Specializes the existing kernel-checked counting bridge to a real-valued
conditional budget, including period720. No original source is edited/rebuilt. -/
set_option autoImplicit false
namespace M02ConditionalCRT
open Research.CoveringCRT

/-- Universal finite-period bound. C bounds every compatible survivor fiber;
H may be any common period, not merely a search cutoff or the prefix period. -/
theorem conditional_density_bound (B H m a C : ℕ) (hB : 0<B) (hm : 0<m)
    (hBH : B∣H) (hmH : m∣H) (U : Finset ℕ)
    (hf : ∀ r : ℕ, (U.filter (fun x => x % B.gcd m = r % B.gcd m)).card ≤ C) :
    (((Finset.range H).filter (fun x => x%B∈U ∧ x%m=a%m)).card:ℝ) ≤
      (H:ℝ)*(B.gcd m:ℝ)*C/((B:ℝ)*m) := by
  have hl : B.lcm m∣H := Nat.lcm_dvd hBH hmH
  have he : H / B.lcm m * B.lcm m=H := Nat.div_mul_cancel hl
  have hc := conditional_class_card_le B m (H / B.lcm m) (a%m) hB hm U
  rw [he] at hc
  have hc' : ((Finset.range H).filter (fun x => x%B∈U ∧ x%m=a%m)).card ≤
      C*(H/B.lcm m) := hc.trans (Nat.mul_le_mul_right _ (hf (a%m)))
  have hcR : (((Finset.range H).filter (fun x => x%B∈U ∧ x%m=a%m)).card:ℝ) ≤
      (C:ℝ)*(H/B.lcm m:ℕ) := by exact_mod_cast hc'
  have heR : (H/B.lcm m:ℕ)*(B.lcm m:ℝ)=(H:ℝ) := by exact_mod_cast he
  have hp : (B.gcd m:ℝ)*(B.lcm m:ℝ)=(B:ℝ)*m := by
    exact_mod_cast Nat.gcd_mul_lcm B m
  have hBr : (0:ℝ)<B := by exact_mod_cast hB
  have hmr : (0:ℝ)<m := by exact_mod_cast hm
  apply (le_div_iff₀ (mul_pos hBr hmr)).2
  calc
    _ ≤ ((C:ℝ)*(H/B.lcm m:ℕ))*((B:ℝ)*m) :=
      mul_le_mul_of_nonneg_right hcR (mul_pos hBr hmr).le
    _ = ((C:ℝ)*(H/B.lcm m:ℕ))*((B.gcd m:ℝ)*(B.lcm m:ℝ)) := by rw [hp]
    _ = (C:ℝ)*((H/B.lcm m:ℕ)*(B.lcm m:ℝ))*(B.gcd m:ℝ) := by ring
    _ = _ := by rw [heR]; ring

/-- The exact period used by the eleven-smooth certificate. -/
theorem period720_conditional_bound (H m a C : ℕ) (hm : 0<m)
    (hH : 720∣H) (hmH : m∣H) (U : Finset ℕ)
    (hf : ∀ r : ℕ, (U.filter (fun x => x % (720:ℕ).gcd m = r % (720:ℕ).gcd m)).card ≤ C) :
    (((Finset.range H).filter (fun x => x%720∈U ∧ x%m=a%m)).card:ℝ) ≤
      (H:ℝ)*((720:ℕ).gcd m:ℝ)*C/(720*(m:ℝ)) :=
  conditional_density_bound 720 H m a C (by norm_num) hm hH hmH U hf

#print axioms conditional_density_bound
#print axioms period720_conditional_bound
end M02ConditionalCRT
