import Mathlib.Data.Real.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
set_option autoImplicit false
namespace S01Gluing
open Filter Set
open scoped Topology

-- Generic local-to-global interface. Actual constructor binding is a separate obligation.
def glued {X : Type} (f : ℕ → ℝ → X) (pick : ℝ → ℕ) (t : ℝ) : X := f (pick t) t

theorem agrees {X : Type} (f : ℕ → ℝ → X) (H : ℕ → ℝ) (pick : ℝ → ℕ)
    (cover : ∀ t, t ≤ H (pick t))
    (compatible : ∀ m n t, t ≤ H m → t ≤ H n → f m t=f n t)
    (n : ℕ) (t : ℝ) (ht : t ≤ H n) : glued f pick t=f n t :=
  compatible (pick t) n t (cover t) ht

theorem safe {X : Type} (f : ℕ → ℝ → X) (H : ℕ → ℝ) (pick : ℝ → ℕ)
    (cover : ∀ t, t ≤ H (pick t)) (P : X → Prop)
    (finite_safe : ∀ n t, 0 ≤ t → t ≤ H n → P (f n t)) :
    ∀ t, 0 ≤ t → P (glued f pick t) := by
  intro t ht
  exact finite_safe (pick t) t ht (cover t)

theorem local_agrees {X : Type} (f : ℕ → ℝ → X) (H : ℕ → ℝ) (pick : ℝ → ℕ)
    (cover : ∀ t, t ≤ H (pick t))
    (compatible : ∀ m n t, t ≤ H m → t ≤ H n → f m t=f n t)
    (n : ℕ) (t : ℝ) (ht : t < H n) :
    glued f pick =ᶠ[𝓝 t] f n := by
  filter_upwards [Iio_mem_nhds ht] with u hu
  exact agrees f H pick cover compatible n u (le_of_lt hu)

 theorem local_continuity {X : Type} [TopologicalSpace X]
    (f : ℕ → ℝ → X) (H : ℕ → ℝ) (pick : ℝ → ℕ)
    (cover : ∀ t, t ≤ H (pick t))
    (compatible : ∀ m n t, t ≤ H m → t ≤ H n → f m t=f n t)
    (n : ℕ) (t : ℝ) (ht : t < H n) (hf : ContinuousAt (f n) t) :
    ContinuousAt (glued f pick) t :=
  hf.congr_of_eventuallyEq (local_agrees f H pick cover compatible n t ht)

#print axioms agrees
#print axioms safe
#print axioms local_agrees
#print axioms local_continuity
end S01Gluing
