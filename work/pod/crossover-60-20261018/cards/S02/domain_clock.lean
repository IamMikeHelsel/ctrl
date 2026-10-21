import HandoffAssembly
noncomputable section
set_option autoImplicit false
namespace S02Clock
open LeanControls LeanControls.ConstructiveHold

def arrival (latency : ℕ → ℝ) (n : ℕ) : ℝ := grid n+latency n
/-- Release cannot precede packet arrival; buffering targets the unchanged C8
clock. Equality with that clock uses the stated transport upper bound. -/
def release (latency : ℕ → ℝ) (n : ℕ) : ℝ := max (arrival latency n) (grid n+h)

theorem arrival_order (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) {i j : ℕ} (hij : i<j) :
    arrival latency i≤arrival latency j := by
  have hi := hb i
  have hj := hb j
  have hc : (i:ℝ)+1≤j := by exact_mod_cast (show i+1≤j by omega)
  dsimp [arrival,grid] at *
  norm_num at hi hj
  linarith

theorem tie_characterization (latency : ℕ → ℝ)
    (hb : ∀ n, 0≤latency n ∧ latency n≤h) {i j : ℕ} (hij : i<j) :
    arrival latency i=arrival latency j ↔
      j=i+1 ∧ latency i=h ∧ latency j=0 := by
  constructor
  · intro he
    have hi := hb i
    have hj := hb j
    have hc : (i:ℝ)+1≤j := by exact_mod_cast (show i+1≤j by omega)
    have hc' : (j:ℝ)≤(i:ℝ)+1 := by
      dsimp [arrival,grid] at he
      norm_num at hi hj
      linarith
    have hjle : j ≤ i+1 := by exact_mod_cast hc'
    have hji : j=i+1 := by omega
    subst j
    refine ⟨rfl,?_,?_⟩
    all_goals simp only [arrival,grid,Nat.cast_add,Nat.cast_one] at he
    · norm_num at hi hj ⊢; linarith
    · norm_num at hi hj; linarith
  · rintro ⟨rfl,hi,hj⟩
    simp [arrival,grid,hi,hj]
    ring

theorem release_eq (latency : ℕ → ℝ) (hb : ∀ n, latency n≤h) (n : ℕ) :
    release latency n=grid n+h := by
  unfold release arrival
  apply max_eq_right
  linarith [hb n]

theorem ready_at_release (latency : ℕ → ℝ) (n : ℕ) :
    arrival latency n≤release latency n := le_max_left _ _

theorem release_strict (latency : ℕ → ℝ) (hb : ∀ n, latency n≤h) :
    StrictMono (release latency) := by
  intro i j hij
  rw [release_eq latency hb i,release_eq latency hb j]
  linarith [grid_strict hij]

theorem prefix_available (latency : ℕ → ℝ) (hb : ∀ n, latency n≤h)
    {j k : ℕ} (hjk : j≤k) : arrival latency j≤release latency k := by
  calc
    _ ≤ release latency j := ready_at_release latency j
    _ ≤ release latency k := (release_strict latency hb).monotone hjk

theorem exact_source_cell_age (latency : ℕ → ℝ) (hb : ∀ n, latency n≤h)
    (n : ℕ) {t : ℝ} (ht : grid n+h≤t ∧ t≤release latency (n+1)) :
    grid n≤t ∧ t-grid n≤1/1000 := by
  rw [release_eq latency hb] at ht
  simp only [grid,Nat.cast_add,Nat.cast_one] at ht ⊢
  norm_num at ht
  constructor <;> linarith [ht.1,ht.2]

#print axioms arrival_order
#print axioms tie_characterization
#print axioms release_eq
#print axioms ready_at_release
#print axioms release_strict
#print axioms prefix_available
#print axioms exact_source_cell_age
end S02Clock
