module
public import ClearanceWitness
public import DelayedWitness
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.ConstructiveHold
open Set Filter DigitalHold
abbrev h : ℝ := 1/2000
def grid (n : ℕ) : ℝ := (n:ℝ)/2000
abbrev index := DelayedEntry.Witness.index
abbrev stamp := DelayedEntry.Witness.stamp

theorem grid_succ (n : ℕ) : grid (n+1)=h+grid n := by simp [grid,Nat.cast_add]; ring

theorem grid_nonneg (n : ℕ) : 0 ≤ grid n := by dsimp [grid]; positivity

theorem grid_strict : StrictMono grid := by
  intro i j hij
  have hh : (i:ℝ)<j := by exact_mod_cast hij
  dsimp [grid]; linarith

theorem right_index {n : ℕ} {t : ℝ} (ht : t ∈ Ico (grid (n+1)) (grid (n+2))) :
    index true t=n := by
  have ht0 : h ≤ t := by
    have hh := grid_nonneg n
    rw [grid_succ] at ht; linarith [ht.1]
  have hi := DelayedEntry.Witness.right_cell ht0
  change h+grid (index true t) ≤ t ∧ t<h+grid (index true t+1) at hi
  rw [← grid_succ,← grid_succ] at hi
  rcases lt_trichotomy (index true t) n with he | he | he
  · have hh := grid_strict.monotone (show index true t+2 ≤ n+1 by omega)
    linarith [hi.2,ht.1]
  · exact he
  · have hh := grid_strict.monotone (show n+2 ≤ index true t+1 by omega)
    linarith [hi.1,ht.2]

theorem left_index {n : ℕ} {t : ℝ} (ht : t ∈ Ioc (grid (n+1)) (grid (n+2))) :
    index false t=n := by
  have ht0 : h<t := by
    have hh := grid_nonneg n
    rw [grid_succ] at ht; linarith [ht.1]
  have hi := DelayedEntry.Witness.left_cell ht0
  change h+grid (index false t)<t ∧ t≤h+grid (index false t+1) at hi
  rw [← grid_succ,← grid_succ] at hi
  rcases lt_trichotomy (index false t) n with he | he | he
  · have hh := grid_strict.monotone (show index false t+2 ≤ n+1 by omega)
    linarith [hi.2,ht.1]
  · exact he
  · have hh := grid_strict.monotone (show n+2 ≤ index false t+1 by omega)
    linarith [hi.1,ht.2]

def measure (m : State) (ε : ℕ → State) (f : ℝ → State) (n : ℕ) : State :=
  if n=0 then m else fun i => f (grid n) i+ε n i

def readings (m : State) (ε : ℕ → State) (f : ℝ → State) (b : Bool) (t : ℝ) : State :=
  measure m ε f (index b t)

def schedule (m : State) (ε : ℕ → State) (f : ℝ → State) : Schedule where
  sample := grid
  dispatch n := h+grid n
  measurement := measure m ε f
  index := index

theorem actual_schedule (H : ℝ) (m : State) (ε : ℕ → State) (f : ℝ → State) :
    ClearanceAdmission.IsSchedule H h (schedule m ε f) stamp (readings m ε f) := by
  constructor
  · norm_num [schedule,grid]
  · norm_num [schedule,grid]
  · intro b t ht; exact DelayedEntry.Witness.startup_index b ht.2
  · intro n; exact ⟨grid_nonneg n,by dsimp [schedule]; norm_num; linarith [grid_nonneg n]⟩
  · intro m n hmn; dsimp [schedule]; linarith [grid_strict hmn]
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (2000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change h+grid n ≤ T at hn
    change n<N
    have hh : (n:ℝ)<N := by dsimp [grid] at hn; linarith
    exact_mod_cast hh
  · intro t ht; exact DelayedEntry.Witness.right_cell ht.1
  · intro t ht; exact DelayedEntry.Witness.left_cell ht.1
  · intro b t ht; rfl
  · intro b t ht; rfl

end LeanControls.ConstructiveHold
