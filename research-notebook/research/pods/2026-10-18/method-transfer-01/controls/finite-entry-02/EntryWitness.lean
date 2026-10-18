module
public import WeightedEntry
public import Mathlib.Algebra.Order.Floor.Semiring
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace LeanControls.WeightedEntry.Witness
open Set
open DigitalHold

def index (b : Bool) (t : ℝ) : ℕ := if b then Nat.floor (1000*t) else Nat.ceil (1000*t)-1
def stamp (b : Bool) (t : ℝ) : ℝ := (index b t : ℝ)/1000

theorem right_cell {t : ℝ} (ht : 0 ≤ t) :
    (index true t : ℝ)/1000 ≤ t ∧ t < ((index true t+1 : ℕ):ℝ)/1000 := by
  have hlo := Nat.floor_le (show 0 ≤ (1000:ℝ)*t by positivity)
  have hhi := Nat.lt_floor_add_one ((1000:ℝ)*t)
  norm_num [index,Nat.cast_add] at *
  constructor <;> linarith

theorem left_cell {t : ℝ} (ht : 0 < t) :
    (index false t : ℝ)/1000 < t ∧ t ≤ ((index false t+1 : ℕ):ℝ)/1000 := by
  have hpos : 1 ≤ Nat.ceil ((1000:ℝ)*t) := Nat.one_le_ceil_iff.mpr (by positivity)
  have hn : Nat.ceil ((1000:ℝ)*t) ≠ 0 := by omega
  have hh := (Nat.ceil_eq_iff hn).mp (rfl : Nat.ceil ((1000:ℝ)*t)=Nat.ceil ((1000:ℝ)*t))
  have he : Nat.ceil ((1000:ℝ)*t)-1+1=Nat.ceil ((1000:ℝ)*t) := Nat.sub_add_cancel hpos
  have her : ((Nat.ceil ((1000:ℝ)*t)-1:ℕ):ℝ)+1=(Nat.ceil ((1000:ℝ)*t):ℝ) := by
    exact_mod_cast he
  norm_num [index] at *
  rw [her]
  constructor <;> linarith

theorem stamp_age {t : ℝ} (ht : 0 ≤ t) (b : Bool) :
    0 ≤ stamp b t ∧ stamp b t ≤ t ∧ t-stamp b t ≤ 1/1000 := by
  have hnonneg : 0 ≤ stamp b t := by dsimp [stamp]; positivity
  refine ⟨hnonneg,?_⟩
  cases b
  · by_cases ht0 : t=0
    · subst t
      norm_num [stamp,index]
    · have hh := left_cell (lt_of_le_of_ne ht (Ne.symm ht0))
      norm_num [Nat.cast_add] at hh
      dsimp [stamp]
      constructor <;> linarith
  · have hh := right_cell ht
    norm_num [Nat.cast_add] at hh
    dsimp [stamp]
    constructor <;> linarith

def schedule (c : ℝ) : Schedule where
  sample n := n/1000
  dispatch n := n/1000
  measurement _ := ![c,0,0]
  index := index

theorem periodic_schedule (H c : ℝ) :
    IsSchedule H (schedule c) stamp (fun _ _ => ![c,0,0]) := by
  constructor
  · norm_num [schedule]
  · norm_num [schedule]
  · intro b
    cases b <;> norm_num [schedule,index]
  · intro n
    dsimp [schedule]
    exact ⟨by positivity,le_rfl⟩
  · intro m n hmn
    dsimp [schedule]
    exact div_lt_div_of_pos_right (by exact_mod_cast hmn) (by norm_num)
  · intro T
    obtain ⟨N,hN⟩ := exists_nat_gt (1000*T)
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    change (n:ℝ)/1000 ≤ T at hn
    change n<N
    have hh : (n:ℝ)<N := by linarith
    exact_mod_cast hh
  · intro t ht
    exact right_cell ht.1
  · intro t ht
    exact left_cell ht.1
  · intro b t ht
    rfl
  · intro b t ht
    rfl

/-- A genuine 1 ms periodic schedule gives an equilibrium execution on any
finite horizon, including horizons beyond entryTime. This is a nonvacuity
witness already inside the target box, not a capture experiment. -/
theorem periodic_sampled_execution (H c : ℝ) :
    IsSampledExecution H c (fun _ => ![c,0,0]) (fun _ _ => 8) (fun _ _ => 0)
      stamp (fun _ _ => ![c,0,0]) (schedule c) := by
  refine ⟨?_,periodic_schedule H c⟩
  constructor
  · exact continuousOn_const
  · intro b t ht
    exact stamp_age ht.1 b
  · intro b t ht
    norm_num
  · intro b t ht
    norm_num
  · intro b t ht
    norm_num
  · intro t ht i
    convert (hasDerivAt_const t (![c,0,0] i)).hasDerivWithinAt using 1 <;>
      fin_cases i <;> norm_num [rhs,command,clip]
  · intro t ht i
    convert (hasDerivAt_const t (![c,0,0] i)).hasDerivWithinAt using 1 <;>
      fin_cases i <;> norm_num [rhs,command,clip]

theorem six_second_instance (c : ℝ) :
    ∀ t ∈ Icc entryTime 6, weightedRadius (coordinates c (![c,0,0])) ≤ target := by
  have hi : ∀ i, |coordinates c (![c,0,0]) i| ≤ radius := by
    intro i
    fin_cases i <;> norm_num [coordinates,radius]
  have hh := sampled_finite_entry (by norm_num [entryTime] : entryTime ≤ (6:ℝ))
    (periodic_sampled_execution 6 c) hi
  intro t ht
  exact (hh.2.2 t ht).1

end LeanControls.WeightedEntry.Witness
