import NativeBridge

noncomputable section
namespace NativeRational
open Set

@[simp] theorem pieceAt_cons_zero (s : Piece) (rest : List Piece) :
    pieceAt (s::rest) 0 = s := by simp [pieceAt]

@[simp] theorem pieceAt_cons_succ (s : Piece) (rest : List Piece) (k : ℕ) :
    pieceAt (s::rest) (k+1) = pieceAt rest k := by simp [pieceAt]

/-- Adjacent checked clock intervals cover from the first start to the last finish. -/
theorem chain_covers (s : Piece) (rest : List Piece) {H : ℚ} {time : ℝ}
    (hc : chainOK (s::rest) = true)
    (hlast : ((s::rest).getLast?.map Piece.finish) = some H)
    (hlo : (s.start : ℝ) ≤ time) (hhi : time ≤ (H : ℝ)) :
    ∃ k, k < (s::rest).length ∧
      time ∈ Icc ((pieceAt (s::rest) k).start : ℝ)
        ((pieceAt (s::rest) k).finish : ℝ) := by
  induction rest generalizing s with
  | nil =>
    have he : s.finish = H := by simpa using hlast
    exact ⟨0, by simp, by simpa [he] using And.intro hlo hhi⟩
  | cons next rest ih =>
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases ht : time ≤ (s.finish : ℝ)
    · exact ⟨0, by simp, by simpa using And.intro hlo ht⟩
    · have he : s.finish = next.start := hc.1.1
      have hn : (next.start : ℝ) ≤ time := by
        rw [← he]
        exact le_of_lt (lt_of_not_ge ht)
      have hl : ((next::rest).getLast?.map Piece.finish) = some H := by
        simpa using hlast
      obtain ⟨k,hk,htk⟩ := ih next hc.2 hl hn
      refine ⟨k+1, by simpa using Nat.succ_lt_succ hk, ?_⟩
      simpa using htk

/-- Every absolute real time in the checked horizon belongs to a recorded piece. -/
theorem checked_time_coverage {H : ℚ} {xs : List Piece} (h : check H xs = true)
    {time : ℝ} (ht : time ∈ Icc 0 (H : ℝ)) :
    ∃ k, k < xs.length ∧
      time ∈ Icc ((pieceAt xs k).start : ℝ) ((pieceAt xs k).finish : ℝ) := by
  cases xs with
  | nil => simp [check] at h
  | cons s rest =>
    have hc := check_chain h
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
    have hs : s.start = 0 := h.1.1.1.1
    apply chain_covers s rest hc h.2
    · simpa [hs] using ht.1
    · exact ht.2

/-- Coverage also gives a valid local time offset for the cubic tracking theorem. -/
theorem checked_local_offset {H : ℚ} {xs : List Piece} (h : check H xs = true)
    {time : ℝ} (ht : time ∈ Icc 0 (H : ℝ)) :
    ∃ k, k < xs.length ∧
      time ∈ Icc ((pieceAt xs k).start : ℝ) ((pieceAt xs k).finish : ℝ) ∧
      time - ((pieceAt xs k).start : ℝ) ∈ Icc 0 (realDuration xs k) := by
  obtain ⟨k,hk,hlo,hhi⟩ := checked_time_coverage h ht
  refine ⟨k,hk,⟨hlo,hhi⟩,?_,?_⟩
  · linarith
  · dsimp [realDuration, duration]
    push_cast
    linarith

end NativeRational
