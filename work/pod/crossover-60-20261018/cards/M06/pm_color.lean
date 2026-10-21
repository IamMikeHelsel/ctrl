import Mathlib.Tactic
namespace CampaignM06Color
 theorem recolor_pair {α : Type} [DecidableEq α] (x y sx sy a : α)
 (hxy : x ≠ y) (hsxy : sx ≠ y) (hxsy : x ≠ sy) :
 (if x=a then sx else x) ≠ (if y=a then sy else y) := by
  by_cases hx : x=a <;> by_cases hy : y=a <;> simp_all
 theorem avoid_apex {α : Type} [DecidableEq α] (x sx a : α) (hs : sx≠a) :
 (if x=a then sx else x) ≠ a := by split_ifs <;> simp_all
 theorem preserve_avoid {α : Type} [DecidableEq α] (x sx a b : α) (hx : x≠b) (hs : sx≠b) :
 (if x=a then sx else x) ≠ b := by split_ifs <;> assumption
 theorem five_cycle (a b x0 x1 x2 x3 x4 : Fin 4) :
 a≠b → x0≠a → x0≠b → x1≠a → x1≠b → x2≠a → x2≠b → x3≠a → x3≠b → x4≠a → x4≠b →
 x0≠x1 → x1≠x2 → x2≠x3 → x3≠x4 → x0≠x4 → False := by omega
 theorem actual_mycielski_not_four_color (c : Fin 23 → Fin 4)
 (h0_1 : c 0 ≠ c 1)
 (h0_4 : c 0 ≠ c 4)
 (h0_6 : c 0 ≠ c 6)
 (h0_9 : c 0 ≠ c 9)
 (h0_12 : c 0 ≠ c 12)
 (h0_15 : c 0 ≠ c 15)
 (h0_17 : c 0 ≠ c 17)
 (h0_20 : c 0 ≠ c 20)
 (h1_2 : c 1 ≠ c 2)
 (h1_5 : c 1 ≠ c 5)
 (h1_7 : c 1 ≠ c 7)
 (h1_11 : c 1 ≠ c 11)
 (h1_13 : c 1 ≠ c 13)
 (h1_16 : c 1 ≠ c 16)
 (h1_18 : c 1 ≠ c 18)
 (h2_3 : c 2 ≠ c 3)
 (h2_6 : c 2 ≠ c 6)
 (h2_8 : c 2 ≠ c 8)
 (h2_12 : c 2 ≠ c 12)
 (h2_14 : c 2 ≠ c 14)
 (h2_17 : c 2 ≠ c 17)
 (h2_19 : c 2 ≠ c 19)
 (h3_4 : c 3 ≠ c 4)
 (h3_7 : c 3 ≠ c 7)
 (h3_9 : c 3 ≠ c 9)
 (h3_13 : c 3 ≠ c 13)
 (h3_15 : c 3 ≠ c 15)
 (h3_18 : c 3 ≠ c 18)
 (h3_20 : c 3 ≠ c 20)
 (h4_5 : c 4 ≠ c 5)
 (h4_8 : c 4 ≠ c 8)
 (h4_11 : c 4 ≠ c 11)
 (h4_14 : c 4 ≠ c 14)
 (h4_16 : c 4 ≠ c 16)
 (h4_19 : c 4 ≠ c 19)
 (h5_10 : c 5 ≠ c 10)
 (h5_12 : c 5 ≠ c 12)
 (h5_15 : c 5 ≠ c 15)
 (h5_21 : c 5 ≠ c 21)
 (h6_10 : c 6 ≠ c 10)
 (h6_11 : c 6 ≠ c 11)
 (h6_13 : c 6 ≠ c 13)
 (h6_21 : c 6 ≠ c 21)
 (h7_10 : c 7 ≠ c 10)
 (h7_12 : c 7 ≠ c 12)
 (h7_14 : c 7 ≠ c 14)
 (h7_21 : c 7 ≠ c 21)
 (h8_10 : c 8 ≠ c 10)
 (h8_13 : c 8 ≠ c 13)
 (h8_15 : c 8 ≠ c 15)
 (h8_21 : c 8 ≠ c 21)
 (h9_10 : c 9 ≠ c 10)
 (h9_11 : c 9 ≠ c 11)
 (h9_14 : c 9 ≠ c 14)
 (h9_21 : c 9 ≠ c 21)
 (h10_16 : c 10 ≠ c 16)
 (h10_17 : c 10 ≠ c 17)
 (h10_18 : c 10 ≠ c 18)
 (h10_19 : c 10 ≠ c 19)
 (h10_20 : c 10 ≠ c 20)
 (h11_22 : c 11 ≠ c 22)
 (h12_22 : c 12 ≠ c 22)
 (h13_22 : c 13 ≠ c 22)
 (h14_22 : c 14 ≠ c 22)
 (h15_22 : c 15 ≠ c 22)
 (h16_22 : c 16 ≠ c 22)
 (h17_22 : c 17 ≠ c 22)
 (h18_22 : c 18 ≠ c 22)
 (h19_22 : c 19 ≠ c 22)
 (h20_22 : c 20 ≠ c 22)
 (h21_22 : c 21 ≠ c 22)
 : False := by
  let d0 := if c 0=c 22 then c 11 else c 0
  have da0 : d0 ≠ c 22 := avoid_apex _ _ _ h11_22
  let d1 := if c 1=c 22 then c 12 else c 1
  have da1 : d1 ≠ c 22 := avoid_apex _ _ _ h12_22
  let d2 := if c 2=c 22 then c 13 else c 2
  have da2 : d2 ≠ c 22 := avoid_apex _ _ _ h13_22
  let d3 := if c 3=c 22 then c 14 else c 3
  have da3 : d3 ≠ c 22 := avoid_apex _ _ _ h14_22
  let d4 := if c 4=c 22 then c 15 else c 4
  have da4 : d4 ≠ c 22 := avoid_apex _ _ _ h15_22
  let d5 := if c 5=c 22 then c 16 else c 5
  have da5 : d5 ≠ c 22 := avoid_apex _ _ _ h16_22
  let d6 := if c 6=c 22 then c 17 else c 6
  have da6 : d6 ≠ c 22 := avoid_apex _ _ _ h17_22
  let d7 := if c 7=c 22 then c 18 else c 7
  have da7 : d7 ≠ c 22 := avoid_apex _ _ _ h18_22
  let d8 := if c 8=c 22 then c 19 else c 8
  have da8 : d8 ≠ c 22 := avoid_apex _ _ _ h19_22
  let d9 := if c 9=c 22 then c 20 else c 9
  have da9 : d9 ≠ c 22 := avoid_apex _ _ _ h20_22
  let d10 := if c 10=c 22 then c 21 else c 10
  have da10 : d10 ≠ c 22 := avoid_apex _ _ _ h21_22
  have hd0_1 : d0 ≠ d1 := recolor_pair _ _ _ _ _ h0_1 (Ne.symm h1_11) h0_12
  have hd0_4 : d0 ≠ d4 := recolor_pair _ _ _ _ _ h0_4 (Ne.symm h4_11) h0_15
  have hd0_6 : d0 ≠ d6 := recolor_pair _ _ _ _ _ h0_6 (Ne.symm h6_11) h0_17
  have hd0_9 : d0 ≠ d9 := recolor_pair _ _ _ _ _ h0_9 (Ne.symm h9_11) h0_20
  have hd1_2 : d1 ≠ d2 := recolor_pair _ _ _ _ _ h1_2 (Ne.symm h2_12) h1_13
  have hd1_5 : d1 ≠ d5 := recolor_pair _ _ _ _ _ h1_5 (Ne.symm h5_12) h1_16
  have hd1_7 : d1 ≠ d7 := recolor_pair _ _ _ _ _ h1_7 (Ne.symm h7_12) h1_18
  have hd2_3 : d2 ≠ d3 := recolor_pair _ _ _ _ _ h2_3 (Ne.symm h3_13) h2_14
  have hd2_6 : d2 ≠ d6 := recolor_pair _ _ _ _ _ h2_6 (Ne.symm h6_13) h2_17
  have hd2_8 : d2 ≠ d8 := recolor_pair _ _ _ _ _ h2_8 (Ne.symm h8_13) h2_19
  have hd3_4 : d3 ≠ d4 := recolor_pair _ _ _ _ _ h3_4 (Ne.symm h4_14) h3_15
  have hd3_7 : d3 ≠ d7 := recolor_pair _ _ _ _ _ h3_7 (Ne.symm h7_14) h3_18
  have hd3_9 : d3 ≠ d9 := recolor_pair _ _ _ _ _ h3_9 (Ne.symm h9_14) h3_20
  have hd4_5 : d4 ≠ d5 := recolor_pair _ _ _ _ _ h4_5 (Ne.symm h5_15) h4_16
  have hd4_8 : d4 ≠ d8 := recolor_pair _ _ _ _ _ h4_8 (Ne.symm h8_15) h4_19
  have hd5_10 : d5 ≠ d10 := recolor_pair _ _ _ _ _ h5_10 (Ne.symm h10_16) h5_21
  have hd6_10 : d6 ≠ d10 := recolor_pair _ _ _ _ _ h6_10 (Ne.symm h10_17) h6_21
  have hd7_10 : d7 ≠ d10 := recolor_pair _ _ _ _ _ h7_10 (Ne.symm h10_18) h7_21
  have hd8_10 : d8 ≠ d10 := recolor_pair _ _ _ _ _ h8_10 (Ne.symm h10_19) h8_21
  have hd9_10 : d9 ≠ d10 := recolor_pair _ _ _ _ _ h9_10 (Ne.symm h10_20) h9_21
  let e0 := if d0=d10 then d5 else d0
  have ea0 : e0 ≠ c 22 := preserve_avoid _ _ _ _ da0 da5
  have eb0 : e0 ≠ d10 := avoid_apex _ _ _ hd5_10
  let e1 := if d1=d10 then d6 else d1
  have ea1 : e1 ≠ c 22 := preserve_avoid _ _ _ _ da1 da6
  have eb1 : e1 ≠ d10 := avoid_apex _ _ _ hd6_10
  let e2 := if d2=d10 then d7 else d2
  have ea2 : e2 ≠ c 22 := preserve_avoid _ _ _ _ da2 da7
  have eb2 : e2 ≠ d10 := avoid_apex _ _ _ hd7_10
  let e3 := if d3=d10 then d8 else d3
  have ea3 : e3 ≠ c 22 := preserve_avoid _ _ _ _ da3 da8
  have eb3 : e3 ≠ d10 := avoid_apex _ _ _ hd8_10
  let e4 := if d4=d10 then d9 else d4
  have ea4 : e4 ≠ c 22 := preserve_avoid _ _ _ _ da4 da9
  have eb4 : e4 ≠ d10 := avoid_apex _ _ _ hd9_10
  have he0_1 : e0 ≠ e1 := recolor_pair _ _ _ _ _ hd0_1 (Ne.symm hd1_5) hd0_6
  have he0_4 : e0 ≠ e4 := recolor_pair _ _ _ _ _ hd0_4 (Ne.symm hd4_5) hd0_9
  have he1_2 : e1 ≠ e2 := recolor_pair _ _ _ _ _ hd1_2 (Ne.symm hd2_6) hd1_7
  have he2_3 : e2 ≠ e3 := recolor_pair _ _ _ _ _ hd2_3 (Ne.symm hd3_7) hd2_8
  have he3_4 : e3 ≠ e4 := recolor_pair _ _ _ _ _ hd3_4 (Ne.symm hd4_8) hd3_9
  exact five_cycle (c 22) d10 e0 e1 e2 e3 e4 (Ne.symm da10) ea0 eb0 ea1 eb1 ea2 eb2 ea3 eb3 ea4 eb4 he0_1 he1_2 he2_3 he3_4 he0_4
def targetEdges : List (Nat × Nat) := [(0,7), (0,11), (0,13), (0,14), (0,15), (1,6), (1,10), (1,12), (1,14), (1,15), (2,5), (2,9), (2,12), (2,13), (2,15), (3,4), (3,8), (3,12), (3,13), (3,14), (4,9), (4,10), (4,11), (4,15), (5,8), (5,10), (5,11), (5,14), (6,8), (6,9), (6,11), (6,13), (7,8), (7,9), (7,10), (7,12), (8,15), (9,14), (10,13), (11,12)]
def targetColors : List (Fin 4) := [0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3]
def tc (v : Fin 16) : Fin 4 := targetColors[v.val]!
def targetAdj (u v : Fin 16) : Prop := (u.val,v.val)∈targetEdges ∨ (v.val,u.val)∈targetEdges
instance (u v : Fin 16) : Decidable (targetAdj u v) := inferInstanceAs (Decidable (_ ∨ _))
theorem target_coloring : ∀ u v : Fin 16, targetAdj u v → tc u ≠ tc v := by decide
theorem no_target_hom (f : Fin 23 → Fin 16)
 (h0_1 : targetAdj (f 0) (f 1))
 (h0_4 : targetAdj (f 0) (f 4))
 (h0_6 : targetAdj (f 0) (f 6))
 (h0_9 : targetAdj (f 0) (f 9))
 (h0_12 : targetAdj (f 0) (f 12))
 (h0_15 : targetAdj (f 0) (f 15))
 (h0_17 : targetAdj (f 0) (f 17))
 (h0_20 : targetAdj (f 0) (f 20))
 (h1_2 : targetAdj (f 1) (f 2))
 (h1_5 : targetAdj (f 1) (f 5))
 (h1_7 : targetAdj (f 1) (f 7))
 (h1_11 : targetAdj (f 1) (f 11))
 (h1_13 : targetAdj (f 1) (f 13))
 (h1_16 : targetAdj (f 1) (f 16))
 (h1_18 : targetAdj (f 1) (f 18))
 (h2_3 : targetAdj (f 2) (f 3))
 (h2_6 : targetAdj (f 2) (f 6))
 (h2_8 : targetAdj (f 2) (f 8))
 (h2_12 : targetAdj (f 2) (f 12))
 (h2_14 : targetAdj (f 2) (f 14))
 (h2_17 : targetAdj (f 2) (f 17))
 (h2_19 : targetAdj (f 2) (f 19))
 (h3_4 : targetAdj (f 3) (f 4))
 (h3_7 : targetAdj (f 3) (f 7))
 (h3_9 : targetAdj (f 3) (f 9))
 (h3_13 : targetAdj (f 3) (f 13))
 (h3_15 : targetAdj (f 3) (f 15))
 (h3_18 : targetAdj (f 3) (f 18))
 (h3_20 : targetAdj (f 3) (f 20))
 (h4_5 : targetAdj (f 4) (f 5))
 (h4_8 : targetAdj (f 4) (f 8))
 (h4_11 : targetAdj (f 4) (f 11))
 (h4_14 : targetAdj (f 4) (f 14))
 (h4_16 : targetAdj (f 4) (f 16))
 (h4_19 : targetAdj (f 4) (f 19))
 (h5_10 : targetAdj (f 5) (f 10))
 (h5_12 : targetAdj (f 5) (f 12))
 (h5_15 : targetAdj (f 5) (f 15))
 (h5_21 : targetAdj (f 5) (f 21))
 (h6_10 : targetAdj (f 6) (f 10))
 (h6_11 : targetAdj (f 6) (f 11))
 (h6_13 : targetAdj (f 6) (f 13))
 (h6_21 : targetAdj (f 6) (f 21))
 (h7_10 : targetAdj (f 7) (f 10))
 (h7_12 : targetAdj (f 7) (f 12))
 (h7_14 : targetAdj (f 7) (f 14))
 (h7_21 : targetAdj (f 7) (f 21))
 (h8_10 : targetAdj (f 8) (f 10))
 (h8_13 : targetAdj (f 8) (f 13))
 (h8_15 : targetAdj (f 8) (f 15))
 (h8_21 : targetAdj (f 8) (f 21))
 (h9_10 : targetAdj (f 9) (f 10))
 (h9_11 : targetAdj (f 9) (f 11))
 (h9_14 : targetAdj (f 9) (f 14))
 (h9_21 : targetAdj (f 9) (f 21))
 (h10_16 : targetAdj (f 10) (f 16))
 (h10_17 : targetAdj (f 10) (f 17))
 (h10_18 : targetAdj (f 10) (f 18))
 (h10_19 : targetAdj (f 10) (f 19))
 (h10_20 : targetAdj (f 10) (f 20))
 (h11_22 : targetAdj (f 11) (f 22))
 (h12_22 : targetAdj (f 12) (f 22))
 (h13_22 : targetAdj (f 13) (f 22))
 (h14_22 : targetAdj (f 14) (f 22))
 (h15_22 : targetAdj (f 15) (f 22))
 (h16_22 : targetAdj (f 16) (f 22))
 (h17_22 : targetAdj (f 17) (f 22))
 (h18_22 : targetAdj (f 18) (f 22))
 (h19_22 : targetAdj (f 19) (f 22))
 (h20_22 : targetAdj (f 20) (f 22))
 (h21_22 : targetAdj (f 21) (f 22))
 : False := by
  apply actual_mycielski_not_four_color (fun v => tc (f v))
  · exact target_coloring _ _ h0_1
  · exact target_coloring _ _ h0_4
  · exact target_coloring _ _ h0_6
  · exact target_coloring _ _ h0_9
  · exact target_coloring _ _ h0_12
  · exact target_coloring _ _ h0_15
  · exact target_coloring _ _ h0_17
  · exact target_coloring _ _ h0_20
  · exact target_coloring _ _ h1_2
  · exact target_coloring _ _ h1_5
  · exact target_coloring _ _ h1_7
  · exact target_coloring _ _ h1_11
  · exact target_coloring _ _ h1_13
  · exact target_coloring _ _ h1_16
  · exact target_coloring _ _ h1_18
  · exact target_coloring _ _ h2_3
  · exact target_coloring _ _ h2_6
  · exact target_coloring _ _ h2_8
  · exact target_coloring _ _ h2_12
  · exact target_coloring _ _ h2_14
  · exact target_coloring _ _ h2_17
  · exact target_coloring _ _ h2_19
  · exact target_coloring _ _ h3_4
  · exact target_coloring _ _ h3_7
  · exact target_coloring _ _ h3_9
  · exact target_coloring _ _ h3_13
  · exact target_coloring _ _ h3_15
  · exact target_coloring _ _ h3_18
  · exact target_coloring _ _ h3_20
  · exact target_coloring _ _ h4_5
  · exact target_coloring _ _ h4_8
  · exact target_coloring _ _ h4_11
  · exact target_coloring _ _ h4_14
  · exact target_coloring _ _ h4_16
  · exact target_coloring _ _ h4_19
  · exact target_coloring _ _ h5_10
  · exact target_coloring _ _ h5_12
  · exact target_coloring _ _ h5_15
  · exact target_coloring _ _ h5_21
  · exact target_coloring _ _ h6_10
  · exact target_coloring _ _ h6_11
  · exact target_coloring _ _ h6_13
  · exact target_coloring _ _ h6_21
  · exact target_coloring _ _ h7_10
  · exact target_coloring _ _ h7_12
  · exact target_coloring _ _ h7_14
  · exact target_coloring _ _ h7_21
  · exact target_coloring _ _ h8_10
  · exact target_coloring _ _ h8_13
  · exact target_coloring _ _ h8_15
  · exact target_coloring _ _ h8_21
  · exact target_coloring _ _ h9_10
  · exact target_coloring _ _ h9_11
  · exact target_coloring _ _ h9_14
  · exact target_coloring _ _ h9_21
  · exact target_coloring _ _ h10_16
  · exact target_coloring _ _ h10_17
  · exact target_coloring _ _ h10_18
  · exact target_coloring _ _ h10_19
  · exact target_coloring _ _ h10_20
  · exact target_coloring _ _ h11_22
  · exact target_coloring _ _ h12_22
  · exact target_coloring _ _ h13_22
  · exact target_coloring _ _ h14_22
  · exact target_coloring _ _ h15_22
  · exact target_coloring _ _ h16_22
  · exact target_coloring _ _ h17_22
  · exact target_coloring _ _ h18_22
  · exact target_coloring _ _ h19_22
  · exact target_coloring _ _ h20_22
  · exact target_coloring _ _ h21_22
end CampaignM06Color
#print axioms CampaignM06Color.recolor_pair
#print axioms CampaignM06Color.five_cycle
#print axioms CampaignM06Color.actual_mycielski_not_four_color
#print axioms CampaignM06Color.target_coloring
#print axioms CampaignM06Color.no_target_hom
