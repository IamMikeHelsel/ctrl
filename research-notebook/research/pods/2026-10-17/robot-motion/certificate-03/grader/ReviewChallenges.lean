import Composition
namespace IndependentRobotReview
open RobotMotion
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem oracle_0_boundary : check 1 0 (5/7) [] = true := by decide +kernel
theorem oracle_0_below : check 1 (-1/997) (5/7) [] = false := by decide +kernel
theorem oracle_1_boundary : check (1/3) 0 1 [((-1/3),(-2/11))] = true := by decide +kernel
theorem oracle_1_below : check (1/3) (-1/997) 1 [((-1/3),(-2/11))] = false := by decide +kernel
theorem oracle_2_boundary : check (1/5) (1000/11) (-3/7) [((5/3),(-4/11)),((-4/3),(-2/11))] = true := by decide +kernel
theorem oracle_2_below : check (1/5) (996989/10967) (-3/7) [((5/3),(-4/11)),((-4/3),(-2/11))] = false := by decide +kernel
theorem oracle_3_boundary : check (1/5) (750/11) 1 [((1/3),(3/11)),((10/3),(-3/11)),((1/3),(2/11))] = true := by decide +kernel
theorem oracle_3_below : check (1/5) (747739/10967) 1 [((1/3),(3/11)),((10/3),(-3/11)),((1/3),(2/11))] = false := by decide +kernel
theorem oracle_4_boundary : check (1/3) (216/11) (3/7) [((-1/3),(4/11)),((5/3),(2/11)),(1,0),((7/3),(4/11))] = true := by decide +kernel
theorem oracle_4_below : check (1/3) (215341/10967) (3/7) [((-1/3),(4/11)),((5/3),(2/11)),(1,0),((7/3),(4/11))] = false := by decide +kernel
theorem oracle_5_boundary : check (1/3) 0 (10/7) [] = true := by decide +kernel
theorem oracle_5_below : check (1/3) (-1/997) (10/7) [] = false := by decide +kernel
theorem oracle_6_boundary : check (1/5) (750/11) (17/7) [(4,(-3/11))] = true := by decide +kernel
theorem oracle_6_below : check (1/5) (747739/10967) (17/7) [(4,(-3/11))] = false := by decide +kernel
theorem oracle_7_boundary : check 1 (4/33) 2 [(-1,(-1/11)),((1/3),(-1/11))] = true := by decide +kernel
theorem oracle_7_below : check 1 (3955/32901) 2 [(-1,(-1/11)),((1/3),(-1/11))] = false := by decide +kernel
theorem oracle_8_boundary : check (1/3) (108/11) (16/7) [((2/3),(-1/11)),((1/3),(-2/11)),((7/3),(-2/11))] = true := by decide +kernel
theorem oracle_8_below : check (1/3) (107665/10967) (16/7) [((2/3),(-1/11)),((1/3),(-2/11)),((7/3),(-2/11))] = false := by decide +kernel
theorem oracle_9_boundary : check (1/5) (750/11) (16/7) [((2/3),(2/11)),((11/3),(-1/11)),(2,(3/11)),((1/3),0)] = true := by decide +kernel
theorem oracle_9_below : check (1/5) (747739/10967) (16/7) [((2/3),(2/11)),((11/3),(-1/11)),(2,(3/11)),((1/3),0)] = false := by decide +kernel
theorem oracle_10_boundary : check (1/5) 0 0 [] = true := by decide +kernel
theorem oracle_10_below : check (1/5) (-1/997) 0 [] = false := by decide +kernel
theorem oracle_11_boundary : check (1/3) (108/11) 2 [((7/3),(-2/11))] = true := by decide +kernel
theorem oracle_11_below : check (1/3) (107665/10967) 2 [((7/3),(-2/11))] = false := by decide +kernel
theorem oracle_12_boundary : check 1 (4/11) (15/7) [((-4/3),(1/11)),((5/3),(2/11))] = true := by decide +kernel
theorem oracle_12_below : check 1 (3977/10967) (15/7) [((-4/3),(1/11)),((5/3),(2/11))] = false := by decide +kernel
theorem oracle_13_boundary : check 1 (8/11) (-1/7) [((-4/3),(4/11)),((11/3),(-3/11)),(0,0)] = true := by decide +kernel
theorem oracle_13_below : check 1 (7965/10967) (-1/7) [((-4/3),(4/11)),((11/3),(-3/11)),(0,0)] = false := by decide +kernel
theorem oracle_14_boundary : check 1 1 (13/7) [((1/3),(-1/11)),((11/3),(-1/11)),((2/3),(2/11)),((2/3),(4/11))] = true := by decide +kernel
theorem oracle_14_below : check 1 (996/997) (13/7) [((1/3),(-1/11)),((11/3),(-1/11)),((2/3),(2/11)),((2/3),(4/11))] = false := by decide +kernel
theorem oracle_15_boundary : check 1 0 (6/7) [] = true := by decide +kernel
theorem oracle_15_below : check 1 (-1/997) (6/7) [] = false := by decide +kernel
theorem oracle_16_boundary : check 1 (13/77) (26/7) [((1/3),(3/11))] = true := by decide +kernel
theorem oracle_16_below : check 1 (12884/76769) (26/7) [((1/3),(3/11))] = false := by decide +kernel
theorem oracle_17_boundary : check (1/3) 0 (27/7) [((1/3),(-1/11)),(0,(1/11))] = true := by decide +kernel
theorem oracle_17_below : check (1/3) (-1/997) (27/7) [((1/3),(-1/11)),(0,(1/11))] = false := by decide +kernel
theorem oracle_18_boundary : check (1/5) (500/11) (13/7) [((7/3),(-2/11)),((2/3),(-3/11)),((1/3),(-2/11))] = true := by decide +kernel
theorem oracle_18_below : check (1/5) (498489/10967) (13/7) [((7/3),(-2/11)),((2/3),(-3/11)),((1/3),(-2/11))] = false := by decide +kernel
theorem oracle_19_boundary : check (1/5) (750/11) 2 [((7/3),(3/11)),((10/3),(-1/11)),((8/3),0),((8/3),0)] = true := by decide +kernel
theorem oracle_19_below : check (1/5) (747739/10967) 2 [((7/3),(3/11)),((10/3),(-1/11)),((8/3),0),((8/3),0)] = false := by decide +kernel
theorem oracle_20_boundary : check 1 0 2 [] = true := by decide +kernel
theorem oracle_20_below : check 1 (-1/997) 2 [] = false := by decide +kernel
theorem oracle_21_boundary : check (1/5) (250/11) (-1/7) [((4/3),(1/11))] = true := by decide +kernel
theorem oracle_21_below : check (1/5) (249239/10967) (-1/7) [((4/3),(1/11))] = false := by decide +kernel
theorem oracle_22_boundary : check (1/3) (216/77) (3/7) [((-1/3),(-1/11)),(-1,(4/11))] = true := by decide +kernel
theorem oracle_22_below : check (1/3) (215275/76769) (3/7) [((-1/3),(-1/11)),(-1,(4/11))] = false := by decide +kernel
theorem oracle_23_boundary : check 1 (35/33) (-3/7) [((4/3),(3/11)),(3,(1/11)),((4/3),(3/11))] = true := by decide +kernel
theorem oracle_23_below : check 1 (34862/32901) (-3/7) [((4/3),(3/11)),(3,(1/11)),((4/3),(3/11))] = false := by decide +kernel
theorem oracle_24_boundary : check (1/5) (250/11) (9/7) [((10/3),(-1/11)),((1/3),(-3/11)),(2,(1/11)),((-1/3),(1/11))] = true := by decide +kernel
theorem oracle_24_below : check (1/5) (249239/10967) (9/7) [((10/3),(-1/11)),((1/3),(-3/11)),(2,(1/11)),((-1/3),(1/11))] = false := by decide +kernel
theorem oracle_25_boundary : check (1/5) 0 (29/7) [] = true := by decide +kernel
theorem oracle_25_below : check (1/5) (-1/997) (29/7) [] = false := by decide +kernel
theorem oracle_26_boundary : check (1/3) 0 (16/7) [((-4/3),(-1/11))] = true := by decide +kernel
theorem oracle_26_below : check (1/3) (-1/997) (16/7) [((-4/3),(-1/11))] = false := by decide +kernel
theorem oracle_27_boundary : check (1/3) (162/11) (13/7) [((4/3),(3/11)),(3,(-1/11))] = true := by decide +kernel
theorem oracle_27_below : check (1/3) (161503/10967) (13/7) [((4/3),(3/11)),(3,(-1/11))] = false := by decide +kernel
theorem oracle_28_boundary : check (1/3) (162/11) (25/7) [((11/3),(3/11)),((-4/3),(-2/11)),((8/3),(-2/11))] = true := by decide +kernel
theorem oracle_28_below : check (1/3) (161503/10967) (25/7) [((11/3),(3/11)),((-4/3),(-2/11)),((8/3),(-2/11))] = false := by decide +kernel
theorem oracle_29_boundary : check (1/3) (54/11) (2/7) [(4,(1/11)),((11/3),0),((-4/3),0),((4/3),0)] = true := by decide +kernel
theorem oracle_29_below : check (1/3) (53827/10967) (2/7) [(4,(1/11)),((11/3),0),((-4/3),0),((4/3),0)] = false := by decide +kernel
theorem oracle_30_boundary : check (1/3) 0 (1/7) [] = true := by decide +kernel
theorem oracle_30_below : check (1/3) (-1/997) (1/7) [] = false := by decide +kernel
theorem oracle_31_boundary : check (1/3) 0 (30/7) [(0,(1/11))] = true := by decide +kernel
theorem oracle_31_below : check (1/3) (-1/997) (30/7) [(0,(1/11))] = false := by decide +kernel
theorem oracle_32_boundary : check (1/3) (162/11) (24/7) [((4/3),(3/11)),(4,(3/11))] = true := by decide +kernel
theorem oracle_32_below : check (1/3) (161503/10967) (24/7) [((4/3),(3/11)),(4,(3/11))] = false := by decide +kernel
theorem oracle_33_boundary : check (1/5) (500/11) (22/7) [(0,(4/11)),((8/3),(4/11)),((11/3),(2/11))] = true := by decide +kernel
theorem oracle_33_below : check (1/5) (498489/10967) (22/7) [(0,(4/11)),((8/3),(4/11)),((11/3),(2/11))] = false := by decide +kernel
theorem oracle_34_boundary : check 1 (17/33) (24/7) [(1,(3/11)),((2/3),(-1/11)),(2,(2/11)),((7/3),(-3/11))] = true := by decide +kernel
theorem oracle_34_below : check 1 (16916/32901) (24/7) [(1,(3/11)),((2/3),(-1/11)),(2,(2/11)),((7/3),(-3/11))] = false := by decide +kernel
theorem oracle_35_boundary : check 1 0 (-1/7) [] = true := by decide +kernel
theorem oracle_35_below : check 1 (-1/997) (-1/7) [] = false := by decide +kernel
theorem oracle_36_boundary : check 1 (2/11) 3 [(1,(1/11))] = true := by decide +kernel
theorem oracle_36_below : check 1 (1983/10967) 3 [(1,(1/11))] = false := by decide +kernel
theorem oracle_37_boundary : check (1/5) (250/11) (18/7) [((4/3),0),((7/3),(1/11))] = true := by decide +kernel
theorem oracle_37_below : check (1/5) (249239/10967) (18/7) [((4/3),0),((7/3),(1/11))] = false := by decide +kernel
theorem oracle_38_boundary : check (1/5) 0 (19/7) [(1,(4/11)),((2/3),0),(-1,(1/11))] = true := by decide +kernel
theorem oracle_38_below : check (1/5) (-1/997) (19/7) [(1,(4/11)),((2/3),0),(-1,(1/11))] = false := by decide +kernel
theorem oracle_39_boundary : check 1 (6/11) (10/7) [((4/3),(3/11)),((1/3),(2/11)),((10/3),0),((10/3),(-3/11))] = true := by decide +kernel
theorem oracle_39_below : check 1 (5971/10967) (10/7) [((4/3),(3/11)),((1/3),(2/11)),((10/3),0),((10/3),(-3/11))] = false := by decide +kernel
theorem oracle_40_boundary : check (1/5) 0 4 [] = true := by decide +kernel
theorem oracle_40_below : check (1/5) (-1/997) 4 [] = false := by decide +kernel
theorem oracle_41_boundary : check 1 (2/11) 2 [(-1,(-2/11))] = true := by decide +kernel
theorem oracle_41_below : check 1 (1983/10967) 2 [(-1,(-2/11))] = false := by decide +kernel
theorem oracle_42_boundary : check (1/5) (250/11) (-1/7) [((-4/3),(-4/11)),((11/3),(-1/11))] = true := by decide +kernel
theorem oracle_42_below : check (1/5) (249239/10967) (-1/7) [((-4/3),(-4/11)),((11/3),(-1/11))] = false := by decide +kernel
theorem oracle_43_boundary : check 1 (6/11) (1/7) [((-1/3),(3/11)),((1/3),(1/11)),(3,(2/11))] = true := by decide +kernel
theorem oracle_43_below : check 1 (5971/10967) (1/7) [((-1/3),(3/11)),((1/3),(1/11)),(3,(2/11))] = false := by decide +kernel
theorem oracle_44_boundary : check (1/5) (3500/33) (2/7) [(3,(-4/11)),((10/3),(3/11)),((10/3),(1/11)),((2/3),(-2/11))] = true := by decide +kernel
theorem oracle_44_below : check (1/5) (3489467/32901) (2/7) [(3,(-4/11)),((10/3),(3/11)),((10/3),(1/11)),((2/3),(-2/11))] = false := by decide +kernel
theorem oracle_45_boundary : check (1/3) 0 3 [] = true := by decide +kernel
theorem oracle_45_below : check (1/3) (-1/997) 3 [] = false := by decide +kernel
theorem oracle_46_boundary : check 1 (2/11) 1 [(1,(1/11))] = true := by decide +kernel
theorem oracle_46_below : check 1 (1983/10967) 1 [(1,(1/11))] = false := by decide +kernel
theorem oracle_47_boundary : check 1 (7/11) (25/7) [((4/3),(1/11)),((5/3),(-4/11))] = true := by decide +kernel
theorem oracle_47_below : check 1 (6968/10967) (25/7) [((4/3),(1/11)),((5/3),(-4/11))] = false := by decide +kernel
theorem invalid_width : check 0 5 0 [(0,1)] = false := by decide +kernel
theorem negative_width : check (-1) 5 0 [] = false := by decide +kernel
theorem negative_limit : check 1 (-1) 0 [] = false := by decide +kernel
theorem duplicate_unsorted : check 1 0 0 [(3,100),(0,20),(3,-100),(0,-20)] = true := by decide +kernel
theorem end_tail_exact : check 1 0 4 [(0,1)] = true := by decide +kernel
theorem just_before_tail_rejects : check 1 0 (399/100) [(0,1)] = false := by decide +kernel
theorem real_tail_interval (t : ℝ) (ht : (7/2:ℝ) ≤ t) : |jerk 1 (realEvents [(0,1)]) t| ≤ (1/2:ℝ) := by
  have hfuture := (check_real_iff 1 (1/2) (7/2) [(0,1)]).mp (by decide +kernel) |>.2.2 t (by norm_num; exact ht)
  norm_num at hfuture ⊢
  exact hfuture
def proposals : List Proposal := [⟨0,1,1/500⟩,⟨1/10,1/2,1/250⟩,⟨1/5,2,0⟩,⟨3/10,3,0⟩,⟨1/4,4,1/1000⟩,⟨2/5,4,1/20⟩]
theorem scheduled_events : (run (1/5) (15/2) (initial 0) proposals).events = [(1,1/500),(2,-1/500)] := by decide +kernel
theorem scheduled_target : (run (1/5) (15/2) (initial 0) proposals).target = 0 := by decide +kernel
theorem scheduled_admission_clock : (run (1/5) (15/2) (initial 0) proposals).lastAdmission = 2/5 := by decide +kernel
theorem scheduled_execution_clock : (run (1/5) (15/2) (initial 0) proposals).lastExecution = 2 := by decide +kernel
def seq0 : SequencedState := ⟨initial 0,-1⟩
def seq1 := submit (1/5) (15/2) seq0 50 0 ⟨0,0,1/20⟩
def seq2 := submit (1/5) (15/2) seq1 49 (1/10) ⟨1/5,1/5,1/1000⟩
def seq3 := submit (1/5) (15/2) seq2 51 (2/5) ⟨3/10,3/10,1/1000⟩
def seq4 := submit (1/5) (15/2) seq3 51 (2/5) ⟨2/5,2/5,1/1000⟩
theorem rejected_watermark : seq1.watermark = 50 ∧ seq1.motion.events = [] := by decide +kernel
theorem stale_after_rejection : seq2 = seq1 := by decide +kernel
theorem premature_after_rejection : seq3 = seq2 := by decide +kernel
theorem ready_recovery : seq4.watermark = 51 ∧ seq4.motion.events = [(2/5,1/1000)] := by decide +kernel
theorem future_prefix_at_commit : referenceJet 9 (1/5) [(1,1/500)] 0 = referenceJet 9 (1/5) [] 0 := by
  exact prefix_jet (by norm_num) (by norm_num : (0:ℝ) ≤ 1) 9 (1/500) [] (by norm_num)
end IndependentRobotReview
