import VelocityFixtures
open RobotMotion RobotMotion.AccelerationAdmission RobotMotion.VelocityAdmission
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem oracle_decision_0_0 : checkVelocity (1/1) (0/1) (0/1) [] = true := by decide +kernel
theorem oracle_decision_0_1 : checkVelocity (1/1) (0/1) (0/1) [] = true := by decide +kernel
theorem oracle_decision_0_2 : checkVelocity (1/1) (0/1) (0/1) [] = true := by decide +kernel
theorem oracle_jet_0_0 : qVelocity (1/1) [] (0/1) = (0/1) ∧ qAcceleration (1/1) [] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_0_1 : qVelocity (1/1) [] (1/7) = (0/1) ∧ qAcceleration (1/1) [] (1/7) = (0/1) := by decide +kernel
theorem oracle_decision_1_0 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(1/1)),((1/1),(-1/1))] = false := by decide +kernel
theorem oracle_decision_1_1 : checkVelocity (1/1) (2/3) (0/1) [((0/1),(1/1)),((1/1),(-1/1))] = true := by decide +kernel
theorem oracle_decision_1_2 : checkVelocity (1/1) (1991/2991) (0/1) [((0/1),(1/1)),((1/1),(-1/1))] = false := by decide +kernel
theorem oracle_jet_1_0 : qVelocity (1/1) [((0/1),(1/1)),((1/1),(-1/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/1),(-1/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_1_1 : qVelocity (1/1) [((0/1),(1/1)),((1/1),(-1/1))] (1/7) = (1/2058) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/1),(-1/1))] (1/7) = (1/98) := by decide +kernel
theorem oracle_decision_2_0 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(1/1)),((1/4),(-1/1))] = false := by decide +kernel
theorem oracle_decision_2_1 : checkVelocity (1/1) (3/16) (0/1) [((0/1),(1/1)),((1/4),(-1/1))] = true := by decide +kernel
theorem oracle_decision_2_2 : checkVelocity (1/1) (2975/15952) (0/1) [((0/1),(1/1)),((1/4),(-1/1))] = false := by decide +kernel
theorem oracle_jet_2_0 : qVelocity (1/1) [((0/1),(1/1)),((1/4),(-1/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/4),(-1/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_2_1 : qVelocity (1/1) [((0/1),(1/1)),((1/4),(-1/1))] (1/7) = (1/2058) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/4),(-1/1))] (1/7) = (1/98) := by decide +kernel
theorem oracle_decision_3_0 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] = false := by decide +kernel
theorem oracle_decision_3_1 : checkVelocity (1/1) (1/6) (0/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] = true := by decide +kernel
theorem oracle_decision_3_2 : checkVelocity (1/1) (991/5982) (0/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] = false := by decide +kernel
theorem oracle_jet_3_0 : qVelocity (1/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_3_1 : qVelocity (1/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] (1/7) = (1/2058) ∧ qAcceleration (1/1) [((0/1),(1/1)),((1/4),(-1/1)),((1/2),(0/1)),((3/4),(0/1))] (1/7) = (1/98) := by decide +kernel
theorem oracle_decision_4_0 : checkVelocity (1/1) (0/1) (7/2) [((0/1),(1/1))] = false := by decide +kernel
theorem oracle_decision_4_1 : checkVelocity (1/1) (1/48) (7/2) [((0/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_4_2 : checkVelocity (1/1) (949/47856) (7/2) [((0/1),(1/1))] = false := by decide +kernel
theorem oracle_jet_4_0 : qVelocity (1/1) [((0/1),(1/1))] (7/2) = (1/48) ∧ qAcceleration (1/1) [((0/1),(1/1))] (7/2) = (-1/8) := by decide +kernel
theorem oracle_jet_4_1 : qVelocity (1/1) [((0/1),(1/1))] (51/14) = (125/16464) ∧ qAcceleration (1/1) [((0/1),(1/1))] (51/14) = (-25/392) := by decide +kernel
theorem oracle_decision_5_0 : checkVelocity (1/1) (0/1) (4/1) [((0/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_5_1 : checkVelocity (1/1) (0/1) (4/1) [((0/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_5_2 : checkVelocity (1/1) (0/1) (4/1) [((0/1),(1/1))] = true := by decide +kernel
theorem oracle_jet_5_0 : qVelocity (1/1) [((0/1),(1/1))] (4/1) = (0/1) ∧ qAcceleration (1/1) [((0/1),(1/1))] (4/1) = (0/1) := by decide +kernel
theorem oracle_jet_5_1 : qVelocity (1/1) [((0/1),(1/1))] (29/7) = (0/1) ∧ qAcceleration (1/1) [((0/1),(1/1))] (29/7) = (0/1) := by decide +kernel
theorem oracle_decision_6_0 : checkVelocity (1/1) (0/1) (0/1) [((10/1),(1/1))] = false := by decide +kernel
theorem oracle_decision_6_1 : checkVelocity (1/1) (2/3) (0/1) [((10/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_6_2 : checkVelocity (1/1) (1991/2991) (0/1) [((10/1),(1/1))] = false := by decide +kernel
theorem oracle_jet_6_0 : qVelocity (1/1) [((10/1),(1/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((10/1),(1/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_6_1 : qVelocity (1/1) [((10/1),(1/1))] (1/7) = (0/1) ∧ qAcceleration (1/1) [((10/1),(1/1))] (1/7) = (0/1) := by decide +kernel
theorem oracle_decision_7_0 : checkVelocity (1/1) (0/1) (0/1) [((10/1),(-1/1)),((0/1),(1/1))] = false := by decide +kernel
theorem oracle_decision_7_1 : checkVelocity (1/1) (2/3) (0/1) [((10/1),(-1/1)),((0/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_7_2 : checkVelocity (1/1) (1991/2991) (0/1) [((10/1),(-1/1)),((0/1),(1/1))] = false := by decide +kernel
theorem oracle_jet_7_0 : qVelocity (1/1) [((10/1),(-1/1)),((0/1),(1/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((10/1),(-1/1)),((0/1),(1/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_7_1 : qVelocity (1/1) [((10/1),(-1/1)),((0/1),(1/1))] (1/7) = (1/2058) ∧ qAcceleration (1/1) [((10/1),(-1/1)),((0/1),(1/1))] (1/7) = (1/98) := by decide +kernel
theorem oracle_decision_8_0 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(100/1)),((0/1),(-100/1))] = true := by decide +kernel
theorem oracle_decision_8_1 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(100/1)),((0/1),(-100/1))] = true := by decide +kernel
theorem oracle_decision_8_2 : checkVelocity (1/1) (0/1) (0/1) [((0/1),(100/1)),((0/1),(-100/1))] = true := by decide +kernel
theorem oracle_jet_8_0 : qVelocity (1/1) [((0/1),(100/1)),((0/1),(-100/1))] (0/1) = (0/1) ∧ qAcceleration (1/1) [((0/1),(100/1)),((0/1),(-100/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_8_1 : qVelocity (1/1) [((0/1),(100/1)),((0/1),(-100/1))] (1/7) = (0/1) ∧ qAcceleration (1/1) [((0/1),(100/1)),((0/1),(-100/1))] (1/7) = (0/1) := by decide +kernel
theorem oracle_decision_9_0 : checkVelocity (1/5) (0/1) (13/25) [((11/50),(1/50)),((31/50),(-1/50))] = false := by decide +kernel
theorem oracle_decision_9_1 : checkVelocity (1/5) (1/15) (13/25) [((11/50),(1/50)),((31/50),(-1/50))] = true := by decide +kernel
theorem oracle_decision_9_2 : checkVelocity (1/5) (982/14955) (13/25) [((11/50),(1/50)),((31/50),(-1/50))] = false := by decide +kernel
theorem oracle_jet_9_0 : qVelocity (1/5) [((11/50),(1/50)),((31/50),(-1/50))] (13/25) = (23/480) ∧ qAcceleration (1/5) [((11/50),(1/50)),((31/50),(-1/50))] (13/25) = (5/16) := by decide +kernel
theorem oracle_jet_9_1 : qVelocity (1/5) [((11/50),(1/50)),((31/50),(-1/50))] (96/175) = (9251/164640) ∧ qAcceleration (1/5) [((11/50),(1/50)),((31/50),(-1/50))] (96/175) = (205/784) := by decide +kernel
theorem oracle_decision_10_0 : checkVelocity (2/7) (0/1) (-2/1) [((-3/1),(-7/5)),((-2/1),(3/5))] = false := by decide +kernel
theorem oracle_decision_10_1 : checkVelocity (2/7) (7/5) (-2/1) [((-3/1),(-7/5)),((-2/1),(3/5))] = true := by decide +kernel
theorem oracle_decision_10_2 : checkVelocity (2/7) (6974/4985) (-2/1) [((-3/1),(-7/5)),((-2/1),(3/5))] = false := by decide +kernel
theorem oracle_jet_10_0 : qVelocity (2/7) [((-3/1),(-7/5)),((-2/1),(3/5))] (-2/1) = (-49/480) ∧ qAcceleration (2/7) [((-3/1),(-7/5)),((-2/1),(3/5))] (-2/1) = (343/160) := by decide +kernel
theorem oracle_jet_10_1 : qVelocity (2/7) [((-3/1),(-7/5)),((-2/1),(3/5))] (-96/49) = (-851/23520) ∧ qAcceleration (2/7) [((-3/1),(-7/5)),((-2/1),(3/5))] (-96/49) = (187/160) := by decide +kernel
theorem oracle_decision_11_0 : checkVelocity (1/3) (0/1) (1/7) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] = true := by decide +kernel
theorem oracle_decision_11_1 : checkVelocity (1/3) (0/1) (1/7) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] = true := by decide +kernel
theorem oracle_decision_11_2 : checkVelocity (1/3) (0/1) (1/7) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] = true := by decide +kernel
theorem oracle_jet_11_0 : qVelocity (1/3) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] (1/7) = (0/1) ∧ qAcceleration (1/3) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] (1/7) = (0/1) := by decide +kernel
theorem oracle_jet_11_1 : qVelocity (1/3) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] (4/21) = (0/1) ∧ qAcceleration (1/3) [((0/1),(0/1)),((1/7),(0/1)),((2/1),(0/1))] (4/21) = (0/1) := by decide +kernel
theorem oracle_decision_12_0 : checkVelocity (1/4) (0/1) (1/4) [((1/4),(1/9)),((1/4),(2/9))] = false := by decide +kernel
theorem oracle_decision_12_1 : checkVelocity (1/4) (8/9) (1/4) [((1/4),(1/9)),((1/4),(2/9))] = true := by decide +kernel
theorem oracle_decision_12_2 : checkVelocity (1/4) (7967/8973) (1/4) [((1/4),(1/9)),((1/4),(2/9))] = false := by decide +kernel
theorem oracle_jet_12_0 : qVelocity (1/4) [((1/4),(1/9)),((1/4),(2/9))] (1/4) = (0/1) ∧ qAcceleration (1/4) [((1/4),(1/9)),((1/4),(2/9))] (1/4) = (0/1) := by decide +kernel
theorem oracle_jet_12_1 : qVelocity (1/4) [((1/4),(1/9)),((1/4),(2/9))] (2/7) = (2/3087) ∧ qAcceleration (1/4) [((1/4),(1/9)),((1/4),(2/9))] (2/7) = (8/147) := by decide +kernel
theorem oracle_decision_13_0 : checkVelocity (7/5) (0/1) (0/1) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_13_1 : checkVelocity (7/5) (0/1) (0/1) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] = true := by decide +kernel
theorem oracle_decision_13_2 : checkVelocity (7/5) (0/1) (0/1) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] = true := by decide +kernel
theorem oracle_jet_13_0 : qVelocity (7/5) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] (0/1) = (0/1) ∧ qAcceleration (7/5) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_13_1 : qVelocity (7/5) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] (1/5) = (0/1) ∧ qAcceleration (7/5) [((-4/1),(1/1)),((4/1),(-1/1)),((-4/1),(-1/1)),((4/1),(1/1))] (1/5) = (0/1) := by decide +kernel
theorem oracle_decision_14_0 : checkVelocity (1/2) (0/1) (0/1) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] = false := by decide +kernel
theorem oracle_decision_14_1 : checkVelocity (1/2) (7/15) (0/1) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] = true := by decide +kernel
theorem oracle_decision_14_2 : checkVelocity (1/2) (6964/14955) (0/1) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] = false := by decide +kernel
theorem oracle_jet_14_0 : qVelocity (1/2) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] (0/1) = (-1/3) ∧ qAcceleration (1/2) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] (0/1) = (0/1) := by decide +kernel
theorem oracle_jet_14_1 : qVelocity (1/2) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] (1/14) = (-3329/10290) ∧ qAcceleration (1/2) [((-1/1),(-1/4)),((0/1),(3/20)),((5/4),(-1/5)),((13/4),(-3/20)),((11/4),(-1/20)),((0/1),(1/5))] (1/14) = (66/245) := by decide +kernel
theorem oracle_decision_15_0 : checkVelocity (1/1) (0/1) (3/4) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] = false := by decide +kernel
theorem oracle_decision_15_1 : checkVelocity (1/1) (941/7680) (3/4) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] = true := by decide +kernel
theorem oracle_decision_15_2 : checkVelocity (1/1) (930497/7656960) (3/4) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] = false := by decide +kernel
theorem oracle_jet_15_0 : qVelocity (1/1) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] (3/4) = (-941/7680) ∧ qAcceleration (1/1) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] (3/4) = (51/640) := by decide +kernel
theorem oracle_jet_15_1 : qVelocity (1/1) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] (25/28) = (-95741/878080) ∧ qAcceleration (1/1) [((1/2),(-1/20)),((7/2),(-1/10)),((-3/2),(-1/5)),((17/4),(1/5)),((15/4),(-1/5)),((9/4),(1/10))] (25/28) = (671/6272) := by decide +kernel
theorem oracle_decision_16_0 : checkVelocity (1/5) (0/1) (1/1) [((-5/4),(1/20))] = true := by decide +kernel
theorem oracle_decision_16_1 : checkVelocity (1/5) (0/1) (1/1) [((-5/4),(1/20))] = true := by decide +kernel
theorem oracle_decision_16_2 : checkVelocity (1/5) (0/1) (1/1) [((-5/4),(1/20))] = true := by decide +kernel
theorem oracle_jet_16_0 : qVelocity (1/5) [((-5/4),(1/20))] (1/1) = (0/1) ∧ qAcceleration (1/5) [((-5/4),(1/20))] (1/1) = (0/1) := by decide +kernel
theorem oracle_jet_16_1 : qVelocity (1/5) [((-5/4),(1/20))] (36/35) = (0/1) ∧ qAcceleration (1/5) [((-5/4),(1/20))] (36/35) = (0/1) := by decide +kernel
theorem oracle_decision_17_0 : checkVelocity (1/1) (0/1) (-1/4) [((17/4),(-1/20)),((15/4),(1/4))] = false := by decide +kernel
theorem oracle_decision_17_1 : checkVelocity (1/1) (71/480) (-1/4) [((17/4),(-1/20)),((15/4),(1/4))] = true := by decide +kernel
theorem oracle_decision_17_2 : checkVelocity (1/1) (70307/478560) (-1/4) [((17/4),(-1/20)),((15/4),(1/4))] = false := by decide +kernel
theorem oracle_jet_17_0 : qVelocity (1/1) [((17/4),(-1/20)),((15/4),(1/4))] (-1/4) = (0/1) ∧ qAcceleration (1/1) [((17/4),(-1/20)),((15/4),(1/4))] (-1/4) = (0/1) := by decide +kernel
theorem oracle_jet_17_1 : qVelocity (1/1) [((17/4),(-1/20)),((15/4),(1/4))] (-3/28) = (0/1) ∧ qAcceleration (1/1) [((17/4),(-1/20)),((15/4),(1/4))] (-3/28) = (0/1) := by decide +kernel
theorem oracle_decision_18_0 : checkVelocity (1/5) (0/1) (7/4) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] = false := by decide +kernel
theorem oracle_decision_18_1 : checkVelocity (1/5) (2/3) (7/4) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] = true := by decide +kernel
theorem oracle_decision_18_2 : checkVelocity (1/5) (1991/2991) (7/4) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] = false := by decide +kernel
theorem oracle_jet_18_0 : qVelocity (1/5) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] (7/4) = (0/1) ∧ qAcceleration (1/5) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] (7/4) = (0/1) := by decide +kernel
theorem oracle_jet_18_1 : qVelocity (1/5) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] (249/140) = (1/8232) ∧ qAcceleration (1/5) [((7/4),(1/20)),((-7/4),(-1/10)),((3/1),(-1/10)),((5/1),(1/5))] (249/140) = (5/392) := by decide +kernel
theorem oracle_decision_19_0 : checkVelocity (1/1) (0/1) (-1/2) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] = false := by decide +kernel
theorem oracle_decision_19_1 : checkVelocity (1/1) (2/15) (-1/2) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] = true := by decide +kernel
theorem oracle_decision_19_2 : checkVelocity (1/1) (1979/14955) (-1/2) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] = false := by decide +kernel
theorem oracle_jet_19_0 : qVelocity (1/1) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] (-1/2) = (29/960) ∧ qAcceleration (1/1) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] (-1/2) = (13/160) := by decide +kernel
theorem oracle_jet_19_1 : qVelocity (1/1) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] (-5/14) = (14069/329280) ∧ qAcceleration (1/1) [((17/4),(1/20)),((-3/2),(1/5)),((1/2),(1/5)),((13/4),(1/10)),((13/4),(-3/20)),((-1/1),(-3/20))] (-5/14) = (717/7840) := by decide +kernel
theorem oracle_decision_20_0 : checkVelocity (1/1) (0/1) (4/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] = false := by decide +kernel
theorem oracle_decision_20_1 : checkVelocity (1/1) (193/1920) (4/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] = true := by decide +kernel
theorem oracle_decision_20_2 : checkVelocity (1/1) (190501/1914240) (4/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] = false := by decide +kernel
theorem oracle_jet_20_0 : qVelocity (1/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] (4/1) = (-181/2560) ∧ qAcceleration (1/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] (4/1) = (39/640) := by decide +kernel
theorem oracle_jet_20_1 : qVelocity (1/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] (29/7) = (-162949/2634240) ∧ qAcceleration (1/1) [((17/4),(-3/20)),((1/4),(1/5)),((5/2),(-1/20)),((5/4),(-3/20)),((1/2),(0/1)),((-5/4),(-1/20))] (29/7) = (1919/31360) := by decide +kernel
theorem oracle_decision_21_0 : checkVelocity (3/2) (0/1) (0/1) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] = false := by decide +kernel
theorem oracle_decision_21_1 : checkVelocity (3/2) (47/270) (0/1) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] = true := by decide +kernel
theorem oracle_decision_21_2 : checkVelocity (3/2) (46589/269190) (0/1) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] = false := by decide +kernel
theorem oracle_jet_21_0 : qVelocity (3/2) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] (0/1) = (1/60) ∧ qAcceleration (3/2) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] (0/1) = (1/30) := by decide +kernel
theorem oracle_jet_21_1 : qVelocity (3/2) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] (3/14) = (127/5145) ∧ qAcceleration (3/2) [((-3/2),(3/20)),((1/1),(-1/20)),((1/1),(-3/20)),((4/1),(-3/20)),((7/2),(-1/4))] (3/14) = (2/49) := by decide +kernel
theorem oracle_decision_22_0 : checkVelocity (3/2) (0/1) (15/4) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] = false := by decide +kernel
theorem oracle_decision_22_1 : checkVelocity (3/2) (11/144) (15/4) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] = true := by decide +kernel
theorem oracle_decision_22_2 : checkVelocity (3/2) (10823/143568) (15/4) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] = false := by decide +kernel
theorem oracle_jet_22_0 : qVelocity (3/2) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] (15/4) = (-7/4860) ∧ qAcceleration (3/2) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] (15/4) = (1/405) := by decide +kernel
theorem oracle_jet_22_1 : qVelocity (3/2) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] (111/28) = (-719/833490) ∧ qAcceleration (3/2) [((9/2),(1/20)),((-2/1),(1/5)),((-2/1),(1/5)),((-5/4),(-1/20)),((15/4),(-1/5))] (111/28) = (83/39690) := by decide +kernel
theorem oracle_decision_23_0 : checkVelocity (1/5) (0/1) (0/1) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] = false := by decide +kernel
theorem oracle_decision_23_1 : checkVelocity (1/5) (3/2) (0/1) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] = true := by decide +kernel
theorem oracle_decision_23_2 : checkVelocity (1/5) (2989/1994) (0/1) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] = false := by decide +kernel
theorem oracle_jet_23_0 : qVelocity (1/5) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] (0/1) = (23/96) ∧ qAcceleration (1/5) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] (0/1) = (-25/16) := by decide +kernel
theorem oracle_jet_23_1 : qVelocity (1/5) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] (1/35) = (6359/32928) ∧ qAcceleration (1/5) [((7/4),(1/20)),((-1/2),(1/10)),((4/1),(1/5)),((5/1),(1/10)),((4/1),(1/5)),((4/1),(1/20))] (1/35) = (-1305/784) := by decide +kernel
theorem oracle_decision_24_0 : checkVelocity (1/1) (0/1) (-3/2) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] = false := by decide +kernel
theorem oracle_decision_24_1 : checkVelocity (1/1) (79/480) (-3/2) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] = true := by decide +kernel
theorem oracle_decision_24_2 : checkVelocity (1/1) (78283/478560) (-3/2) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] = false := by decide +kernel
theorem oracle_jet_24_0 : qVelocity (1/1) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] (-3/2) = (0/1) ∧ qAcceleration (1/1) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] (-3/2) = (0/1) := by decide +kernel
theorem oracle_jet_24_1 : qVelocity (1/1) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] (-19/14) = (0/1) ∧ qAcceleration (1/1) [((-1/4),(0/1)),((17/4),(1/10)),((-1/1),(-1/10)),((7/2),(-3/20)),((-5/4),(-3/20))] (-19/14) = (0/1) := by decide +kernel
theorem oracle_decision_25_0 : checkVelocity (1/5) (0/1) (5/2) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] = false := by decide +kernel
theorem oracle_decision_25_1 : checkVelocity (1/5) (11/6) (5/2) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] = true := by decide +kernel
theorem oracle_decision_25_2 : checkVelocity (1/5) (10961/5982) (5/2) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] = false := by decide +kernel
theorem oracle_jet_25_0 : qVelocity (1/5) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] (5/2) = (0/1) ∧ qAcceleration (1/5) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] (5/2) = (0/1) := by decide +kernel
theorem oracle_jet_25_1 : qVelocity (1/5) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] (177/70) = (0/1) ∧ qAcceleration (1/5) [((-7/4),(1/5)),((7/2),(-1/20)),((7/2),(-1/4)),((3/1),(0/1)),((7/2),(-1/4))] (177/70) = (0/1) := by decide +kernel
theorem oracle_decision_26_0 : checkVelocity (3/2) (0/1) (3/4) [((-2/1),(-3/20))] = false := by decide +kernel
theorem oracle_decision_26_1 : checkVelocity (3/2) (1/15) (3/4) [((-2/1),(-3/20))] = true := by decide +kernel
theorem oracle_decision_26_2 : checkVelocity (3/2) (982/14955) (3/4) [((-2/1),(-3/20))] = false := by decide +kernel
theorem oracle_jet_26_0 : qVelocity (3/2) [((-2/1),(-3/20))] (3/4) = (-277/4320) ∧ qAcceleration (3/2) [((-2/1),(-3/20))] (3/4) = (-7/360) := by decide +kernel
theorem oracle_jet_26_1 : qVelocity (3/2) [((-2/1),(-3/20))] (27/28) = (-98701/1481760) ∧ qAcceleration (3/2) [((-2/1),(-3/20))] (27/28) = (-11/3528) := by decide +kernel
theorem oracle_decision_27_0 : checkVelocity (1/2) (0/1) (-1/4) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] = false := by decide +kernel
theorem oracle_decision_27_1 : checkVelocity (1/2) (1/3) (-1/4) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] = true := by decide +kernel
theorem oracle_decision_27_2 : checkVelocity (1/2) (994/2991) (-1/4) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] = false := by decide +kernel
theorem oracle_jet_27_0 : qVelocity (1/2) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] (-1/4) = (1/480) ∧ qAcceleration (1/2) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] (-1/4) = (1/40) := by decide +kernel
theorem oracle_jet_27_1 : qVelocity (1/2) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] (-5/28) = (243/54880) ∧ qAcceleration (1/2) [((7/2),(1/4)),((-1/2),(1/20)),((17/4),(-1/20)),((17/4),(-1/20)),((0/1),(-1/5))] (-5/28) = (81/1960) := by decide +kernel
theorem oracle_decision_28_0 : checkVelocity (1/1) (0/1) (3/2) [((3/2),(1/4)),((3/2),(1/4))] = false := by decide +kernel
theorem oracle_decision_28_1 : checkVelocity (1/1) (1/3) (3/2) [((3/2),(1/4)),((3/2),(1/4))] = true := by decide +kernel
theorem oracle_decision_28_2 : checkVelocity (1/1) (994/2991) (3/2) [((3/2),(1/4)),((3/2),(1/4))] = false := by decide +kernel
theorem oracle_jet_28_0 : qVelocity (1/1) [((3/2),(1/4)),((3/2),(1/4))] (3/2) = (0/1) ∧ qAcceleration (1/1) [((3/2),(1/4)),((3/2),(1/4))] (3/2) = (0/1) := by decide +kernel
theorem oracle_jet_28_1 : qVelocity (1/1) [((3/2),(1/4)),((3/2),(1/4))] (23/14) = (1/4116) ∧ qAcceleration (1/1) [((3/2),(1/4)),((3/2),(1/4))] (23/14) = (1/196) := by decide +kernel
theorem oracle_decision_29_0 : checkVelocity (1/5) (0/1) (9/4) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] = false := by decide +kernel
theorem oracle_decision_29_1 : checkVelocity (1/5) (2/3) (9/4) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] = true := by decide +kernel
theorem oracle_decision_29_2 : checkVelocity (1/5) (1991/2991) (9/4) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] = false := by decide +kernel
theorem oracle_jet_29_0 : qVelocity (1/5) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] (9/4) = (-121/384) ∧ qAcceleration (1/5) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] (9/4) = (-105/32) := by decide +kernel
theorem oracle_jet_29_1 : qVelocity (1/5) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] (319/140) = (-53995/131712) ∧ qAcceleration (1/5) [((-2/1),(1/10)),((5/4),(1/5)),((-1/4),(-1/5)),((2/1),(-1/5)),((-2/1),(1/10))] (319/140) = (-5185/1568) := by decide +kernel
theorem oracle_decision_30_0 : checkVelocity (1/2) (0/1) (7/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] = false := by decide +kernel
theorem oracle_decision_30_1 : checkVelocity (1/2) (2/15) (7/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] = true := by decide +kernel
theorem oracle_decision_30_2 : checkVelocity (1/2) (1979/14955) (7/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] = false := by decide +kernel
theorem oracle_jet_30_0 : qVelocity (1/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] (7/2) = (0/1) ∧ qAcceleration (1/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] (7/2) = (0/1) := by decide +kernel
theorem oracle_jet_30_1 : qVelocity (1/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] (25/7) = (0/1) ∧ qAcceleration (1/2) [((17/4),(-1/10)),((5/1),(0/1)),((-3/2),(1/10)),((1/4),(1/20))] (25/7) = (0/1) := by decide +kernel
theorem oracle_decision_31_0 : checkVelocity (3/2) (0/1) (11/4) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] = false := by decide +kernel
theorem oracle_decision_31_1 : checkVelocity (3/2) (1253/9720) (11/4) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] = true := by decide +kernel
theorem oracle_decision_31_2 : checkVelocity (3/2) (1239521/9690840) (11/4) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] = false := by decide +kernel
theorem oracle_jet_31_0 : qVelocity (3/2) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] (11/4) = (4973/38880) ∧ qAcceleration (3/2) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] (11/4) = (23/3240) := by decide +kernel
theorem oracle_jet_31_1 : qVelocity (3/2) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] (83/28) = (1717061/13335840) ∧ qAcceleration (3/2) [((-7/4),(1/10)),((1/4),(1/10)),((-7/4),(1/10)),((7/4),(1/10)),((0/1),(3/20))] (83/28) = (-73/158760) := by decide +kernel
theorem oracle_decision_32_0 : checkVelocity (3/2) (0/1) (-5/4) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] = false := by decide +kernel
theorem oracle_decision_32_1 : checkVelocity (3/2) (2/15) (-5/4) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] = true := by decide +kernel
theorem oracle_decision_32_2 : checkVelocity (3/2) (1979/14955) (-5/4) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] = false := by decide +kernel
theorem oracle_jet_32_0 : qVelocity (3/2) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] (-5/4) = (0/1) ∧ qAcceleration (3/2) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] (-5/4) = (0/1) := by decide +kernel
theorem oracle_jet_32_1 : qVelocity (3/2) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] (-29/28) = (0/1) ∧ qAcceleration (3/2) [((9/2),(3/20)),((9/2),(3/20)),((5/2),(-3/20))] (-29/28) = (0/1) := by decide +kernel
theorem oracle_decision_33_0 : checkVelocity (1/2) (0/1) (1/4) [((1/4),(1/5))] = false := by decide +kernel
theorem oracle_decision_33_1 : checkVelocity (1/2) (4/15) (1/4) [((1/4),(1/5))] = true := by decide +kernel
theorem oracle_decision_33_2 : checkVelocity (1/2) (3973/14955) (1/4) [((1/4),(1/5))] = false := by decide +kernel
theorem oracle_jet_33_0 : qVelocity (1/2) [((1/4),(1/5))] (1/4) = (0/1) ∧ qAcceleration (1/2) [((1/4),(1/5))] (1/4) = (0/1) := by decide +kernel
theorem oracle_jet_33_1 : qVelocity (1/2) [((1/4),(1/5))] (9/28) = (1/5145) ∧ qAcceleration (1/2) [((1/4),(1/5))] (9/28) = (2/245) := by decide +kernel
theorem oracle_decision_34_0 : checkVelocity (3/2) (0/1) (3/2) [((-7/4),(1/20)),((11/4),(1/5))] = false := by decide +kernel
theorem oracle_decision_34_1 : checkVelocity (3/2) (4/45) (3/2) [((-7/4),(1/20)),((11/4),(1/5))] = true := by decide +kernel
theorem oracle_decision_34_2 : checkVelocity (3/2) (3943/44865) (3/2) [((-7/4),(1/20)),((11/4),(1/5))] = false := by decide +kernel
theorem oracle_jet_34_0 : qVelocity (3/2) [((-7/4),(1/20)),((11/4),(1/5))] (3/2) = (277/12960) ∧ qAcceleration (3/2) [((-7/4),(1/20)),((11/4),(1/5))] (3/2) = (-7/1080) := by decide +kernel
theorem oracle_jet_34_1 : qVelocity (3/2) [((-7/4),(1/20)),((11/4),(1/5))] (12/7) = (17357/889056) ∧ qAcceleration (3/2) [((-7/4),(1/20)),((11/4),(1/5))] (12/7) = (-559/52920) := by decide +kernel
theorem oracle_decision_35_0 : checkVelocity (1/2) (0/1) (-5/4) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] = false := by decide +kernel
theorem oracle_decision_35_1 : checkVelocity (1/2) (11/24) (-5/4) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] = true := by decide +kernel
theorem oracle_decision_35_2 : checkVelocity (1/2) (10943/23928) (-5/4) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] = false := by decide +kernel
theorem oracle_jet_35_0 : qVelocity (1/2) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] (-5/4) = (1/15) ∧ qAcceleration (1/2) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] (-5/4) = (2/5) := by decide +kernel
theorem oracle_jet_35_1 : qVelocity (1/2) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] (-33/28) = (508/5145) ∧ qAcceleration (1/2) [((1/4),(-3/20)),((1/2),(1/10)),((-7/4),(1/5)),((19/4),(3/20)),((0/1),(-1/4)),((4/1),(-1/20))] (-33/28) = (24/49) := by decide +kernel
theorem oracle_decision_36_0 : checkVelocity (1/5) (0/1) (3/1) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] = false := by decide +kernel
theorem oracle_decision_36_1 : checkVelocity (1/5) (1/2) (3/1) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] = true := by decide +kernel
theorem oracle_decision_36_2 : checkVelocity (1/5) (995/1994) (3/1) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] = false := by decide +kernel
theorem oracle_jet_36_0 : qVelocity (1/5) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] (3/1) = (121/512) ∧ qAcceleration (1/5) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] (3/1) = (315/128) := by decide +kernel
theorem oracle_jet_36_1 : qVelocity (1/5) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] (106/35) = (53995/175616) ∧ qAcceleration (1/5) [((-7/4),(-3/20)),((11/4),(1/5)),((-1/4),(1/20)),((-1/4),(1/10)),((-5/4),(3/20)),((11/4),(-1/20))] (106/35) = (15555/6272) := by decide +kernel
theorem oracle_decision_37_0 : checkVelocity (3/2) (0/1) (15/4) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] = false := by decide +kernel
theorem oracle_decision_37_1 : checkVelocity (3/2) (1/15) (15/4) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] = true := by decide +kernel
theorem oracle_decision_37_2 : checkVelocity (3/2) (982/14955) (15/4) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] = false := by decide +kernel
theorem oracle_jet_37_0 : qVelocity (3/2) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] (15/4) = (823/38880) ∧ qAcceleration (3/2) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] (15/4) = (-61/1080) := by decide +kernel
theorem oracle_jet_37_1 : qVelocity (3/2) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] (111/28) = (150151/13335840) ∧ qAcceleration (3/2) [((-1/1),(1/5)),((-2/1),(3/20)),((-5/4),(1/4)),((15/4),(-3/20))] (111/28) = (-131/3528) := by decide +kernel
theorem oracle_decision_38_0 : checkVelocity (1/1) (0/1) (-1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] = false := by decide +kernel
theorem oracle_decision_38_1 : checkVelocity (1/1) (4/15) (-1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] = true := by decide +kernel
theorem oracle_decision_38_2 : checkVelocity (1/1) (3973/14955) (-1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] = false := by decide +kernel
theorem oracle_jet_38_0 : qVelocity (1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] (-1/1) = (-9/512) ∧ qAcceleration (1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] (-1/1) = (-9/128) := by decide +kernel
theorem oracle_jet_38_1 : qVelocity (1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] (-6/7) = (-15625/526848) ∧ qAcceleration (1/1) [((1/1),(-1/10)),((9/2),(-1/5)),((7/4),(-1/20)),((-7/4),(-1/4)),((9/2),(-1/5)),((1/1),(-3/20))] (-6/7) = (-625/6272) := by decide +kernel
theorem oracle_decision_39_0 : checkVelocity (1/2) (0/1) (2/1) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] = false := by decide +kernel
theorem oracle_decision_39_1 : checkVelocity (1/2) (4/15) (2/1) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] = true := by decide +kernel
theorem oracle_decision_39_2 : checkVelocity (1/2) (3973/14955) (2/1) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] = false := by decide +kernel
theorem oracle_jet_39_0 : qVelocity (1/2) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] (2/1) = (0/1) ∧ qAcceleration (1/2) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] (2/1) = (0/1) := by decide +kernel
theorem oracle_jet_39_1 : qVelocity (1/2) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] (29/14) = (0/1) ∧ qAcceleration (1/2) [((19/4),(-3/20)),((-1/1),(1/20)),((-2/1),(1/4)),((5/2),(1/5)),((5/1),(3/20)),((9/2),(3/20))] (29/14) = (0/1) := by decide +kernel
theorem oracle_decision_40_0 : checkVelocity (1/2) (0/1) (2/1) [((9/2),(-1/10)),((9/2),(-1/10))] = false := by decide +kernel
theorem oracle_decision_40_1 : checkVelocity (1/2) (4/15) (2/1) [((9/2),(-1/10)),((9/2),(-1/10))] = true := by decide +kernel
theorem oracle_decision_40_2 : checkVelocity (1/2) (3973/14955) (2/1) [((9/2),(-1/10)),((9/2),(-1/10))] = false := by decide +kernel
theorem oracle_jet_40_0 : qVelocity (1/2) [((9/2),(-1/10)),((9/2),(-1/10))] (2/1) = (0/1) ∧ qAcceleration (1/2) [((9/2),(-1/10)),((9/2),(-1/10))] (2/1) = (0/1) := by decide +kernel
theorem oracle_jet_40_1 : qVelocity (1/2) [((9/2),(-1/10)),((9/2),(-1/10))] (29/14) = (0/1) ∧ qAcceleration (1/2) [((9/2),(-1/10)),((9/2),(-1/10))] (29/14) = (0/1) := by decide +kernel
theorem oracle_decision_41_0 : checkVelocity (1/5) (0/1) (13/4) [((15/4),(3/20))] = false := by decide +kernel
theorem oracle_decision_41_1 : checkVelocity (1/5) (1/2) (13/4) [((15/4),(3/20))] = true := by decide +kernel
theorem oracle_decision_41_2 : checkVelocity (1/5) (995/1994) (13/4) [((15/4),(3/20))] = false := by decide +kernel
theorem oracle_jet_41_0 : qVelocity (1/5) [((15/4),(3/20))] (13/4) = (0/1) ∧ qAcceleration (1/5) [((15/4),(3/20))] (13/4) = (0/1) := by decide +kernel
theorem oracle_jet_41_1 : qVelocity (1/5) [((15/4),(3/20))] (459/140) = (0/1) ∧ qAcceleration (1/5) [((15/4),(3/20))] (459/140) = (0/1) := by decide +kernel
theorem oracle_decision_42_0 : checkVelocity (1/2) (0/1) (3/1) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] = false := by decide +kernel
theorem oracle_decision_42_1 : checkVelocity (1/2) (1/3) (3/1) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] = true := by decide +kernel
theorem oracle_decision_42_2 : checkVelocity (1/2) (994/2991) (3/1) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] = false := by decide +kernel
theorem oracle_jet_42_0 : qVelocity (1/2) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] (3/1) = (1/12) ∧ qAcceleration (1/2) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] (3/1) = (1/2) := by decide +kernel
theorem oracle_jet_42_1 : qVelocity (1/2) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] (43/14) = (127/1029) ∧ qAcceleration (1/2) [((5/2),(1/4)),((-2/1),(3/20)),((-1/4),(-1/5))] (43/14) = (30/49) := by decide +kernel
theorem oracle_decision_43_0 : checkVelocity (1/5) (0/1) (2/1) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] = false := by decide +kernel
theorem oracle_decision_43_1 : checkVelocity (1/5) (5/6) (2/1) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] = true := by decide +kernel
theorem oracle_decision_43_2 : checkVelocity (1/5) (4979/5982) (2/1) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] = false := by decide +kernel
theorem oracle_jet_43_0 : qVelocity (1/5) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] (2/1) = (0/1) ∧ qAcceleration (1/5) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] (2/1) = (0/1) := by decide +kernel
theorem oracle_jet_43_1 : qVelocity (1/5) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] (71/35) = (0/1) ∧ qAcceleration (1/5) [((9/4),(1/4)),((3/4),(-1/4)),((1/2),(-1/20)),((3/1),(-1/20)),((5/1),(-3/20))] (71/35) = (0/1) := by decide +kernel
theorem oracle_decision_44_0 : checkVelocity (1/5) (0/1) (3/4) [((1/4),(1/5)),((0/1),(1/5))] = false := by decide +kernel
theorem oracle_decision_44_1 : checkVelocity (1/5) (185/384) (3/4) [((1/4),(1/5)),((0/1),(1/5))] = true := by decide +kernel
theorem oracle_decision_44_2 : checkVelocity (1/5) (184061/382848) (3/4) [((1/4),(1/5)),((0/1),(1/5))] = false := by decide +kernel
theorem oracle_jet_44_0 : qVelocity (1/5) [((1/4),(1/5)),((0/1),(1/5))] (3/4) = (185/384) ∧ qAcceleration (1/5) [((1/4),(1/5)),((0/1),(1/5))] (3/4) = (-105/32) := by decide +kernel
theorem oracle_jet_44_1 : qVelocity (1/5) [((1/4),(1/5)),((0/1),(1/5))] (109/140) = (50899/131712) ∧ qAcceleration (1/5) [((1/4),(1/5)),((0/1),(1/5))] (109/140) = (-5265/1568) := by decide +kernel
theorem oracle_decision_45_0 : checkVelocity (1/5) (0/1) (1/2) [((-2/1),(3/20))] = true := by decide +kernel
theorem oracle_decision_45_1 : checkVelocity (1/5) (0/1) (1/2) [((-2/1),(3/20))] = true := by decide +kernel
theorem oracle_decision_45_2 : checkVelocity (1/5) (0/1) (1/2) [((-2/1),(3/20))] = true := by decide +kernel
theorem oracle_jet_45_0 : qVelocity (1/5) [((-2/1),(3/20))] (1/2) = (0/1) ∧ qAcceleration (1/5) [((-2/1),(3/20))] (1/2) = (0/1) := by decide +kernel
theorem oracle_jet_45_1 : qVelocity (1/5) [((-2/1),(3/20))] (37/70) = (0/1) ∧ qAcceleration (1/5) [((-2/1),(3/20))] (37/70) = (0/1) := by decide +kernel
theorem oracle_decision_46_0 : checkVelocity (3/2) (0/1) (9/4) [((15/4),(-1/4)),((15/4),(-1/4))] = false := by decide +kernel
theorem oracle_decision_46_1 : checkVelocity (3/2) (2/9) (9/4) [((15/4),(-1/4)),((15/4),(-1/4))] = true := by decide +kernel
theorem oracle_decision_46_2 : checkVelocity (3/2) (1985/8973) (9/4) [((15/4),(-1/4)),((15/4),(-1/4))] = false := by decide +kernel
theorem oracle_jet_46_0 : qVelocity (3/2) [((15/4),(-1/4)),((15/4),(-1/4))] (9/4) = (0/1) ∧ qAcceleration (3/2) [((15/4),(-1/4)),((15/4),(-1/4))] (9/4) = (0/1) := by decide +kernel
theorem oracle_jet_46_1 : qVelocity (3/2) [((15/4),(-1/4)),((15/4),(-1/4))] (69/28) = (0/1) ∧ qAcceleration (3/2) [((15/4),(-1/4)),((15/4),(-1/4))] (69/28) = (0/1) := by decide +kernel
theorem oracle_decision_47_0 : checkVelocity (1/5) (0/1) (1/4) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] = false := by decide +kernel
theorem oracle_decision_47_1 : checkVelocity (1/5) (1/3) (1/4) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] = true := by decide +kernel
theorem oracle_decision_47_2 : checkVelocity (1/5) (994/2991) (1/4) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] = false := by decide +kernel
theorem oracle_jet_47_0 : qVelocity (1/5) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] (1/4) = (0/1) ∧ qAcceleration (1/5) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] (1/4) = (0/1) := by decide +kernel
theorem oracle_jet_47_1 : qVelocity (1/5) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] (39/140) = (0/1) ∧ qAcceleration (1/5) [((3/1),(-1/20)),((1/2),(-1/10)),((3/1),(-1/20))] (39/140) = (0/1) := by decide +kernel
theorem oracle_decision_48_0 : checkVelocity (1/5) (0/1) (2/1) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] = false := by decide +kernel
theorem oracle_decision_48_1 : checkVelocity (1/5) (2/3) (2/1) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] = true := by decide +kernel
theorem oracle_decision_48_2 : checkVelocity (1/5) (1991/2991) (2/1) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] = false := by decide +kernel
theorem oracle_jet_48_0 : qVelocity (1/5) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] (2/1) = (0/1) ∧ qAcceleration (1/5) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] (2/1) = (0/1) := by decide +kernel
theorem oracle_jet_48_1 : qVelocity (1/5) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] (71/35) = (0/1) ∧ qAcceleration (1/5) [((-5/4),(0/1)),((5/1),(-3/20)),((1/1),(1/5)),((-1/4),(-1/10)),((15/4),(1/5)),((2/1),(0/1)),((-5/4),(0/1))] (71/35) = (0/1) := by decide +kernel
theorem oracle_decision_49_0 : checkVelocity (1/1) (0/1) (-1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] = false := by decide +kernel
theorem oracle_decision_49_1 : checkVelocity (1/1) (25/192) (-1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] = true := by decide +kernel
theorem oracle_decision_49_2 : checkVelocity (1/1) (24733/191424) (-1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] = false := by decide +kernel
theorem oracle_jet_49_0 : qVelocity (1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] (-1/1) = (0/1) ∧ qAcceleration (1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] (-1/1) = (0/1) := by decide +kernel
theorem oracle_jet_49_1 : qVelocity (1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] (-6/7) = (-1/8232) ∧ qAcceleration (1/1) [((-1/4),(1/10)),((-1/4),(-1/20)),((-1/4),(1/10)),((-1/1),(-1/4))] (-6/7) = (-1/392) := by decide +kernel
theorem oracle_decision_50_0 : checkVelocity (1/5) (0/1) (1/4) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] = false := by decide +kernel
theorem oracle_decision_50_1 : checkVelocity (1/5) (1/2) (1/4) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] = true := by decide +kernel
theorem oracle_decision_50_2 : checkVelocity (1/5) (995/1994) (1/4) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] = false := by decide +kernel
theorem oracle_jet_50_0 : qVelocity (1/5) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] (1/4) = (0/1) ∧ qAcceleration (1/5) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] (1/4) = (0/1) := by decide +kernel
theorem oracle_jet_50_1 : qVelocity (1/5) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] (39/140) = (-1/2744) ∧ qAcceleration (1/5) [((-5/4),(-1/4)),((7/4),(-3/20)),((5/1),(-3/20)),((11/4),(-3/20)),((1/4),(-3/20))] (39/140) = (-15/392) := by decide +kernel
theorem oracle_decision_51_0 : checkVelocity (1/2) (0/1) (3/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] = false := by decide +kernel
theorem oracle_decision_51_1 : checkVelocity (1/2) (2/15) (3/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] = true := by decide +kernel
theorem oracle_decision_51_2 : checkVelocity (1/2) (1979/14955) (3/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] = false := by decide +kernel
theorem oracle_jet_51_0 : qVelocity (1/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] (3/2) = (-1/240) ∧ qAcceleration (1/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] (3/2) = (3/20) := by decide +kernel
theorem oracle_jet_51_1 : qVelocity (1/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] (11/7) = (479/82320) ∧ qAcceleration (1/2) [((-1/4),(-1/5)),((5/4),(1/10)),((2/1),(-1/10))] (11/7) = (131/980) := by decide +kernel
theorem oracle_decision_52_0 : checkVelocity (1/1) (0/1) (5/2) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] = false := by decide +kernel
theorem oracle_decision_52_1 : checkVelocity (1/1) (893/3840) (5/2) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] = true := by decide +kernel
theorem oracle_decision_52_2 : checkVelocity (1/1) (886481/3828480) (5/2) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] = false := by decide +kernel
theorem oracle_jet_52_0 : qVelocity (1/1) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] (5/2) = (-1/10) ∧ qAcceleration (1/1) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] (5/2) = (1/5) := by decide +kernel
theorem oracle_jet_52_1 : qVelocity (1/1) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] (37/14) = (-397/5145) ∧ qAcceleration (1/1) [((3/2),(-1/10)),((19/4),(-1/20)),((13/4),(-1/10)),((-1/2),(-1/4)),((3/1),(-1/4)),((-3/2),(1/5)),((-1/2),(-1/4))] (37/14) = (6/49) := by decide +kernel
theorem oracle_decision_53_0 : checkVelocity (1/5) (0/1) (2/1) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] = true := by decide +kernel
theorem oracle_decision_53_1 : checkVelocity (1/5) (0/1) (2/1) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] = true := by decide +kernel
theorem oracle_decision_53_2 : checkVelocity (1/5) (0/1) (2/1) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] = true := by decide +kernel
theorem oracle_jet_53_0 : qVelocity (1/5) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] (2/1) = (0/1) ∧ qAcceleration (1/5) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] (2/1) = (0/1) := by decide +kernel
theorem oracle_jet_53_1 : qVelocity (1/5) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] (71/35) = (0/1) ∧ qAcceleration (1/5) [((-1/4),(-3/20)),((-5/4),(1/20)),((-1/1),(-1/20)),((-1/1),(-1/20))] (71/35) = (0/1) := by decide +kernel
theorem oracle_decision_54_0 : checkVelocity (1/1) (0/1) (3/4) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] = false := by decide +kernel
theorem oracle_decision_54_1 : checkVelocity (1/1) (1/10) (3/4) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] = true := by decide +kernel
theorem oracle_decision_54_2 : checkVelocity (1/1) (987/9970) (3/4) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] = false := by decide +kernel
theorem oracle_jet_54_0 : qVelocity (1/1) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] (3/4) = (0/1) ∧ qAcceleration (1/1) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] (3/4) = (0/1) := by decide +kernel
theorem oracle_jet_54_1 : qVelocity (1/1) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] (25/28) = (0/1) ∧ qAcceleration (1/1) [((15/4),(-1/20)),((9/2),(-1/10)),((1/1),(3/20))] (25/28) = (0/1) := by decide +kernel
theorem oracle_decision_55_0 : checkVelocity (3/2) (0/1) (13/4) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] = false := by decide +kernel
theorem oracle_decision_55_1 : checkVelocity (3/2) (1/9) (13/4) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] = true := by decide +kernel
theorem oracle_decision_55_2 : checkVelocity (3/2) (988/8973) (13/4) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] = false := by decide +kernel
theorem oracle_jet_55_0 : qVelocity (3/2) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] (13/4) = (83/1620) ∧ qAcceleration (3/2) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] (13/4) = (1/18) := by decide +kernel
theorem oracle_jet_55_1 : qVelocity (3/2) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] (97/28) = (34661/555660) ∧ qAcceleration (3/2) [((13/4),(-1/4)),((3/4),(1/4)),((19/4),(1/4)),((1/4),(-1/10))] (97/28) = (41/882) := by decide +kernel
theorem oracle_decision_56_0 : checkVelocity (3/2) (0/1) (4/1) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] = false := by decide +kernel
theorem oracle_decision_56_1 : checkVelocity (3/2) (34/405) (4/1) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] = true := by decide +kernel
theorem oracle_decision_56_2 : checkVelocity (3/2) (33493/403785) (4/1) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] = false := by decide +kernel
theorem oracle_jet_56_0 : qVelocity (3/2) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] (4/1) = (34/405) ∧ qAcceleration (3/2) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] (4/1) = (-1/540) := by decide +kernel
theorem oracle_jet_56_1 : qVelocity (3/2) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] (59/14) = (91667/1111320) ∧ qAcceleration (3/2) [((-1/2),(-1/10)),((1/4),(3/20)),((3/4),(-1/20)),((-1/2),(1/10)),((3/2),(3/20))] (59/14) = (-319/26460) := by decide +kernel
theorem oracle_decision_57_0 : checkVelocity (3/2) (0/1) (7/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] = false := by decide +kernel
theorem oracle_decision_57_1 : checkVelocity (3/2) (679/12960) (7/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] = true := by decide +kernel
theorem oracle_decision_57_2 : checkVelocity (3/2) (664003/12921120) (7/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] = false := by decide +kernel
theorem oracle_jet_57_0 : qVelocity (3/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] (7/2) = (679/12960) ∧ qAcceleration (3/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] (7/2) = (-53/3240) := by decide +kernel
theorem oracle_jet_57_1 : qVelocity (3/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] (26/7) = (41987/889056) ∧ qAcceleration (3/2) [((17/4),(1/20)),((-5/4),(1/20)),((0/1),(3/20)),((-3/2),(-1/4))] (26/7) = (-4901/158760) := by decide +kernel
theorem oracle_decision_58_0 : checkVelocity (3/2) (0/1) (-3/2) [((4/1),(1/5)),((19/4),(-3/20))] = false := by decide +kernel
theorem oracle_decision_58_1 : checkVelocity (3/2) (19/360) (-3/2) [((4/1),(1/5)),((19/4),(-3/20))] = true := by decide +kernel
theorem oracle_decision_58_2 : checkVelocity (3/2) (18583/358920) (-3/2) [((4/1),(1/5)),((19/4),(-3/20))] = false := by decide +kernel
theorem oracle_jet_58_0 : qVelocity (3/2) [((4/1),(1/5)),((19/4),(-3/20))] (-3/2) = (0/1) ∧ qAcceleration (3/2) [((4/1),(1/5)),((19/4),(-3/20))] (-3/2) = (0/1) := by decide +kernel
theorem oracle_jet_58_1 : qVelocity (3/2) [((4/1),(1/5)),((19/4),(-3/20))] (-9/7) = (0/1) ∧ qAcceleration (3/2) [((4/1),(1/5)),((19/4),(-3/20))] (-9/7) = (0/1) := by decide +kernel
theorem oracle_decision_59_0 : checkVelocity (1/5) (0/1) (4/1) [((19/4),(0/1)),((-1/1),(-1/10))] = true := by decide +kernel
theorem oracle_decision_59_1 : checkVelocity (1/5) (0/1) (4/1) [((19/4),(0/1)),((-1/1),(-1/10))] = true := by decide +kernel
theorem oracle_decision_59_2 : checkVelocity (1/5) (0/1) (4/1) [((19/4),(0/1)),((-1/1),(-1/10))] = true := by decide +kernel
theorem oracle_jet_59_0 : qVelocity (1/5) [((19/4),(0/1)),((-1/1),(-1/10))] (4/1) = (0/1) ∧ qAcceleration (1/5) [((19/4),(0/1)),((-1/1),(-1/10))] (4/1) = (0/1) := by decide +kernel
theorem oracle_jet_59_1 : qVelocity (1/5) [((19/4),(0/1)),((-1/1),(-1/10))] (141/35) = (0/1) ∧ qAcceleration (1/5) [((19/4),(0/1)),((-1/1),(-1/10))] (141/35) = (0/1) := by decide +kernel
theorem oracle_decision_60_0 : checkVelocity (1/2) (0/1) (-1/1) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] = false := by decide +kernel
theorem oracle_decision_60_1 : checkVelocity (1/2) (19/60) (-1/1) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] = true := by decide +kernel
theorem oracle_decision_60_2 : checkVelocity (1/2) (18883/59820) (-1/1) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] = false := by decide +kernel
theorem oracle_jet_60_0 : qVelocity (1/2) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] (-1/1) = (0/1) ∧ qAcceleration (1/2) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] (-1/1) = (0/1) := by decide +kernel
theorem oracle_jet_60_1 : qVelocity (1/2) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] (-13/14) = (1/5145) ∧ qAcceleration (1/2) [((-1/1),(1/5)),((-1/4),(-1/10)),((-3/4),(1/20)),((13/4),(-1/5)),((11/4),(-1/10)),((2/1),(1/5))] (-13/14) = (2/245) := by decide +kernel
theorem oracle_decision_61_0 : checkVelocity (1/2) (0/1) (3/4) [((3/1),(-1/20))] = false := by decide +kernel
theorem oracle_decision_61_1 : checkVelocity (1/2) (1/15) (3/4) [((3/1),(-1/20))] = true := by decide +kernel
theorem oracle_decision_61_2 : checkVelocity (1/2) (982/14955) (3/4) [((3/1),(-1/20))] = false := by decide +kernel
theorem oracle_jet_61_0 : qVelocity (1/2) [((3/1),(-1/20))] (3/4) = (0/1) ∧ qAcceleration (1/2) [((3/1),(-1/20))] (3/4) = (0/1) := by decide +kernel
theorem oracle_jet_61_1 : qVelocity (1/2) [((3/1),(-1/20))] (23/28) = (0/1) ∧ qAcceleration (1/2) [((3/1),(-1/20))] (23/28) = (0/1) := by decide +kernel
theorem oracle_decision_62_0 : checkVelocity (3/2) (0/1) (-5/4) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] = false := by decide +kernel
theorem oracle_decision_62_1 : checkVelocity (3/2) (23/72) (-5/4) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] = true := by decide +kernel
theorem oracle_decision_62_2 : checkVelocity (3/2) (22859/71784) (-5/4) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] = false := by decide +kernel
theorem oracle_jet_62_0 : qVelocity (3/2) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] (-5/4) = (0/1) ∧ qAcceleration (3/2) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] (-5/4) = (0/1) := by decide +kernel
theorem oracle_jet_62_1 : qVelocity (3/2) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] (-29/28) = (0/1) ∧ qAcceleration (3/2) [((1/2),(-1/4)),((9/2),(-3/20)),((15/4),(-1/10)),((1/2),(-1/4)),((5/1),(1/4)),((11/4),(1/10)),((-1/4),(-1/4))] (-29/28) = (0/1) := by decide +kernel
theorem oracle_decision_63_0 : checkVelocity (3/2) (0/1) (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] = false := by decide +kernel
theorem oracle_decision_63_1 : checkVelocity (3/2) (293/3888) (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] = true := by decide +kernel
theorem oracle_decision_63_2 : checkVelocity (3/2) (288233/3876336) (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] = false := by decide +kernel
theorem oracle_jet_63_0 : qVelocity (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] (3/2) = (0/1) ∧ qAcceleration (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] (3/2) = (0/1) := by decide +kernel
theorem oracle_jet_63_1 : qVelocity (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] (12/7) = (0/1) ∧ qAcceleration (3/2) [((5/2),(1/5)),((7/4),(-1/20)),((5/1),(-1/10)),((-2/1),(0/1))] (12/7) = (0/1) := by decide +kernel
