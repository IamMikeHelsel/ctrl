import FutureCommit
namespace ExactClient
open RobotMotion RobotMotion.FutureCommit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def p : Pending := ⟨⟨[((11/50:ℚ),(1/50:ℚ))],(0/1:ℚ),(1/5:ℚ),7⟩,⟨(0/1:ℚ),(13/25:ℚ),(17/10:ℚ),(1/10:ℚ),(1/2:ℚ),(15/2:ℚ),10⟩,(31/50:ℚ),(-1/50:ℚ),[(13/25:ℚ),(31/50:ℚ)]⟩
def b : Base := ⟨[((11/50:ℚ),(1/50:ℚ)),((31/50:ℚ),(-1/50:ℚ))],(0/1:ℚ),(1/5:ℚ),8⟩
def t : Task := ⟨(0/1:ℚ),(13/25:ℚ),(17/10:ℚ),(1/10:ℚ),(1/2:ℚ),(15/2:ℚ),10⟩
def tm : Timing := ⟨(57/100:ℚ),(57/100:ℚ),(1/100:ℚ)⟩
#eval commitOK p b t tm
end ExactClient
