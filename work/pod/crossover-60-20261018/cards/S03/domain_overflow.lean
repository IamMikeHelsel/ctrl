import LeanControls.Quantized
namespace S03Overflow
open LeanControls.PD
/-- True state is strictly in the unchanged source invariant. -/
theorem admitted : energy (-1/20) (349/1000)<1/10 := by norm_num [energy]
/-- All four full-cell corners are safe; no reliance on a rounded-center admission. -/
theorem cell_admitted :
    energy (-6555/131072) (45743/131072)<1/10 ∧
    energy (-6555/131072) (45745/131072)<1/10 ∧
    energy (-6553/131072) (45743/131072)<1/10 ∧
    energy (-6553/131072) (45745/131072)<1/10 := by norm_num [energy]
/-- Explicit modulo16-produced command, exact source plant hold h=.5,w=0. -/
theorem overflow_violates :
    energy (-1/20+(1/2)*(349/1000)+(1/2)^2/2*(3474/65536))
      (349/1000+(1/2)*(3474/65536))>1/10 := by norm_num [energy]
/-- Widened arithmetic produces the correctly decoded Q16 command at the same state. -/
theorem proper_arithmetic_safe :
    energy (-1/20+(1/2)*(349/1000)+(1/2)^2/2*(-62062/65536))
      (349/1000+(1/2)*(-62062/65536))≤1/10 := by norm_num [energy]
end S03Overflow
#print axioms S03Overflow.admitted
#print axioms S03Overflow.cell_admitted
#print axioms S03Overflow.overflow_violates
#print axioms S03Overflow.proper_arithmetic_safe
