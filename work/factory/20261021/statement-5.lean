import Mathlib
namespace FactoryStatementCheck
def statement : Prop :=
  ∀ (x z dx dz ε : ℝ), 0 ≤ ε → ε < z → |dz| ≤ ε →
    0 < z + dz ∧
    |(x+dx)/(z+dz) - x/z| ≤ (|dx|*z + |x|*ε)/(z*(z-ε))
#check statement
end FactoryStatementCheck
