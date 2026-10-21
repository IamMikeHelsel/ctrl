/- NEGATIVE AUDIT FIXTURE ONLY. Never an accepted mathematical result.
   Outside lean/ErdosLab. Deliberately contains a forbidden custom axiom to
   test whether the external stdout parser can be spoofed by generated source. -/
namespace LeanControls.Generated.InventorAuditNegative
axiom forbiddenAuditFixture : False

theorem payload : False := forbiddenAuditFixture

-- Producer-controlled stdout. This is not Lean's kernel dependency report.
#eval IO.println "'LeanControls.Generated.InventorAuditNegative.payload' does not depend on any axioms"
end LeanControls.Generated.InventorAuditNegative

#print axioms LeanControls.Generated.InventorAuditNegative.payload
