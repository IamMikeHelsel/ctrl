import PhysicalArrival
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[`Primitive,`Kernel,`Knots,`RationalGuard,`Reference,`AccelerationGuard,`AccelerationFixtures,`ReversalProposal,`TimedAdmission,`Admission,`LeanControls.Discrete,`LeanControls.BernsteinCertificate,`LeanControls.Generated.LagLower,`LeanControls.Generated.LagUpper,`LeanControls.VertexCertificate,`LeanControls.ActuatorLag,`LeanControls.PD,`LeanControls.SampledPD,`LeanControls.RobustPD,`LeanControls.SaturationSector,`LeanControls.Generated.TravelQuarterLower,`LeanControls.Generated.TravelQuarterUpper,`LeanControls.Generated.TravelFullLower,`LeanControls.Generated.TravelFullUpper,`LeanControls.SaturatedLag,`LeanControls.TravelGeometry,`LeanControls.TravelDisturbance,`LeanControls.UncertainResponse,`LeanControls.Generated.UncertainA0L0R0,`LeanControls.Generated.UncertainA0L0R1,`LeanControls.Generated.UncertainA0L0R2,`LeanControls.Generated.UncertainA0L1R0,`LeanControls.Generated.UncertainA0L1R1,`LeanControls.Generated.UncertainA0L1R2,`LeanControls.Generated.UncertainA1L0R0,`LeanControls.Generated.UncertainA1L0R1,`LeanControls.Generated.UncertainA1L0R2,`LeanControls.Generated.UncertainA1L1R0,`LeanControls.Generated.UncertainA1L1R1,`LeanControls.Generated.UncertainA1L1R2,`LeanControls.UncertainLag,`ComparisonEnvelope,`RobustHold,`SmoothReplan,`TrackingReplan,`ScaledTracking,`Composition,`PhysicalArrival]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.allImportedModuleNames[idx.toNat]!
      if localModules.contains moduleName then
        if info.isUnsafe then throwError "UNSAFE {name}"
        if info.isAxiom then throwError "LOCAL_AXIOM {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "UNAPPROVED {name} {ax}"
        logInfo m!"AUDIT|{moduleName}|{name}|theorem={info.isTheorem}|{axioms}"
