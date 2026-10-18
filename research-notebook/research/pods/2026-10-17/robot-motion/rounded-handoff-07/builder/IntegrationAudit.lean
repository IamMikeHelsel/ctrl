import HandoffWitnesses
import NativeInstances
import NativeGlobal
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[`LeanControls.Discrete,`LeanControls.BernsteinCertificate,`LeanControls.Generated.LagLower,`LeanControls.Generated.LagUpper,`LeanControls.VertexCertificate,`LeanControls.ActuatorLag,`LeanControls.PD,`LeanControls.SampledPD,`LeanControls.RobustPD,`LeanControls.SaturationSector,`LeanControls.Generated.TravelQuarterLower,`LeanControls.Generated.TravelQuarterUpper,`LeanControls.Generated.TravelFullLower,`LeanControls.Generated.TravelFullUpper,`LeanControls.SaturatedLag,`LeanControls.TravelGeometry,`LeanControls.TravelDisturbance,`LeanControls.UncertainResponse,`LeanControls.Generated.UncertainA0L0R0,`LeanControls.Generated.UncertainA0L0R1,`LeanControls.Generated.UncertainA0L0R2,`LeanControls.Generated.UncertainA0L1R0,`LeanControls.Generated.UncertainA0L1R1,`LeanControls.Generated.UncertainA0L1R2,`LeanControls.Generated.UncertainA1L0R0,`LeanControls.Generated.UncertainA1L0R1,`LeanControls.Generated.UncertainA1L0R2,`LeanControls.Generated.UncertainA1L1R0,`LeanControls.Generated.UncertainA1L1R1,`LeanControls.Generated.UncertainA1L1R2,`LeanControls.UncertainLag,`ComparisonEnvelope,`RobustHold,`SmoothReplan,`TrackingReplan,`ScaledTracking,`RoundedHandoff,`HandoffWitnesses,`NativeData,`NativeBridge,`NativeInstances,`NativeCoverage,`NativeGlobal]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let mod := env.allImportedModuleNames[idx.toNat]!
      if owned.contains mod then
        if info.isUnsafe then throwError "unsafe local declaration {n}"
        if info.isAxiom then throwError "local axiom {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {ax} in {n}"
        logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{used}"
