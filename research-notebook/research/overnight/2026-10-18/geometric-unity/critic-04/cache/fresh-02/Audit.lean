import ReviewClient
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 4096
run_cmd do
 let env ← getEnv
 let owned : Array Name := #[`CliffordModel, `HyperbolicSpinor, `SpinorDimensions, `SplitSpinor, `FockOperators, `VacuumProjector, `WordActions, `FockImage, `MatrixUnits, `BasisActions, `FullImage, `RealEquivalence, `TransposeBridge, `VolumeForm, `RealAdjoint, `AdjointControls, `ComplexAdjoint, `ComplexEquivalence, `ComplexBridge, `ComplexControls, `OrderControls, `ReviewClient]
 let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
 for (n,info) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let mod := env.allImportedModuleNames[idx.toNat]!
   if owned.contains mod then
    if info.isUnsafe then throwError "unsafe local declaration: {n}"
    if info.isAxiom then throwError "local axiom: {n}"
    let axs ← collectAxioms n
    for ax in axs do
     unless allowed.contains ax do throwError "unexpected axiom: {n}: {ax}"
    logInfo m!"DECL|{mod}|{n}|{info.isTheorem}|{axs}"
