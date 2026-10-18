import UniquenessClient
import ComplexUniquenessClient
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[`CliffordModel, `HyperbolicSpinor, `SpinorDimensions, `SplitSpinor, `FockOperators, `VacuumProjector, `WordActions, `FockImage, `MatrixUnits, `BasisActions, `FullImage, `RealEquivalence, `TransposeBridge, `VolumeForm, `RealAdjoint, `AdjointControls, `ComplexAdjoint, `ComplexEquivalence, `ComplexBridge, `ComplexControls, `ComplementAction, `SplitSignature, `ComplexSignature, `OrderControls, `SignatureControls, `ReviewerClient, `CounterWitnesses, `FormUniqueness, `UniquenessClient, `ComplexFormUniqueness, `ComplexUniquenessClient]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[i.toNat]!
      if owned.contains origin then
        if info.isUnsafe then throwError "Unsafe owned declaration: {n}"
        if info.isAxiom then throwError "Owned axiom: {n}"
        let axioms ← collectAxioms n
        for ax in axioms do
          unless allowed.contains ax do throwError "Unexpected axiom: {n}: {ax}"
        logInfo m!"AUDIT|{origin}|{n}|{info.isTheorem}|{axioms}"
