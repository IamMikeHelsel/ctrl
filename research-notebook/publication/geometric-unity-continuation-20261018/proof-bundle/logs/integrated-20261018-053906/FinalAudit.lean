import CliffordModel
import HyperbolicSpinor
import SpinorDimensions
import SplitSpinor
import FockOperators
import VacuumProjector
import WordActions
import FockImage
import MatrixUnits
import BasisActions
import FullImage
import RealEquivalence
import TransposeBridge
import VolumeForm
import RealAdjoint
import AdjointControls
import ComplexAdjoint
import ComplexEquivalence
import ComplexBridge
import ComplexControls
import ComplementAction
import SplitSignature
import SkewLie
import Chirality
import SpinEquivariance
import RationalBoost
import BoostClient
import ChiralityClient
import VolumeTwist
import ComplexChoices
import ComplexFormUniqueness
import ComplexSignature
import ComplexUniquenessClient
import SignatureControls
import OrderControls
import ReviewerClient
import CounterWitnesses
import VolumeTwistActual
import QuadraticTwist
import GeneralBoost
import HermitianFamily
import LiftEquivalence
import FinalClient
import FormUniqueness
import QuadraticClient
import SkewClient
import SpinClient
import UniquenessClient
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let owned : Array Name := #[`CliffordModel, `HyperbolicSpinor, `SpinorDimensions, `SplitSpinor, `FockOperators, `VacuumProjector, `WordActions, `FockImage, `MatrixUnits, `BasisActions, `FullImage, `RealEquivalence, `TransposeBridge, `VolumeForm, `RealAdjoint, `AdjointControls, `ComplexAdjoint, `ComplexEquivalence, `ComplexBridge, `ComplexControls, `ComplementAction, `SplitSignature, `SkewLie, `Chirality, `SpinEquivariance, `RationalBoost, `BoostClient, `ChiralityClient, `VolumeTwist, `ComplexChoices, `ComplexFormUniqueness, `ComplexSignature, `ComplexUniquenessClient, `SignatureControls, `OrderControls, `ReviewerClient, `CounterWitnesses, `VolumeTwistActual, `QuadraticTwist, `GeneralBoost, `HermitianFamily, `LiftEquivalence, `FinalClient, `FormUniqueness, `QuadraticClient, `SkewClient, `SpinClient, `UniquenessClient]
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
