import Witnesses
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[`Primitive,`Kernel,`Knots,`RationalGuard,`Reference,`AccelerationGuard,`AccelerationFixtures,`ReversalProposal,`TimedAdmission,`Witnesses]
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
