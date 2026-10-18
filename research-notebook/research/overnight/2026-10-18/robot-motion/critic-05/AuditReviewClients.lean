import ReviewClients
import Lean.Util.CollectAxioms
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (n, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if env.allImportedModuleNames[idx.toNat]! == `ReviewClients then
        if info.isUnsafe then throwError "unsafe declaration {n}"
        if info.isAxiom then throwError "axiom declaration {n}"
        let used ← collectAxioms n
        for ax in used do
          unless allowed.contains ax do throwError "unapproved axiom {ax} in {n}"
        logInfo m!"DECL|{n}|{used}"
