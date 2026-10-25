import ControlsLean
import Lean

open Lean

/- Resolve each backticked doc token against the environment of `import ControlsLean`:
a token resolves if it is a declaration name, a dot-suffix of one, or an imported module.
Prints unresolved tokens (`.lean` file tokens are left to the Python side). -/
#eval show CoreM Unit from do
  let env ← getEnv
  let mut names : Std.HashSet String := {}
  for (c, _) in env.constants.toList do
    let comps := c.components.map toString
    for i in [0:comps.length] do
      names := names.insert (".".intercalate (comps.drop i))
  for m in env.header.moduleNames do
    names := names.insert m.toString
  let lines ← IO.FS.lines "Scratch/explore-20261024/repairs/doc_tokens.tsv"
  let mut out : Array String := #[]
  for l in lines do
    match l.splitOn "\t" with
    | [tok, loc] =>
      if tok.endsWith ".lean" then continue
      let tok' := if tok.startsWith "_root_." then (tok.drop 7).toString else tok
      unless names.contains tok' do out := out.push s!"{tok}\t{loc}"
    | _ => pure ()
  IO.FS.writeFile "Scratch/explore-20261024/repairs/doc_unresolved.tsv"
    ("\n".intercalate out.toList ++ "\n")
  IO.println s!"{out.size} unresolved of {lines.size}"
