import Lean
open Lean
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := args[0]!.toName }] {} (trustLevel := 1024) (loadExts := true)
  for a in args.drop 1 do
    let n := a.toName
    match env.find? n with
    | some ci =>
      IO.println s!"== {n} : {ci.type}"
      if let some v := ci.value? (allowOpaque := true) then IO.println s!"   := {v}"
    | none => IO.println s!"not found {n}"
