import Lean.Data.Json
import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.Lowering

/-! Command-line execution of a versioned checked-Hull export through Core. -/
set_option autoImplicit false

open Lean Solcore Solcore.Frontend.RustHull

private def resultJson : Core.Value → Json
  | .word value => Json.mkObj [("kind", "word"), ("value", toJson (toString value.val))]
  | .bool value => Json.mkObj [("kind", "bool"), ("value", toJson value)]
  | .unit => Json.mkObj [("kind", "unit")]
  | .pair left right => Json.mkObj [("kind", "product"), ("left", resultJson left), ("right", resultJson right)]
  | .inLeft _ value => Json.mkObj [("kind", "inl"), ("value", resultJson value)]
  | .inRight _ value => Json.mkObj [("kind", "inr"), ("value", resultJson value)]
  | other => Json.mkObj [("kind", "unsupported-output"), ("detail", toJson (reprStr other))]

private def report (stage status : String) (details : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj ([("stage", toJson stage), ("status", toJson status)] ++ details)).compress)

def main (args : List String) : IO UInt32 := do
  let file :: rest := args | do
    IO.eprintln "usage: lean --run Tests/RustHullRun.lean EXPORT.json [ENTRY [WORD...]]"
    return 2
  let raw ← IO.FS.readFile file
  let envelope ← match decodeText raw with
    | .ok envelope => pure envelope
    | .error error => do
        report "transport" "rejected" [("detail", toJson (reprStr error))]
        return 1
  let (entry, inputs) ← match rest with
    | entry :: inputs => pure (entry, inputs)
    | [] => match envelope.program.entryPoints with
      | [entry] => pure (entry, [])
      | entries => do
          report "entry" "rejected" [("detail", "select one entry"), ("entries", toJson entries)]
          return 1
  let compiled ← match compile envelope.program entry with
    | .ok compiled => pure compiled
    | .error error => do
        report "lowering" "rejected" [("detail", toJson (reprStr error))]
        return 1
  unless inputs.length = compiled.parameters.length do
    report "input" "rejected" [("detail", "argument count mismatch")]
    return 1
  let mut values := []
  for (input, type) in inputs.zip compiled.parameters do
    let value : LowerM Core.Expr := match type with
      | .word => return .word (← parseWord input)
      | .bool => if input = "true" then pure (.bool true)
          else if input = "false" then pure (.bool false)
          else fail "Boolean input must be true or false"
      | .sum .unit .unit => if input = "true" then pure (.inRight .unit .unit)
          else if input = "false" then pure (.inLeft .unit .unit)
          else fail "Boolean input must be true or false"
      | .unit => if input = "unit" then pure .unit else fail "Unit input must be unit"
      | _ => fail "CLI input supports Word, Bool and Unit"
    match value with
    | .error error =>
        report "input" "rejected" [("detail", toJson (reprStr error))]
        return 1
    | .ok value => values := values ++ [value]
  let expression := Core.Expr.apply compiled.expression (bundle values)
  match Core.runStateful 10000000 (.initial expression) with
  | .done (.inRight _ value) store =>
      report "execution" "succeeded" [("value", resultJson value), ("heapCells", toJson store.length)]
      return 0
  | .done (.inLeft _ value) _ =>
      report "execution" "failed" [("reason", resultJson value)]
      return 1
  | .done value _ =>
      report "execution" "invalid-result" [("value", resultJson value)]
      return 1
  | .outOfFuel _ =>
      report "execution" "out-of-fuel" []
      return 1
  | .fault error _ =>
      report "execution" "core-fault" [("detail", toJson (reprStr error))]
      return 1
