import Solcore.Synthesis.Core.CallGraphGenerator
import Solcore.Core.Machine

/-! Generator regressions use the original checked Core program. Structural
coverage below describes generated syntax, not measured compiler/EVM traces. -/
set_option autoImplicit false

namespace Tests.CallGraphGenerator

open Solcore.Core
open Solcore.Synthesis.Core

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def generated (seed budget : Nat) : IO CallGraph.Generated :=
  match CallGraph.generate {seed := Seed.ofNat seed, maxProgramNodes := budget} with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"call graph generation failed at {seed}/{budget}: {reprStr error}")

private def invariantChecks (value : CallGraph.Generated) : IO Unit := do
  ensure value.function.program.check "generated function is not accepted by the whole Core checker"
  ensure ((value.function.instantiate Word.maximum).check) "runtime application is not typed"
  ensure (value.nodeCount ≤ value.maxProgramNodes) "actual applied graph exceeds its budget"
  ensure (value.function.helpers.length ≥ 1 && value.function.helpers.length ≤ 3)
    "helper count is outside the supported range"
  ensure (value.bodyBudgets.length == value.function.helpers.length + 1 &&
      value.bodyBudgets.all (· > 0) &&
      value.bodyBudgets.foldl (· + ·) 0 + CallGraph.appliedOverhead value.function.helpers.length ==
        value.maxProgramNodes) "body allocations do not account for the exact whole-program budget"
  for (body, budget) in (value.function.helpers ++ [value.function.entry]).zip value.bodyBudgets do
    ensure (Wire.exprNodes body ≤ budget) "generated body exceeds its assigned expression budget"
  let some decoded := CheckedWordFunctionDAG.ofProgram? value.program |
    throw (IO.userError "generated original program cannot be readmitted")
  ensure (Wire.encodeProgram decoded.program == Wire.encodeProgram value.program)
    "readmission changed the original graph"

private def boundsAndReplay : IO Unit := do
  ensure (CallGraph.version == "core-call-graph-grammar-v1/lcg64-v1") "generator version drift"
  for count in [1, 2, 3] do
    let minimum := CallGraph.minimumAppliedNodes count
    ensure (minimum == CallGraph.appliedOverhead count + count + 1)
      "minimum graph accounting omitted a body or a wrapper"
  ensure ([1, 2, 3].map CallGraph.minimumAppliedNodes == [13, 18, 23] &&
    [1, 2, 3].map CallGraph.appliedOverhead == [11, 15, 19])
    "canonical applied wrapper accounting changed"
  for (seed, finalSeed, count, budgets, nodes) in [
      (0, 10886584781152613473, 2, [33, 6, 42], 59),
      (1, 4158591199845347631, 2, [56, 2, 23], 72),
      (7, 4960277783812433452, 2, [15, 47, 19], 87),
      (31, 7742363979015232405, 1, [68, 17], 67)] do
    let value ← generated seed 96
    ensure (value.finalSeed.toNat == finalSeed && value.function.helpers.length == count &&
      value.bodyBudgets == budgets && value.nodeCount == nodes)
      "versioned choice order or budget distribution changed"
  for budget in [0, CallGraph.minimumAppliedNodes 1 - 1] do
    ensure (match CallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := budget} with
      | .error .budgetTooSmall => true | _ => false) "undersized budget was not rejected"
  ensure (match CallGraph.generate {seed := Seed.ofNat 0, maxProgramNodes := 513} with
    | .error .budgetTooLarge => true | _ => false) "oversized budget was not rejected"
  for budget in [CallGraph.minimumAppliedNodes 1, 24, 48, 96, 256, 512] do
    for seed in [0, 1, 2, 3, 7, 31, 127, 255, 65535, 2 ^ 64 - 1] do
      let first ← generated seed budget
      let second ← generated seed budget
      invariantChecks first
      ensure (Wire.encodeProgram first.program == Wire.encodeProgram second.program &&
        first.initialSeed == Seed.ofNat seed && first.finalSeed == second.finalSeed &&
        first.bodyBudgets == second.bodyBudgets) "seed replay changed the graph or generation provenance"
  let minimum ← generated 0 (CallGraph.minimumAppliedNodes 1)
  ensure (minimum.nodeCount == CallGraph.minimumAppliedNodes 1) "minimum request was not exact"
  ensure ((CheckedWordFunctionDAG.ofParts? [.apply (.var 1) (.var 0)] (.var 0)).isNone)
    "a helper was allowed to call itself"
  ensure ((CheckedWordFunctionDAG.ofParts? [.var 0] (.apply (.var 2) (.var 0))).isNone)
    "an out-of-scope helper was admitted"

/-- A bounded census of generated ASTs guards against silently reverting to the
old immediate-predecessor chain or fixed aggregate templates. -/
private def structuralDiversity : IO Unit := do
  let mut shapes : List String := []
  let mut features : List String := []
  let mut counts : List Nat := []
  let mut programs : List String := []
  for seed in List.range 256 do
    let value ← generated seed 256
    invariantChecks value
    shapes := (shapes ++ CallGraph.structuralShapes value.function).eraseDups
    features := (features ++ value.features).eraseDups
    counts := (value.function.helpers.length :: counts).eraseDups
    programs := (Wire.encodeProgram value.program).compress :: programs
  for shape in ["skipped-helper", "multiple-callees", "shared-callee", "nested-call",
      "branch-call", "local-call", "diamond", "predicate-call", "primitive-operand-call"] do
    ensure (shapes.contains shape) s!"generated graph census lacks {shape}"
  let scalarFeatures := ["wordLiteral", "boolLiteral", "local", "let", "if"] ++
    (unaryOps.toList.map fun operation => "unary:" ++ reprStr operation) ++
    (binaryOps.toList.map fun operation => "binary:" ++ reprStr operation) ++
    (ternaryOps.toList.map fun operation => "ternary:" ++ reprStr operation)
  for feature in scalarFeatures do
    ensure (features.contains feature) s!"generated scalar grammar lacks {feature}"
  ensure (features.contains "functionCall") "call form was never generated"
  ensure ([1, 2, 3].all counts.contains) "helper counts did not vary"
  ensure (programs.eraseDups.length > 240) "seed census collapsed to too few graph shapes"

private def executionChecks : IO Unit := do
  for seed in [0, 1, 2, 3, 7, 31, 127, 255] do
    let value ← generated seed 96
    let program := value.function.instantiate (Word.ofNatModulo 7)
    match program.toCore.runStateful 0 with
    | .outOfFuel _ => pure ()
    | _ => throw (IO.userError "zero fuel was treated as a completed generated execution")
    match program.toCore.runStateful 100000 with
    | .done (.word _) _ => pure ()
    | .outOfFuel _ => throw (IO.userError "bounded generated execution exhausted its test budget")
    | _ => throw (IO.userError "checked generated graph did not return a Word")

def testCallGraphGenerator : IO Unit := do
  boundsAndReplay
  structuralDiversity
  executionChecks

end Tests.CallGraphGenerator
