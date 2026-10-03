import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Consumers retain actual preparation slots, binder positions and raw types.
Packed types alone do not identify a parameter vector of unknown arity. The
runtime fixture inspects every real prepared input and its accumulated scope. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedParameterProjections
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open RecursiveNamedPreparedParameterProjections

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {slot : Nat} {named : SourceCoreGeneralFunctions.Function}
  (selected : compiled.indexed.base.functions[slot]? = some named)

include selected in
theorem actual_preparation :
    ∃ specialized, compiled.compatible.prepared.plan.specializations.reverse[slot]? = some specialized ∧
      SourceCoreGeneralFunctions.prepareFunctionWithRepresentation compiled.sourceProgram
        (SourceCoreCompatibleFunctions.representation (.initial compiled.compatible.checked) compiled.compilationFuel)
        specialized = .ok named := cached_preparation compiled selected

include selected in
theorem actual_binder_order :
    named.inputs.map Prod.fst = named.specialized.function.typedBody.inputs :=
  (cached_inputs compiled selected).1

include selected in
theorem actual_prefix {position : Nat} {binding : TypedBinder × Core.Ty}
    (found : named.inputs[position]? = some binding) :
    SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked
      named.specialized.function.typedBody
      ((named.inputs.take position).reverse.map (fun item => (item.1.id, item.2))) binding.1 = .ok binding.2 :=
  (cached_inputs compiled selected).2 position binding found

include selected in
theorem actual_projections :
    (named.inputs.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project =
      .ok (named.inputs.map Prod.snd) := cached_projected compiled selected

/-- The Header's source binders agree with the actual prepared list. The result
still names the actual native vector, not the Header's separately supplied one. -/
theorem actual_header_raw {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment}
    {program : SourceSemantics.Program} (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program)
    (selectedHeader : compiled.indexed.base.functions[header.slot]? = some header.named) :
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project =
      .ok (header.named.inputs.map Prod.snd) := by
  have same := header.parameters.symm.trans header.agreement.parameters
  have raw := congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) same
  simp only [List.map_map, Function.comp_def] at raw
  rw [raw]
  exact cached_projected compiled selectedHeader
end Formal

theorem packed_unit_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [] = SourceCoreCompatibleCatalog.packTypes [.unit] ∧
      ([] : List Core.Ty) ≠ [.unit] := by decide

theorem packed_product_arity_boundary :
    SourceCoreCompatibleCatalog.packTypes [.product .word .bool] =
      SourceCoreCompatibleCatalog.packTypes [.word, .bool] ∧
      ([.product .word .bool] : List Core.Ty) ≠ [.word, .bool] := by decide

private def content : String := String.intercalate "\n" [
  "function empty() {}",
  "function unitArg(value: Unit) returns (Unit) { return value; }",
  "function mixed(first: Word, middle: Bool, last: Word) returns (Word) { return first + last; }",
  "function tupleArg(value: (Word, Bool)) returns (Word) { return 3; }",
  "function choose<A, B>(first: A, second: B) returns (A) { return first; }",
  "function fail(first: Word, second: Word) returns (Word) { let gap: Word; return gap; }",
  "function rootUnit() returns (Unit) { return unitArg(()); }",
  "function rootMixed() returns (Word) { return mixed(7, true, 7); }",
  "function rootTuple() returns (Word) { return tupleArg((7, true)); }",
  "function rootGeneric() returns (Word) { return choose(9, false); }",
  "function rootFault() returns (Word) { return fail(5, 5); }"
]
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let representation := SourceCoreCompatibleFunctions.representation (.initial compiled.compatible.checked) compiled.compilationFuel
  let mut emptyCount := 0
  let mut singletonCount := 0
  let mut manyCount := 0
  let mut genericCount := 0
  let mut total := 0
  for (named, slot) in compiled.indexed.base.functions.zipIdx do
    let specialized ← match compiled.compatible.prepared.plan.specializations.reverse[slot]? with
      | some specialized => pure specialized
      | none => throw (IO.userError "prepared parameter specialization slot missing")
    let actual ← get "actual named preparation" (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation
      compiled.sourceProgram representation specialized)
    require (reprStr actual == reprStr named) "full prepared function/slot changed"
    require (reprStr (named.inputs.map Prod.fst) == reprStr specialized.function.typedBody.inputs)
      "original ordered input binders changed"
    if named.inputs.isEmpty then emptyCount := emptyCount + 1
    else if named.inputs.length == 1 then singletonCount := singletonCount + 1
    else manyCount := manyCount + 1
    if !specialized.parameterSubstitution.isEmpty then genericCount := genericCount + 1
    for (binding, position) in named.inputs.zipIdx do
      let preceding := (named.inputs.take position).reverse.map (fun item => (item.1.id, item.2))
      let native ← get "actual input prefix admission"
        (representation.expressions.lowerBinder specialized.function.typedBody preceding binding.1)
      require (native == binding.2) "actual binder native type changed"
      let projected ← get "actual raw input projection" (compiled.compatible.checked.catalog.project binding.1.scheme.body)
      require (projected == binding.2) "raw binder projection changed"
      require (preceding.length == position) "actual ordered prefix lost a binder"
      total := total + 1
    let vector ← get "actual ordered native input vector"
      ((named.inputs.map (fun binding => binding.1.scheme.body)).mapM compiled.compatible.checked.catalog.project)
    require (vector == named.inputs.map Prod.snd) "actual whole native vector/order changed"
  require (emptyCount == 6 && singletonCount == 2 && manyCount == 3 && genericCount == 1 && total == 9)
    s!"prepared parameter fixture coverage changed {emptyCount}/{singletonCount}/{manyCount}/{genericCount}/{total}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String) (fuel : Nat)
    (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
  pure (← get "prepared parameters public resume" (first.resume 300000)).observation

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) : IO Unit := do
  require (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap) "prepared parameters initial heap changed"
  require (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"prepared parameters full ordered source cells changed: {reprStr final.heap}"

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "recursive named prepared parameter projections" content
    ["empty", "rootUnit", "rootMixed", "rootTuple", "rootGeneric", "rootFault"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 813)⟩]}
  let successes : List (String × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("empty", .unit, []),
    ("rootUnit", .unit, [(.unit, some .unit)]),
    ("rootMixed", w 14, [(.word, some (w 7)), (.bool, some (.bool true)), (.word, some (w 7))]),
    ("rootTuple", w 3, [(.product .word .bool, some (.product (w 7) (.bool true)))]),
    ("rootGeneric", w 9, [(.word, some (w 9)), (.bool, some (.bool false))])]
  let baselines ← successes.mapM (fun row => finish compiled row.1 300000 initial)
  let faultBaseline ← finish compiled "rootFault" 300000 initial
  for fuel in [0, 43, 300000] do
    for (test, baseline) in successes.zip baselines do
      let (name, expected, expectedCells) := test
      let observed ← finish compiled name fuel initial
      require (reprStr observed == reprStr baseline) s!"prepared parameter resume changed {name}"
      match observed with
      | .done value final =>
        require (reprStr value == reprStr expected) s!"prepared parameter result changed {name}"
        cells initial final expectedCells
      | _ => throw (IO.userError s!"prepared parameter expected completion {name}")
    let observed ← finish compiled "rootFault" fuel initial
    require (reprStr observed == reprStr faultBaseline) "prepared parameter fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final => cells initial final [(.word, some (w 5)), (.word, some (w 5)), (.word, none)]
    | _ => throw (IO.userError "prepared parameter fault prefix changed")
  IO.println "recursive named prepared parameters: actual ordered full-prefix preparation/raw projections, Unit/product arities, duplicate types, whole cells and resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedParameterProjections
