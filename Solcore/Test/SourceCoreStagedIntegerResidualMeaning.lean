import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

/-! Actual pure compatibility elaboration with retained scalar inputs and
Integer-let erasure. The Source heap and Core store remain distinct states. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerResidualMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal SourceSemantics SourceSemantics.CoreLowering
open SourceStagedIntegerResidualMeaning

abbrev actual_expression := @expression_meaning
abbrev actual_statements := @statements_of_accepted
abbrev actual_public_function := @elaborateFunction_sound
abbrev retained_inputs := @inputs_heaps
abbrev actual_typed_inputs := @inputs_typed
abbrev actual_dropped_binding := @MixedEnvironment.erase_allocated

theorem artifact_type (artifact : ElaboratedFunction) :
    Resolved.HasType artifact.inputs artifact.resolved artifact.returnType := artifact_typed artifact

/-- Integer-let execution grows the Source heap even when Core stays pure. -/
theorem source_heap_grows {before after : Dynamic.Heap} {head : Int} {tail : List Int}
    (cells : SourceStagedIntegerStatementsMeaning.Extends before after (head :: tail)) : after ≠ before := by
  have length := cells.length_eq
  intro same
  subst after
  simp only [List.length_cons] at length
  omega

/-- The full captured-environment relation cannot drop a lexical row. -/
theorem captures_keep_length {mapping : SourceStagingHeapRelation.LocationMap}
    {source residual : Dynamic.Environment}
    (related : SourceStagingHeapRelation.EnvironmentRel mapping source residual) :
    source.length = residual.length := related.length

/-- The scalar ABI deliberately excludes staged Integer payloads. -/
theorem integer_is_not_runtime_scalar (value : Int) (native : Core.Value) :
    ¬ ScalarRep (.integer value) native := by intro impossible; cases impossible

/-- Runtime Word and Bool cells cannot occupy a dropped mapping position. -/
theorem runtime_scalar_not_dropped {mapping : SourceStagingHeapRelation.LocationMap}
    {source residual : Dynamic.Heap} {location : Dynamic.Location}
    {value : Dynamic.Value} {native : Core.Value} {type : TypeSystem.Ty}
    (related : SourceStagingHeapRelation.HeapRel mapping source residual)
    (read : Dynamic.Heap.Reads source location {type := type, value := some value})
    (scalar : ScalarRep value native)
    (dropped : mapping[location.index]? = some none) : False := by
  obtain ⟨cell, found, integer, equal⟩ := related.dropped location.index dropped
  cases read with
  | intro actual =>
    have selectedEq : ∀ {cells index cell}, Dynamic.Heap.CellAt cells index cell → cells[index]? = some cell := by
      intro cells index cell selected
      induction selected with
      | head => rfl
      | tail selected ih => exact ih
    have actualEq := selectedEq actual
    have same := Option.some.inj (actualEq.symm.trans found)
    have values := congrArg Dynamic.Cell.value (same.trans equal)
    cases scalar <;> cases values

theorem pure_store {environment : Resolved.Environment} {before after : Core.Store}
    {expression : Resolved.Expr} {value : Core.Value}
    (evaluated : Resolved.Evaluates environment before expression value after) : after = before :=
  evaluated.store_eq

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α : Type} (message : String) : Except SourceCoreElaboration.Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{message}: {reprStr error}")
private def word (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def content : String := String.intercalate "\n" [
  "function scalar(flag: Bool, value: Word) returns (Word) { let x: integer = integerAdd(20, 22); return flag ? value : wordFromInteger(x); }",
  "function equal(value: Word) returns (Bool) { let x: integer = 3; let y: integer = integerMul(x, 2); return integerEq(y, 6); }",
  "function less(flag: Bool) returns (Bool) { let x: integer = integerSub(0, 3); return flag ? integerLt(x, 0) : false; }",
  "function branches(flag: Bool, value: Word) returns (Word) { if (flag) { let x: integer = 10; return wordFromInteger(x); } else { let y: integer = 99; return value; } }",
  "function block(value: Word) returns (Word) { { let x: integer = 5; let y: integer = integerAdd(x, x); return (wordFromInteger(y)); } }",
  "function empty(flag: Bool) returns (Bool) { return flag; }",
  "function literal() returns (Word) { return 7; }",
  "function arithmetic() returns (Word) { let x: integer = true ? integerMul(6, 7) : integerSub(0, 1); return wordFromInteger(x); }"
]

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry => entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"missing residual function {name}")

private def inspect (function : CheckedFunction) (native : List Core.Value) (expectedValue : Core.Value) : IO Unit := do
  let scope ← get "actual input scope" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let projected ← get "actual return type" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let roots := SourceStagedIntegerResidualMeaning.statementRoots function.typedBody
  let fuel := function.typedBody.nodes.length + 1
  require (Staged.Residual.statementsSupported function.typedBody fuel roots) "actual supported statement tree"
  let site := match Staged.IntegerLet.lastStatement roots with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  let result ← get "actual lowering" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody
    scope [] fuel projected site .statementListFallthrough roots)
  let draft ← get "actual draft" (lowerFunctionBody function)
  let artifact ← get "actual public elaboration" (elaborateFunction function)
  require (scope == draft.inputs && scope == artifact.inputs && result.resolved == draft.resolved &&
    result.resolved == artifact.resolved && projected == artifact.returnType && draft.unconsumedRequirements.isEmpty)
    "draft/finalized artifact differs from the accepted private result"
  require (result.consumedRequirements == function.solvedRequirements.map (·.id)) "ordered whole consumed ledger"
  require (artifact.resolved.lower? artifact.inputs.ids == some artifact.core &&
    Core.infer? artifact.inputs.values artifact.core == some artifact.returnType) "actual positional/type receipts"
  let store : Core.Store := [.bool true, .unit, .integer (-17), word 901]
  for fuel in [0, 1, 2, 5] do
    let actual := match Core.runStateful fuel (.initial artifact.core native store) with
      | .outOfFuel remaining => Core.runStateful 200 remaining
      | result => result
    require (actual == .done expectedValue store) "pure actual code result/full original store or resume changed"

/-- The IO fixtures exercise the actual default compatibility API. They do not
stand in for a public unified compilation or physical-cell correspondence. -/
def run : IO Unit := do
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content}], externalLibraries := []} with
    | .ok program => pure program | .error errors => throw (IO.userError s!"residual checker: {reprStr errors}")
  for (name, values, expected) in [
      ("scalar", [.bool true, word 77], word 77), ("scalar", [.bool false, word 77], word 42),
      ("equal", [word 0], .bool true), ("less", [.bool true], .bool true), ("less", [.bool false], .bool false),
      ("branches", [.bool true, word 31], word 10), ("branches", [.bool false, word 31], word 31),
      ("block", [word 12], word 10), ("empty", [.bool false], .bool false),
      ("literal", [], word 7), ("arithmetic", [], word 42)] do
    inspect (← named program name) values expected
  let scalar ← named program "scalar"
  let extra ← match scalar.solvedRequirements.head? with
    | some row => pure {row with id := ⟨100000⟩} | none => throw (IO.userError "missing numeric row")
  let original ← get "original draft" (lowerFunctionBody scalar)
  let augmented ← get "unused ordered rows draft" (lowerFunctionBody {scalar with solvedRequirements := extra :: scalar.solvedRequirements ++ [extra]})
  require (augmented.resolved == original.resolved && augmented.unconsumedRequirements == [extra.id, extra.id])
    "unused prefix/suffix ledger was filtered or reordered"
  match augmented.finalize with
  | .error {reason := .unconsumedRequirements remaining, ..} =>
      require (remaining == [extra.id, extra.id]) "exact unused remainder"
  | _ => throw (IO.userError "unused ledger passed actual finalization")
  -- This retained-IR modification targets the dynamically unselected arm.
  let scalar ← named program "scalar"
  let no ← match scalar.typedBody.nodes.filterMap (fun
      | .expression {form := .conditional _ _ no, ..} => some no | _ => none) with
    | [no] => pure no | _ => throw (IO.userError "missing conditional")
  let tampered := {scalar with typedBody := {scalar.typedBody with nodes := scalar.typedBody.nodes.map fun
    | .expression node => if node.id == no then .expression {node with requirements := [⟨100001⟩]} else .expression node
    | node => node}}
  match elaborateFunction tampered with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "tampered unselected arm escaped validation")
end Tests.SourceCoreStagedIntegerResidualMeaning
