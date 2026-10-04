import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

/-! Actual closed Integer statement/function acceptance. Both branches remain
in validation and consumed order; source allocations are covered by the formal
consumers and are not identified with the erased runtime heap. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerStatementsMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal

section Static

theorem actual_function {function : CheckedFunction} {arguments : List Int} {value : Int}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value) :
    Staged.Statements.FunctionChecked function arguments value := Staged.Statements.function_checked accepted

theorem actual_statements {source : TypedSource} {solved : List SolvedRequirement}
    {environment : Staged.Environment} {execute : Bool} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId} {result : StagedIntegerEvaluation}
    (accepted : Staged.Statements.evaluate solved source environment execute fuel site reason roots = .ok result) :
    Staged.Statements.Checked solved source environment execute fuel roots result := Staged.Statements.checked accepted

theorem actual_inputs {source : TypedSource} {seen : List Resolved.LocalId}
    {binders : List TypedBinder} {values : List Int} {environment : Staged.Environment}
    (accepted : Staged.Statements.bindInputs source seen binders values = .ok environment) :
    Staged.Statements.InputsChecked source seen binders values environment := Staged.Statements.inputs_checked accepted

/-- Acceptance supplies the full original roots and complete reconciliation. -/
theorem full_roots_and_ledger {function : CheckedFunction} {arguments : List Int} {value : Int}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value) :
    ∃ environment roots result,
      roots.map NodeId.statement = function.typedBody.roots ∧
      Staged.Statements.Checked function.solvedRequirements function.typedBody environment true
        (function.typedBody.nodes.length + 1) roots result ∧ result.value = value ∧
      reconcileConsumedRequirements function.declaration
        (function.solvedRequirements.map (·.id)) result.consumedRequirements = .ok [] := by
  cases Staged.Statements.function_checked accepted with
  | intro owned arity inferred type inputs roots checked value reconciled =>
    exact ⟨_, _, _, roots, checked, value, reconciled⟩

/-- The native staged binder validator does not replace source binder typing. -/
theorem malformed_scheme_has_no_source_extension
    {source : TypedSource} {context final : SourceSemantics.Context} {binder : TypedBinder}
    (mono : binder.scheme.quantified = []) (nonempty : binder.schemeRequirements ≠ [])
    (extended : SourceSemantics.BinderExtends source.owner context binder final) : False := by
  cases extended with
  | intro wellFormed fresh => exact nonempty (wellFormed.monomorphic_requirements_empty mono)
end Static

section SourceMeaning
open SourceSemantics SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning

/-- Public acceptance closes both the original ordered input allocation and
source statements. Original cells and selected let allocations remain explicit. -/
theorem actual_function_source
    {function : CheckedFunction} {arguments : List Int} {value : Int}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {before : Dynamic.Heap} {facts : BodyFacts}
    (accepted : evaluateStagedIntegerFunction function arguments = .ok value)
    (unique : NodeOccurrencesUnique function.typedBody)
    (typed : BodyHasType function.typedBody context .integer facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id))) :
    Staged.Statements.FunctionChecked function arguments value ∧
      ∃ environment bound roots final after added,
        roots.map NodeId.statement = function.typedBody.roots ∧
        Dynamic.BindersAllocate [] before function.typedBody.inputs
          (arguments.map Dynamic.Value.integer) environment bound ∧
        Dynamic.StatementsExecute program context evidence function.typedBody environment bound roots final
          (.returned (.integer value)) after ∧ Extends before after (arguments ++ added) :=
  SourceStagedIntegerStatementsMeaning.evaluateStagedIntegerFunction_sound accepted unique typed ledger valid

/-- Arbitrary existing cells need only satisfy the actual compiler environment
lookups. No whole-heap typing or erased runtime correspondence is assumed. -/
theorem actual_statements_source
    {program : Program} {context finalTyped : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {solved : List SolvedRequirement} {actual : Staged.Environment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {fuel : Nat}
    {site : ErrorSite} {reason : ErrorReason} {roots : List StatementId}
    {result : StagedIntegerEvaluation} {control : ControlContext} {facts : BodyFacts}
    (accepted : Staged.Statements.evaluate solved source actual true fuel site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (typed : StatementsHaveType source control context roots finalTyped facts)
    (ledger : context.solvedRequirements = solved)
    (environments : EnvironmentRep actual environment before)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.Statements.Checked solved source actual true fuel roots result ∧
      ∃ final after added,
        Dynamic.StatementsExecute program context evidence source environment before roots final
          (.returned (.integer result.value)) after ∧ Extends before after added :=
  statements_of_accepted accepted unique typed ledger environments valid

theorem original_cell {before after : Dynamic.Heap} {values : List Int}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (extension : Extends before after values) (read : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := extension.preserves_read read

theorem ordered_input_cells {source : TypedSource} {binders : List TypedBinder}
    {values : List Int} {actual : Staged.Environment}
    (accepted : Staged.Statements.bindInputs source [] binders values = .ok actual)
    (before : Dynamic.Heap) :
    ∃ environment after,
      Dynamic.BindersAllocate [] before binders (values.map Dynamic.Value.integer) environment after ∧
      EnvironmentRep actual environment after ∧ Extends before after values :=
  allocate (Staged.Statements.inputs_checked accepted) before

/-- Nonempty input allocation makes the source heap strictly longer. -/
theorem nonempty_inputs_grow {before after : Dynamic.Heap} {arguments added : List Int}
    (nonempty : arguments ≠ []) (extension : Extends before after (arguments ++ added)) :
    before.cells.length < after.cells.length := by
  have length := extension.length_eq
  have positive : 0 < arguments.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_append] at length
  omega

end SourceMeaning

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def content : String := String.intercalate "\n" [
  "function sequential(first: integer, second: integer) returns (integer) {",
  "  let x: integer = integerSub(first, second);",
  "  let y: integer = integerMul(x, 2);",
  "  return integerAdd(y, first);",
  "}",
  "function branch(comptime x: integer) returns (comptime<integer>) {",
  "  if (integerLt(x, 0)) {",
  "    let negative: integer = integerSub(0, x);",
  "    return integerAdd(negative, 3);",
  "  } else {",
  "    let positive: integer = integerAdd(x, 5);",
  "    return integerMul(positive, 2);",
  "  }",
  "}",
  "function nested() returns (integer) {",
  "  let outer: integer = 4;",
  "  { let inner: integer = integerAdd(outer, 6); return inner; }",
  "}",
  "function duplicate() returns (integer) { return integerAdd(3, 4); }",
  "function direct(x: integer) returns (integer) { return sequential(x, x); }"
]

private def named (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun function =>
      (program.environment.declaration? function.declaration).any fun entry => entry.name == some name with
  | some function => pure function
  | none => throw (IO.userError s!"missing function {name}")

private def roots (function : CheckedFunction) : IO (List StatementId) :=
  function.typedBody.roots.mapM fun
    | .statement statement => pure statement
    | .expression _ => throw (IO.userError "unexpected expression root")

private def evaluate (function : CheckedFunction) (arguments : List Int) (execute : Bool := true) :
    IO StagedIntegerEvaluation := do
  let environment ← match Staged.Statements.bindInputs function.typedBody [] function.typedBody.inputs arguments with
    | .ok environment => pure environment
    | .error error => throw (IO.userError s!"input binding rejected: {reprStr error}")
  let statements ← roots function
  match Staged.Statements.evaluate function.solvedRequirements function.typedBody environment execute
      (function.typedBody.nodes.length + 1) (.declaration function.declaration)
      .statementListFallthrough statements with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"statement evaluation rejected: {reprStr error}")

private def inspect (function : CheckedFunction) (arguments : List Int) (expected : Int) : IO Unit := do
  let result ← evaluate function arguments
  assertTrue (result.value == expected) "actual statement value changed"
  assertTrue (result.consumedRequirements == function.solvedRequirements.map (·.id))
    "statement consumption lost source order or an unselected branch"
  match evaluateStagedIntegerFunction function arguments with
  | .ok value => assertTrue (value == expected) "public function result changed"
  | .error error => throw (IO.userError s!"public function rejected: {reprStr error}")
  let disabled ← evaluate function arguments false
  assertTrue (disabled.consumedRequirements == result.consumedRequirements)
    "disabled statement validation lost consumption"

private def rejected (function : CheckedFunction) (arguments : List Int) : IO Unit :=
  match evaluateStagedIntegerFunction function arguments with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "tampered or unsupported function accepted")

/-- Actual checker output is tested separately from explicitly modified IR. -/
def run : IO Unit := do
  let program ← match checkProgram {
      entry := "main.solc", mainSources := [{ path := "main.solc", content }], externalLibraries := [] } with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"statement fixture check failed: {reprStr errors}")
  let sequential ← named program "sequential"
  let branch ← named program "branch"
  let nested ← named program "nested"
  let duplicate ← named program "duplicate"
  let direct ← named program "direct"
  inspect sequential [9, 2] 23
  inspect branch [-4] 7
  inspect branch [4] 18
  inspect nested [] 10
  inspect duplicate [] 7
  rejected direct [1]
  rejected sequential [9]
  let inputs := sequential.typedBody.inputs
  match inputs with
  | first :: second :: [] =>
      assertTrue (first.id != second.id && first.scheme.body == Ty.integer && second.scheme.body == Ty.integer)
        "checker input order or type changed"
      rejected { sequential with typedBody := { sequential.typedBody with inputs := [first, first] } } [9, 2]
  | _ => throw (IO.userError "expected two ordered inputs")
  let branchRoots ← roots branch
  let branchStatement ← match branchRoots with
    | [statement] => pure statement
    | _ => throw (IO.userError "branch roots changed")
  let elseBody ← match branch.typedBody.lookupStatement? branchStatement with
    | some { form := .ifThen _ _ (some body), .. } => pure body
    | _ => throw (IO.userError "terminal conditional changed")
  let last ← match elseBody.getLast? with
    | some statement => pure statement
    | none => throw (IO.userError "else branch vanished")
  let invalid := { branch with typedBody := { branch.typedBody with nodes := branch.typedBody.nodes.map fun
    | .statement node => if node.id == last then .statement { node with type := .word } else .statement node
    | node => node } }
  rejected invalid [-4]
  let invalidEnv ← match Staged.Statements.bindInputs invalid.typedBody [] invalid.typedBody.inputs [-4] with
    | .ok env => pure env | .error _ => throw (IO.userError "invalid test inputs")
  match Staged.Statements.evaluate invalid.solvedRequirements invalid.typedBody invalidEnv false
      (invalid.typedBody.nodes.length + 1) (.declaration invalid.declaration) .statementListFallthrough branchRoots with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "disabled validation skipped tampered unselected branch")
  -- An unused ledger row survives statement evaluation but public reconciliation rejects it.
  let extra ← match duplicate.solvedRequirements.head? with
    | some row => pure { row with id := ⟨100000⟩ }
    | none => throw (IO.userError "missing numeric row")
  let augmented := { duplicate with solvedRequirements := extra :: duplicate.solvedRequirements ++ [extra] }
  let original ← evaluate duplicate []
  let augmentedResult ← evaluate augmented []
  assertTrue (original == augmentedResult) "unused ledger rows changed statement traversal"
  match evaluateStagedIntegerFunction augmented [] with
  | .error { reason := .unconsumedRequirements remaining, .. } =>
      assertTrue (remaining == [extra.id, extra.id]) "unused full ledger order changed"
  | _ => throw (IO.userError "public reconciliation lost exact unused ledger rows")
  -- Repeated references are modified retained IR, not fresh checker output.
  let (call, callee, left) ← match duplicate.typedBody.nodes.filterMap (fun
      | .expression node => match node.form with
        | .call callee [left, _] (.builtinFunction .integerAdd) => some (node, callee, left)
        | _ => none
      | _ => none) with
    | [selected] => pure selected
    | _ => throw (IO.userError "duplicate fixture call changed")
  let requirement ← match duplicate.typedBody.lookupExpression? left with
    | some { form := .integerLiteral _ resolution, .. } => pure resolution.requirement
    | _ => throw (IO.userError "duplicate fixture literal changed")
  let repeated := { duplicate with typedBody := { duplicate.typedBody with nodes := duplicate.typedBody.nodes.map fun
    | .expression node => if node.id == call.id then
        .expression { node with form := .call callee [left, left] (.builtinFunction .integerAdd) }
      else .expression node
    | node => node } }
  let repeatedResult ← evaluate repeated []
  assertTrue (repeatedResult.value == 6 && repeatedResult.consumedRequirements == [requirement, requirement])
    "actual ordered duplicate consumption changed"
  match evaluateStagedIntegerFunction repeated [] with
  | .error { reason := .duplicateConsumedRequirement actual, .. } =>
      assertTrue (actual == requirement) "public duplicate rejection named a different row"
  | _ => throw (IO.userError "public reconciliation accepted duplicate consumption")
end Tests.SourceCoreStagedIntegerStatementsMeaning
