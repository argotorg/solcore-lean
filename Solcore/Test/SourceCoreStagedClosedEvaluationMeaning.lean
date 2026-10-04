import Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning

/-! The static boundary and actual accepted closed staged expressions. The
validation mode checks both branches; only execution mode has source meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedClosedEvaluationMeaning
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference Solcore.TypeSystem
open Solcore.Frontend.SourceCoreElaboration
open Solcore.Frontend.SourceCoreElaboration.Internal

section Boundary
variable {solved : List SolvedRequirement} {source : TypedSource}
  {expression : ExpressionId}

theorem actual_integer {result : StagedIntegerEvaluation}
    (accepted : evaluateStagedInteger solved source expression = .ok result) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedInteger_checked accepted

theorem actual_word {result : StagedWordEvaluation}
    (accepted : evaluateStagedWord solved source expression = .ok result) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedWord_checked accepted

theorem actual_bool {result : StagedBoolEvaluation}
    (accepted : evaluateStagedBool solved source expression = .ok result) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) expression result :=
  Staged.evaluateStagedBool_checked accepted

/-- Disabled evaluation returns a validation tree; this theorem assigns no
source meaning to its placeholder result. -/
theorem disabled_integer {environment : Staged.Environment} {fuel : Nat}
    {result : StagedIntegerEvaluation}
    (accepted : Staged.integer solved source environment false fuel expression = .ok result) :
    Staged.IntegerChecked solved source environment false fuel expression result :=
  Staged.integer_checked accepted

/-- Full callee validation remains attached to the actual ordered arguments. -/
theorem actual_callee {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {function : BuiltinFunctionId}
    (checked : Staged.BuiltinChecked source node callee arguments function) :
    validateBuiltinFunctionCall source node callee arguments function = .ok () ∧
      node.requirements = [] ∧ node.coercions = [] :=
  ⟨checked.accepted, checked.requirements, checked.coercions⟩

/-- Consumed requirements form an ordered list, including repeated occurrences. -/
theorem repeated_consumption (requirement : RequirementId) :
    [requirement] ++ [requirement] = [requirement, requirement] ∧
      ([requirement] ++ [requirement]).length = 2 := ⟨rfl, rfl⟩
end Boundary


section SourceMeaning
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning
variable {program : Program} {context : Solcore.SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {source : TypedSource}
  {environment : Dynamic.Environment} {heap : Dynamic.Heap} {expression : ExpressionId}

/-- The public accepted result itself supplies the exact receipt; no source
execution premise, unique-node assumption, or full-ledger validity is supplied. -/
theorem integer_source {result : StagedIntegerEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedInteger solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.IntegerChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.integer result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedInteger_sound ledger accepted valid

theorem word_source {result : StagedWordEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedWord solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.WordChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.word result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedWord_sound ledger accepted valid

theorem bool_source {result : StagedBoolEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedBool solved source expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Staged.BoolChecked solved source [] true (source.nodes.length + 1) expression result ∧
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.bool result.value) heap :=
  SourceStagedClosedEvaluationMeaning.evaluateStagedBool_sound ledger accepted valid

/-- Actual function-local Integer cells are related by compiler lookup and
ordinary initialized source cells, without changing the heap. -/
theorem local_environment {actual : Staged.Environment} {fuel : Nat}
    {result : StagedIntegerEvaluation}
    (ledger : context.solvedRequirements = solved)
    (related : EnvironmentRep actual environment heap)
    (accepted : Staged.integer solved source actual true fuel expression = .ok result)
    (valid : UsedValid context solved result.consumedRequirements) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.integer result.value) heap :=
  (integer_of_accepted ledger related accepted valid).2

/-- A receipt that consumes no numeric requirements imposes no validity
condition on any ledger row, including unused implementation rows. -/
theorem no_numeric_validity {result : StagedBoolEvaluation}
    (ledger : context.solvedRequirements = solved)
    (accepted : evaluateStagedBool solved source expression = .ok result)
    (empty : result.consumedRequirements = []) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap expression (.bool result.value) heap := by
  apply (SourceStagedClosedEvaluationMeaning.evaluateStagedBool_sound ledger accepted ?_).2
  intro row proof member used implementation
  rw [empty] at used
  cases used

/-- The actual environment relation is vacuous for the closed public wrappers;
no assumptions on unrelated source heap cells are added. -/
theorem closed_environment : EnvironmentRep [] environment heap := EnvironmentRep.empty _ _
end SourceMeaning

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def workspace (content : String) : Workspace.RawWorkspace := {
  entry := "main.solc", mainSources := [{ path := "main.solc", content }], externalLibraries := [] }

private def sourceText : String := String.intercalate "\n" [
  "function arithmetic() returns (Word) { return wordFromInteger((integerLt(1, 2) ? integerMul(integerAdd(3, 4), integerSub(9, 2)) : wordToInteger(17))); }",
  "function words() returns (Word) { return false ? 7 : 9; }",
  "function booleans() returns (Bool) { return true ? integerEq((1), (1)) : integerLt(3, 2); }",
  "function duplicate() returns (Word) { return wordFromInteger(integerAdd(3, 4)); }",
  "function unused() returns (Word) { return 31; }"
]

private def functionNamed (program : CheckedProgram) (name : String) : IO CheckedFunction :=
  match program.functions.find? fun fn =>
      (program.environment.declaration? fn.declaration).any fun decl => decl.name == some name with
  | some fn => pure fn
  | none => throw (IO.userError s!"missing staged fixture {name}")

private def returned (fn : CheckedFunction) : IO ExpressionId :=
  match fn.typedBody.roots with
  | [.statement statement] => match fn.typedBody.lookupStatement? statement with
    | some { form := .returnStmt (some expression), .. } => pure expression
    | _ => throw (IO.userError "missing staged return")
  | _ => throw (IO.userError "unexpected staged roots")

private def change (source : TypedSource) (expression : ExpressionId)
    (update : ExpressionNode → ExpressionNode) : TypedSource := {
  source with nodes := source.nodes.map fun
    | .expression node => if node.id = expression then .expression (update node) else .expression node
    | .statement node => .statement node }

private def wordResult (solved : List SolvedRequirement) (source : TypedSource)
    (expression : ExpressionId) : IO StagedWordEvaluation :=
  match evaluateStagedWord solved source expression with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"word staging failed: {reprStr error}")

/-- Actual checker output exercises all seven builtins, all three conditional
result types, groups, disabled validation, and ordered complete consumption. -/
def run : IO Unit := do
  let program ← match checkProgram (workspace sourceText) with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"staged fixture checking: {reprStr error}")
  let unused ← functionNamed program "unused"
  -- The surrounding unused rows are explicit ledger augmentation. Their fresh
  -- ID is independent of the checker-produced requirement sequence.
  let unusedRow ← match unused.solvedRequirements with
    | [row] => pure { row with id := ⟨100000⟩ }
    | _ => throw (IO.userError "expected one unused numeric row")
  for (name, expected) in [("arithmetic", 49), ("words", 9), ("duplicate", 7)] do
    let fn ← functionNamed program name
    let root ← returned fn
    let result ← wordResult fn.solvedRequirements fn.typedBody root
    assertTrue (result.value == Core.Word.ofNatModulo expected &&
        result.consumedRequirements == fn.solvedRequirements.map (·.id))
      s!"{name}: value or complete ordered consumption changed"
    let extended := unusedRow :: (fn.solvedRequirements ++ [unusedRow])
    let padded ← wordResult extended fn.typedBody root
    assertTrue (padded == result) s!"{name}: unused prefix/suffix changed staging"
    match Staged.word extended fn.typedBody [] false (fn.typedBody.nodes.length + 1) root with
    | .ok disabled =>
        assertTrue (disabled.value == Core.Word.ofNatModulo (if name == "words" then 9 else 0))
          s!"{name}: validation-only placeholder boundary changed"
        assertTrue (disabled.consumedRequirements == result.consumedRequirements)
          s!"{name}: disabled traversal lost branch consumption"
    | .error error => throw (IO.userError s!"{name}: disabled validation failed: {reprStr error}")
  let boolFn ← functionNamed program "booleans"
  let boolRoot ← returned boolFn
  match evaluateStagedBool boolFn.solvedRequirements boolFn.typedBody boolRoot with
  | .ok result =>
      assertTrue (result.value && result.consumedRequirements == boolFn.solvedRequirements.map (·.id))
        "Bool group/conditional/comparison or all-branch consumption changed"
  | .error error => throw (IO.userError s!"Bool staging failed: {reprStr error}")
  let arithmetic ← functionNamed program "arithmetic"
  let arithmeticRoot ← returned arithmetic
  let inactive ← match arithmetic.typedBody.nodes.find? fun
      | .expression { form := .call _ _ (.builtinFunction .wordToInteger), .. } => true
      | _ => false with
    | some (.expression { form := .call callee _ _, .. }) => pure callee
    | _ => throw (IO.userError "missing inactive conversion callee")
  let tampered := change arithmetic.typedBody inactive fun node =>
    { node with form := .reference "wrongBuiltinSpelling" (.builtinFunction .wordToInteger) }
  assertTrue (match evaluateStagedWord arithmetic.solvedRequirements tampered arithmeticRoot with
    | .error _ => true | .ok _ => false)
    "malformed inactive callee escaped validation"
  assertTrue (match Staged.word arithmetic.solvedRequirements tampered [] false
    (tampered.nodes.length + 1) arithmeticRoot with | .error _ => true | .ok _ => false)
    "disabled validation ignored malformed callee"
  let duplicate ← functionNamed program "duplicate"
  let duplicateRoot ← returned duplicate
  let (call, callee, left) ← match duplicate.typedBody.nodes.find? fun
      | .expression { form := .call _ _ (.builtinFunction .integerAdd), .. } => true
      | _ => false with
    | some (.expression { id, form := .call callee [left, _] _, .. }) => pure (id, callee, left)
    | _ => throw (IO.userError "missing repeated-operand fixture")
  -- This retained IR mutation is checked by the actual evaluator; it is not
  -- asserted to be fresh parser/checker output.
  let repeated := change duplicate.typedBody call fun node =>
    { node with form := .call callee [left, left] (.builtinFunction .integerAdd) }
  let repeatedResult ← wordResult duplicate.solvedRequirements repeated duplicateRoot
  let requirement ← match repeated.lookupExpression? left with
    | some { form := .integerLiteral _ resolution, .. } => pure resolution.requirement
    | _ => throw (IO.userError "repeated operand is not a numeric literal")
  assertTrue (repeatedResult.value == Core.Word.ofNatModulo 6 &&
    repeatedResult.consumedRequirements == [requirement, requirement])
    "repeated operand consumption was deduplicated or reordered"

end Tests.SourceCoreStagedClosedEvaluationMeaning
