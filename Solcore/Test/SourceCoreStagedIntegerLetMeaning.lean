import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning

/-! Actual Integer-let lowering: the resolved body omits this let, while the
independent source step allocates its exact Integer cell. -/
set_option autoImplicit false
namespace Tests.SourceCoreStagedIntegerLetMeaning
open Solcore Frontend SourceInference TypeSystem SourceCoreElaboration
open SourceCoreElaboration.Internal SourceSemantics SourceSemantics.CoreLowering
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning

abbrev actual_erased_step := @SourceStagedIntegerLetMeaning.let_erased_step

abbrev actual_let := @SourceStagedIntegerLetMeaning.let_of_accepted
abbrev actual_function_head := @SourceStagedIntegerLetMeaning.function_head_source_step
abbrev actual_typed_extension := @SourceStagedIntegerLetMeaning.typed_extension

theorem actual_draft {function : CheckedFunction} {draft : BodyDraft}
    (accepted : lowerFunctionBody function = .ok draft) :
    Staged.IntegerLet.FunctionAccepted function draft := Staged.IntegerLet.function_of_accepted accepted

theorem actual_remainder {function : CheckedFunction} {draft : BodyDraft}
    (accepted : lowerFunctionBody function = .ok draft) :
    ∃ consumed, reconcileConsumedRequirements function.declaration
      (function.solvedRequirements.map (·.id)) consumed = .ok draft.unconsumedRequirements := by
  cases Staged.IntegerLet.function_of_accepted accepted with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
    exact ⟨_, reconciled⟩

theorem prior_cell {before after : Dynamic.Heap} {value : Int}
    {location : Dynamic.Location} {cell : Dynamic.Cell}
    (extended : Extends before after [value]) (original : Dynamic.Heap.Reads before location cell) :
    Dynamic.Heap.Reads after location cell := extended.preserves_read original

/-- An erased source let still allocates; the source heaps cannot be equated. -/
theorem source_grows {before after : Dynamic.Heap} {value : Int}
    (extended : Extends before after [value]) : after ≠ before := by
  have length := extended.length_eq
  simp only [List.length_cons, List.length_nil] at length
  intro same
  subst after
  omega

/-- Empty quantified variables alone do not establish source binder extension. -/
theorem malformed_scheme {source : TypedSource} {context next : SourceSemantics.Context} {binder : TypedBinder}
    (mono : binder.scheme.quantified = []) (nonempty : binder.schemeRequirements ≠ [])
    (extended : BinderExtends source.owner context binder next) : False := by
  cases extended with
  | intro wellFormed fresh => exact nonempty (wellFormed.monomorphic_requirements_empty mono)

/-- A valid draft can retain unused ledger rows; finalization rejects them. -/
theorem nonempty_remainder {draft : BodyDraft} {head : RequirementId} {tail : List RequirementId}
    (remaining : draft.unconsumedRequirements = head :: tail) :
    draft.finalize = .error ⟨.declaration draft.declaration, .unconsumedRequirements (head :: tail)⟩ := by
  unfold BodyDraft.finalize
  rw [remaining]
  rfl

private def require (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def get {α : Type} (message : String) : Except SourceCoreElaboration.Error α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{message}: {reprStr error}")

private def content : String := String.intercalate "\n" [
  "function basic() returns (Word) { let x: integer = 42; let y: integer = integerAdd(x, 8); return wordFromInteger(integerMul(y, 2)); }",
  "function negative() returns (Word) { let x: integer = integerSub(0, 3); return wordFromInteger(x); }",
  "function chosen() returns (Word) { let x: integer = true ? integerAdd(2, 3) : integerMul(6, 7); return wordFromInteger(x); }",
  "function reuse() returns (Word) { let x: integer = 3; return wordFromInteger(integerAdd(x, x)); }",
  "function unused() returns (Word) { let ignored: integer = integerAdd(20, 22); return 7; }",
  "function shadow() returns (Word) { let x: integer = 3; let x: integer = integerAdd(x, 1); return wordFromInteger(x); }",
  "function runtime(value: Word) returns (Word) { let x: integer = 2; return value; }",
  "function helper() returns (integer) { return 3; }",
  "function direct() returns (Word) { let x: integer = helper(); return wordFromInteger(x); }"
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

private def whole (function : CheckedFunction) : IO LoweredExpression := do
  let scope ← get "actual inputs" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let expected ← get "actual result projection" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let statements ← roots function
  let site := match Staged.IntegerLet.lastStatement statements with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  get "actual statement lowerer" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody scope []
    (function.typedBody.nodes.length + 1) expected site .statementListFallthrough statements)

private def inspect (function : CheckedFunction) (expectedInitial : Int) : IO Unit := do
  let statements ← roots function
  let (statement, rest) ← match statements with
    | first :: rest => pure (first, rest) | [] => throw (IO.userError "empty roots")
  let (node, binder, initializer) ← match function.typedBody.lookupStatement? statement with
    | some node => match node.form with
      | .letDecl binder (some initializer) => pure (node, binder, initializer)
      | _ => throw (IO.userError "expected Integer let")
    | none => throw (IO.userError "missing head")
  require (node.type == Ty.unit && binder.scheme.quantified.isEmpty && binder.scheme.body == Ty.integer)
    "actual first let metadata"
  let scope ← get "actual scope" (Staged.IntegerLet.inputScope function.typedBody.inputs)
  let expected ← get "actual return type" (lowerType (.declaration function.declaration) function.inferredBodyType)
  let site := match Staged.IntegerLet.lastStatement statements with
    | some last => ErrorSite.occurrence last.occurrence | none => .declaration function.declaration
  let fuel := function.typedBody.nodes.length
  let initial ← get "actual initializer" (Staged.integer function.solvedRequirements function.typedBody [] true fuel initializer)
  require (initial.value == expectedInitial) "initializer source order/value"
  let environment := [Staged.Statements.bind binder initial.value]
  let body ← get "actual body under Integer head" (Staged.IntegerLet.lower function.solvedRequirements function.typedBody
    scope environment fuel expected site .statementListFallthrough rest)
  let result ← whole function
  let draft ← get "actual public draft" (lowerFunctionBody function)
  require (result.resolved == body.resolved && result.consumedRequirements == initial.consumedRequirements ++ body.consumedRequirements)
    "Integer head erasure or ordered consumption changed"
  require (draft.inputs == scope && draft.resolved == result.resolved && draft.returnType == expected &&
    draft.unconsumedRequirements.isEmpty && result.consumedRequirements == function.solvedRequirements.map (·.id))
    "public receipt lost same actual scope/body/full reconciliation"
  let _ ← get "actual finalization" draft.finalize
  -- The original compiler environment duplicate guards precede all children.
  for (badScope, badEnvironment) in [((binder.id, Core.Ty.word) :: scope, ([] : Staged.Environment)), (scope, environment)] do
    match Staged.IntegerLet.lower function.solvedRequirements function.typedBody badScope badEnvironment
        (fuel + 1) expected site .statementListFallthrough statements with
    | .error {reason := .duplicateLocal actual, ..} => require (actual == binder.id) "duplicate guard identity"
    | _ => throw (IO.userError "duplicate let accepted")

private def reject (function : CheckedFunction) : IO Unit :=
  match lowerFunctionBody function with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed or unsupported let accepted")

/-- Real checker fixtures and explicitly modified retained IR are separate.
IO inspects compiler erasure, not a source/runtime heap equivalence. -/
def run : IO Unit := do
  let program ← match checkProgram {entry := "main.solc", mainSources := [{path := "main.solc", content}], externalLibraries := []} with
    | .ok program => pure program | .error errors => throw (IO.userError s!"Integer let checker: {reprStr errors}")
  for (name, value) in [("basic", 42), ("negative", -3), ("chosen", 5), ("reuse", 3), ("unused", 42), ("shadow", 3), ("runtime", 2)] do
    inspect (← named program name) value
  reject (← named program "direct")
  let basic ← named program "basic"
  let statements ← roots basic
  let first ← match statements.head? with | some first => pure first | none => throw (IO.userError "no head")
  let (node, binder, initializer) ← match basic.typedBody.lookupStatement? first with
    | some node => match node.form with
      | .letDecl binder (some initializer) => pure (node, binder, initializer)
      | _ => throw (IO.userError "missing let")
    | none => throw (IO.userError "missing statement")
  let foreign ← named program "negative"
  for changed in [{node with form := .letDecl {binder with id := {binder.id with owner := foreign.declaration}} (some initializer)},
      {node with type := .word}, {node with form := .letDecl binder none},
      {node with form := .letDecl {binder with scheme := {binder.scheme with quantified := [⟨999⟩]}} (some initializer)}] do
    reject {basic with typedBody := {basic.typedBody with nodes := basic.typedBody.nodes.map fun
      | .statement old => if old.id == first then .statement changed else .statement old
      | other => other}}
  -- Validation also checks the unselected initializer arm.
  let chosen ← named program "chosen"
  let no ← match chosen.typedBody.nodes.filterMap (fun
      | .expression {form := .conditional _ _ no, ..} => some no | _ => none) with
    | [no] => pure no | _ => throw (IO.userError "conditional fixture")
  reject {chosen with typedBody := {chosen.typedBody with nodes := chosen.typedBody.nodes.map fun
    | .expression old => if old.id == no then .expression {old with type := .word} else .expression old
    | other => other}}
  -- Draft acceptance keeps every unused row in order; only finalize rejects.
  let extra ← match basic.solvedRequirements.head? with
    | some row => pure {row with id := ⟨100000⟩} | none => throw (IO.userError "no numeric evidence")
  let augmented := {basic with solvedRequirements := extra :: basic.solvedRequirements ++ [extra]}
  let original ← whole basic
  let retained ← whole augmented
  require (original == retained) "unused prefix/suffix ledger altered private traversal"
  let draft ← get "augmented public draft must remain accepted" (lowerFunctionBody augmented)
  require (draft.resolved == retained.resolved && draft.unconsumedRequirements == [extra.id, extra.id])
    "draft lost full unused ledger order"
  match draft.finalize with
  | .error {reason := .unconsumedRequirements remaining, ..} => require (remaining == [extra.id, extra.id]) "finalize exact remainder"
  | _ => throw (IO.userError "finalize accepted unused evidence")
end Tests.SourceCoreStagedIntegerLetMeaning
