import Solcore.Frontend.SourceCoreLocalCell
import Solcore.Core.BoundedSafety
import Solcore.SourceSemantics.CoreLowering.LocalCell

/-! Local-read lowering coverage: occurrence metadata, first-match source
identity lookup, checked Core execution, and retained exhaustion checkpoints.
The parsed fixture exercises a local read, not a whole-function compiler. -/

set_option autoImplicit false

namespace Tests.SourceCoreLocalCell

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"local_cell", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def otherBinder : Resolved.LocalId := ⟨owner, 1⟩
private def foreignBinder : Resolved.LocalId := ⟨⟨ownerModule, 1⟩, 0⟩
private def expressionId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def missingId : ExpressionId := ⟨⟨owner, 99⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "local_cell.solc" }
  startByte := 0
  endByte := 1
}

private def node (type : TypeSystem.Ty := .word) : ExpressionNode := {
  id := expressionId
  span
  type
  form := .reference "value" (.local binder)
}

private def sourceWith (expression : ExpressionNode) : TypedSource := {
  owner
  inputs := [{ id := binder, name := "value", scheme := .mono expression.type }]
  roots := [.expression expressionId]
  nodes := [.expression expression]
}

private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def literal (value : Nat) : Core.Expr := .word (word value)
private def scalar (value : Nat) : Core.Value := .word (word value)
private def reason : Core.Word := word 71

private def scalarScope : Frontend.SourceCoreLocalCell.Scope :=
  [(otherBinder, .bool), (binder, .word), (binder, .bool)]

private def scalarRead : Core.Expr := Core.OptionalCell.read .word (.var 1) reason

private theorem scalar_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word)) scalarScope expressionId reason =
      .ok scalarRead := by rfl

example : Frontend.SourceCoreLocalCell.lookup? scalarScope binder = some (1, .word) := by rfl
example : Frontend.SourceCoreLocalCell.lookup? scalarScope otherBinder = some (0, .bool) := by rfl
example : Frontend.SourceCoreLocalCell.lookup? scalarScope foreignBinder = none := by rfl
example : (Frontend.SourceCoreLocalCell.coreContext scalarScope)[1]? =
    some (Core.OptionalCell.referenceType .word) :=
  Frontend.SourceCoreLocalCell.lookup?_context (id := binder) (by rfl)

private def scalarProgram (read : Core.Expr := scalarRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body :=
    .letE (Core.OptionalCell.allocateInitialized .bool (.bool true)) <|
    .letE (Core.OptionalCell.allocateInitialized .word (literal 42)) <|
    .letE (Core.OptionalCell.allocateInitialized .bool (.bool false)) read
}

private def scalarStore : Core.Store :=
  [.inRight .unit (.bool true), .inRight .unit (scalar 42), .inRight .unit (.bool false)]

private def productType : Core.Ty := .product .word .bool
private def productScope : Frontend.SourceCoreLocalCell.Scope := [(binder, productType)]
private def productRead : Core.Expr := Core.OptionalCell.read productType (.var 0) reason
private def productValue : Core.Value := .pair (scalar 8) (.bool true)
private def productProgram (read : Core.Expr := productRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType productType
  body := .letE
    (Core.OptionalCell.allocateInitialized productType (.pair (literal 8) (.bool true))) read
}

private theorem product_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node (.product .word .bool)))
      productScope expressionId reason = .ok productRead := by rfl

private def uninitializedRead : Core.Expr := Core.OptionalCell.read .word (.var 0) reason
private def uninitializedProgram (read : Core.Expr := uninitializedRead) : Core.Program := {
  resultType := Core.LanguageResult.resultType .word
  body := .letE (Core.OptionalCell.allocate .word) read
}

private theorem uninitialized_lowered :
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word))
      [(binder, .word)] expressionId reason = .ok uninitializedRead := by rfl

private theorem scalar_checked : (scalarProgram).check = true := by decide
private theorem product_checked : (productProgram).check = true := by decide
private theorem uninitialized_checked : (uninitializedProgram).check = true := by decide

private theorem scalar_completed :
    (scalarProgram).runStateful 80 = .done (.inRight .word (scalar 42)) scalarStore := by rfl
private theorem product_completed :
    (productProgram).runStateful 80 =
      .done (.inRight .word productValue) [.inRight .unit productValue] := by rfl
private theorem uninitialized_completed :
    (uninitializedProgram).runStateful 80 =
      .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by rfl

private theorem scalar_exhausted :
    ∃ checkpoint, (scalarProgram).runStateful 24 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

private theorem uninitialized_exhausted :
    ∃ checkpoint, (uninitializedProgram).runStateful 10 = .outOfFuel checkpoint := by
  exact ⟨_, rfl⟩

example : ∃ checkpoint,
    (scalarProgram).runStateful 24 = .outOfFuel checkpoint ∧
    Core.StateHasType checkpoint (Core.LanguageResult.resultType .word) ∧
    Core.runStateful 56 checkpoint = .done (.inRight .word (scalar 42)) scalarStore := by
  obtain ⟨checkpoint, exhausted⟩ := scalar_exhausted
  have typed := Core.initial_state_has_type (Core.Program.check_full_sound scalar_checked).bodyHasType
  exact ⟨checkpoint, exhausted,
    Core.well_typed_runStateful_preserves_checkpoint_type typed exhausted,
    (Core.runStateful_resume exhausted 56).trans scalar_completed⟩

example : ∃ checkpoint,
    (uninitializedProgram).runStateful 10 = .outOfFuel checkpoint ∧
    Core.StateHasType checkpoint (Core.LanguageResult.resultType .word) ∧
    Core.runStateful 70 checkpoint =
      .done (.inLeft .word (.word reason)) [.inLeft .word .unit] := by
  obtain ⟨checkpoint, exhausted⟩ := uninitialized_exhausted
  have typed := Core.initial_state_has_type
    (Core.Program.check_full_sound uninitialized_checked).bodyHasType
  exact ⟨checkpoint, exhausted,
    Core.well_typed_runStateful_preserves_checkpoint_type typed exhausted,
    (Core.runStateful_resume exhausted 70).trans uninitialized_completed⟩

private def wordReadSite : SourceSemantics.CoreLowering.LocalCell.ReadSite
    (sourceWith (node .word)) [(binder, .word)] expressionId .word := {
  node := node .word
  binder
  name := "value"
  index := 0
  contains := ⟨List.Mem.head _, rfl⟩
  form := rfl
  owner := rfl
  requirements := rfl
  coercions := rfl
  slot := rfl
  types := .word
}

private theorem wordSource_unique :
    SourceSemantics.NodeOccurrencesUnique (sourceWith (node .word)) := by
  simp [SourceSemantics.NodeOccurrencesUnique, SourceSemantics.nodeOccurrenceIds, sourceWith]

/-- A concrete proof consumer includes actual lowering, an independent source
outcome, a finite completion bound, and reflection of every completed run. -/
private def ReadCorrespondence (program : SourceSemantics.Program)
    (context : SourceSemantics.Context) (evidence : SourceSemantics.Dynamic.EvidenceEnvironment)
    (heap : SourceSemantics.Dynamic.Heap) (store : Core.Store) : Prop :=
  Core.RuntimeStoreHasTypes [Core.OptionalCell.cellType .word] store ∧
  ∃ expression sourceOutcome coreValue required,
    Frontend.SourceCoreLocalCell.lowerRead (sourceWith (node .word)) [(binder, .word)]
      expressionId reason = .ok expression ∧
    SourceSemantics.Dynamic.ExpressionEvaluatesOutcome program context evidence
      (sourceWith (node .word)) [(binder, ⟨0⟩)] heap expressionId sourceOutcome heap ∧
    SourceSemantics.CoreLowering.LocalCell.OutcomeRepresents ⟨0⟩ reason sourceOutcome coreValue ∧
    (∀ fuel, required ≤ fuel → Core.runStateful fuel
      (.initial expression [.cellRef (Core.OptionalCell.cellType .word) 0] store) =
        .done coreValue store) ∧
    (∀ fuel result finalStore, Core.runStateful fuel
      (.initial expression [.cellRef (Core.OptionalCell.cellType .word) 0] store) =
        .done result finalStore → result = coreValue ∧ finalStore = store)

private def initializedCell : SourceSemantics.Dynamic.Cell := {
  type := .word
  value := some (.word (word 42))
}

private def absentCell : SourceSemantics.Dynamic.Cell := {
  type := .word
  value := none
}

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : SourceSemantics.Dynamic.EvidenceEnvironment) :
    ReadCorrespondence program context evidence ⟨[initializedCell]⟩
      [.inRight .unit (scalar 42)] := by
  have heaps : SourceSemantics.CoreLowering.LocalCell.HeapRepresents [initializedCell]
      [.inRight .unit (scalar 42)] [Core.OptionalCell.cellType .word] :=
    .cons (.initialized (.word (word 42))) .nil
  exact ⟨heaps.runtime_hasTypes [],
    wordReadSite.lower_run_preserves wordSource_unique program context evidence
      [(binder, ⟨0⟩)] ⟨[initializedCell]⟩ [.cellRef (Core.OptionalCell.cellType .word) 0]
      [.inRight .unit (scalar 42)] [Core.OptionalCell.cellType .word] ⟨0⟩ initializedCell
      heaps .head (.intro .head) rfl rfl reason⟩

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : SourceSemantics.Dynamic.EvidenceEnvironment) :
    ReadCorrespondence program context evidence ⟨[absentCell]⟩ [.inLeft .word .unit] := by
  have heaps : SourceSemantics.CoreLowering.LocalCell.HeapRepresents [absentCell]
      [.inLeft .word .unit] [Core.OptionalCell.cellType .word] :=
    .cons (.uninitialized .word) .nil
  exact ⟨heaps.runtime_hasTypes [],
    wordReadSite.lower_run_preserves wordSource_unique program context evidence
      [(binder, ⟨0⟩)] ⟨[absentCell]⟩ [.cellRef (Core.OptionalCell.cellType .word) 0]
      [.inLeft .word .unit] [Core.OptionalCell.cellType .word] ⟨0⟩ absentCell
      heaps .head (.intro .head) rfl rfl reason⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def lower (source : TypedSource) (scope : Frontend.SourceCoreLocalCell.Scope)
    (id : ExpressionId) : IO Core.Expr := do
  match Frontend.SourceCoreLocalCell.lowerRead source scope id reason with
  | .ok expression => pure expression
  | .error error => throw (IO.userError s!"local read failed to lower: {reprStr error}")

private def expectError (label : String) (source : TypedSource)
    (scope : Frontend.SourceCoreLocalCell.Scope) (id : ExpressionId)
    (accept : Frontend.SourceCoreLocalCell.Error → Bool) : IO Unit := do
  match Frontend.SourceCoreLocalCell.lowerRead source scope id reason with
  | .ok _ => throw (IO.userError s!"{label}: invalid local read lowered")
  | .error error => assertTrue (accept error) s!"{label}: wrong error {reprStr error}"

private def testRejections : IO Unit := do
  let source := sourceWith (node .word)
  expectError "missing occurrence" source scalarScope missingId
    fun error => match error with | .missingExpression id => id == missingId | _ => false
  expectError "non-reference expression" (sourceWith { node .word with form := .literal (.decimal "1") })
    scalarScope expressionId fun error => error matches .expectedLocalReference _
  expectError "nonlocal reference"
    (sourceWith { node .word with form := .reference "true" (.builtinBoolean true) })
    scalarScope expressionId fun error => error matches .expectedLocalReference _
  expectError "foreign owner before missing binding"
    (sourceWith { node .word with form := .reference "value" (.local foreignBinder) })
    [] expressionId fun error => match error with
      | .ownerMismatch id => decide (id = foreignBinder)
      | _ => false
  expectError "missing binding" source [] expressionId fun error => match error with
    | .missingBinding id => decide (id = binder)
    | _ => false
  let coercion : CoercionStep := { requirement := ⟨3⟩, source := .word, target := .word }
  expectError "requirements before coercions and missing binding"
    (sourceWith { node .word with requirements := [⟨3⟩], coercions := [coercion] })
    [] expressionId fun error => error matches .requirementsPresent _
  expectError "coercions before missing binding"
    (sourceWith { node .word with coercions := [coercion] })
    [] expressionId fun error => error matches .coercionsPresent _
  expectError "unsupported projected type" (sourceWith (node (.function .word .word)))
    scalarScope expressionId fun error => match error with
      | .typeProjection failure =>
          failure.site == .occurrence expressionId.occurrence &&
            (failure.reason matches .unsupportedType _)
      | _ => false
  expectError "slot type mismatch" source [(binder, .bool)] expressionId fun error =>
    error matches .slotTypeMismatch .word .bool

private def checkResume (label : String) (program : Core.Program) (spent : Nat)
    (value : Core.Value) (store : Core.Store) : IO Unit := do
  match program.runStateful spent with
  | .outOfFuel checkpoint =>
      assertTrue (Core.runStateful (80 - spent) checkpoint == .done value store)
        s!"{label}: resumption lost the local reference or optional payload"
  | _ => throw (IO.userError s!"{label}: expected a retained checkpoint")

private def testLoweredExecution : IO Unit := do
  let scalarExpr ← lower (sourceWith (node .word)) scalarScope expressionId
  assertTrue (scalarExpr == scalarRead) "source identity lookup lost the first matching slot"
  let scalarCore := scalarProgram scalarExpr
  assertTrue scalarCore.check "lowered scalar read did not pass the Core checker"
  assertTrue (scalarCore.runStateful 80 == .done (.inRight .word (scalar 42)) scalarStore)
    "lowered scalar read chose the wrong slot or changed the store"
  checkResume "scalar read" scalarCore 24 (.inRight .word (scalar 42)) scalarStore
  let productExpr ← lower (sourceWith (node (.product .word .bool))) productScope expressionId
  let product := productProgram productExpr
  assertTrue product.check "lowered product read did not pass the Core checker"
  assertTrue (product.runStateful 80 ==
      .done (.inRight .word productValue) [.inRight .unit productValue])
    "lowered product read lost its structural payload"
  let absentExpr ← lower (sourceWith (node .word)) [(binder, .word)] expressionId
  let absent := uninitializedProgram absentExpr
  assertTrue absent.check "lowered uninitialized read did not pass the Core checker"
  assertTrue (Core.LanguageResult.run absent 80 == .failed reason [.inLeft .word .unit])
    "lowered uninitialized read must return the supplied reason and unchanged marker"
  checkResume "uninitialized read" absent 10 (.inLeft .word (.word reason)) [.inLeft .word .unit]

private def testParsedCheckedLocalRead : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    mainSources := [{ path := "main.solc", content :=
      "function read(value: Word) returns (Word) { return value; }" }]
    externalLibraries := []
  }
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error errors => throw (IO.userError s!"local read fixture failed checking: {reprStr errors}")
  let function ← match program.functions with
    | [function] => pure function
    | _ => throw (IO.userError "local read fixture expected one checked function")
  let occurrence ← match function.typedBody.nodes.find? (fun
      | .expression { form := .reference _ (.local _), .. } => true
      | _ => false) with
    | some (.expression node) => pure node
    | _ => throw (IO.userError "checked local occurrence is missing")
  let localId ← match occurrence.form with
    | .reference _ (.local localId) => pure localId
    | _ => throw (IO.userError "checked occurrence is not a local reference")
  let expression ← lower function.typedBody [(localId, .word)] occurrence.id
  let core : Core.Program := {
    resultType := Core.LanguageResult.resultType .word
    body := .letE (Core.OptionalCell.allocateInitialized .word (literal 17)) expression
  }
  assertTrue core.check "the actual checked occurrence did not lower to checked Core"
  assertTrue (Core.LanguageResult.run core 80 == .succeeded (scalar 17) [.inRight .unit (scalar 17)])
    "the actual checked occurrence lost its local value"

def run : IO Unit := do
  testRejections
  testLoweredExecution
  testParsedCheckedLocalRead

end Tests.SourceCoreLocalCell
