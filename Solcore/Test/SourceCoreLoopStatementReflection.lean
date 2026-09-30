import Solcore.SourceSemantics.CoreLowering.LoopStatementReflectionBridge

/-! Core-only completion witnesses reconstruct independent nested-loop source traces.
The initial store already contains a closure. Source location zero maps to
Core location one; both generated self cells remain administrative. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementReflection

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_reflection.solc" }, startByte := 0, endByte := 1 }
private def reason : Core.Word := Core.Word.ofNatModulo 43
private def escaped : Core.Word := Core.Word.ofNatModulo 44
private def compilation : SourceCorePrimitive.Context := { solvedRequirements := [] }
private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def context : SourceSemantics.Context :=
  (Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def scope : SourceCoreLocalCell.Scope := [(binder.id, .bool)]
private def assignment : AssignmentResolution := { target := { root := binder.id, projections := [], type := .bool } }
private def guardNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "flag" (.local binder.id) }
private def falseNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def outerNode : StatementNode := { id := stmtId 0, span, type := .unit, form := .whileLoop (exprId 0) [stmtId 1, stmtId 2, stmtId 3] }
private def innerNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .whileLoop (exprId 1) [] }
private def assignNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .assignValue assignment .equal (exprId 1) }
private def continueNode : StatementNode := { id := stmtId 3, span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner, inputs := [binder], roots := [.statement (stmtId 0)]
  nodes := [.expression guardNode, .expression falseNode, .statement outerNode,
    .statement innerNode, .statement assignNode, .statement continueNode] }
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def sourceHeap (value : Option Bool) : Dynamic.Heap := ⟨[{ type := .bool, value := value.map Dynamic.Value.bool }]⟩
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .bool) 1]
private def adminType : Core.Ty := .sum .unit (.function .unit .unit)
private def admin : Core.Value := .inRight .unit (.closure .unit .unit .unit [])
private def corePayload : Option Bool → Core.Value
  | none => .inLeft .bool .unit
  | some value => .inRight .unit (.bool value)
private def initialStore (value : Option Bool) : Core.Store := [admin, corePayload value]
private def world : Core.StoreTyping := [adminType, Core.OptionalCell.cellType .bool]
private def conditionCode : Core.Expr := Core.OptionalCell.read .bool (.var 0) reason
private def innerCode : Core.Expr := Core.LocalLoop.whileLoop .unit (Core.LanguageResult.success (.bool false))
  (Core.LocalLoop.fallthrough .unit) escaped
private def bodyCode : Core.Expr := Core.LocalLoop.sequence .unit innerCode
  (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0)
    (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit))
private def flow : Core.Expr := Core.LocalLoop.sequence .unit
  (Core.LocalLoop.whileLoop .unit conditionCode bodyCode escaped) (Core.LocalLoop.fallthrough .unit)
private def code : Core.Expr := Core.LocalControl.finish .unit (Core.LocalLoop.toControl .unit flow escaped)
  (Core.LanguageResult.success .unit)
private def outerClosure : Core.Value := Core.LocalLoop.installedClosure .unit conditionCode bodyCode
  (Core.LocalLoop.fallthrough .unit) escaped 2 coreEnvironment
private def innerClosure : Core.Value := Core.LocalLoop.installedClosure .unit
  (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.fallthrough .unit) (Core.LocalLoop.fallthrough .unit) escaped 3
  [.bool true, .unit, .cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 2,
    .cellRef (Core.OptionalCell.cellType .bool) 1]

private theorem aligned : BasicStatements.ScopeContextAligned scope context :=
  (BasicStatements.ScopeContextAligned.empty signatures).bind binder .bool
private theorem unique : NodeOccurrencesUnique source := by
  unfold NodeOccurrencesUnique nodeOccurrenceIds
  decide
private theorem noFor : NoForLoops source := by
  intro id node found initializer condition post body
  have member := (lookupStatement?_sound found).1
  simp [source] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals simp [outerNode, innerNode, assignNode, continueNode]
private theorem accepted : SourceCoreLoops.lowerStatementsWithReasons 10 compilation source scope [stmtId 0]
    .unit (fun _ => reason) reason escaped = .ok code := by rfl
private theorem valid : PrimitiveExpressions.ContextValid compilation context := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [RequirementIdsUnique, context, Context.withLocal, Context.ofSignatures]
  · intro requirement impossible
    simp [context, Context.withLocal, Context.ofSignatures] at impossible
private theorem covers : Dynamic.EvidenceEnvironment.Covers context [] := by
  constructor
  · intro goal evidence found; cases found
  · intro predicate member
    simp [context, Context.withLocal, Context.ofSignatures] at member
private theorem heaps (value : Option Bool) : GeneralHeap.HeapRepresents [1] world (sourceHeap value) (initialStore value) := by
  have adminTyped : Core.RuntimeValueHasType [] admin adminType := .inRight (.closure .nil .unit)
  have base := GeneralHeap.HeapRepresents.empty.allocate_administrative adminTyped
  cases value with
  | none =>
    exact (base.allocate (LocalCell.CellRepresents.uninitialized LocalCell.TypeRepresents.bool) Dynamic.Heap.Allocates.append).1
  | some value =>
    exact (base.allocate (LocalCell.CellRepresents.initialized (.bool value)) Dynamic.Heap.Allocates.append).1
private theorem environments : GeneralHeap.EnvRepresents [1] world [] scope sourceEnvironment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil .nil)


private def successStore : Core.Store :=
  [admin, .inRight .unit (.bool false), .inRight .unit outerClosure, .inRight .unit innerClosure]
private def failureStore : Core.Store := [admin, .inLeft .bool .unit, .inRight .unit outerClosure]


private def installedStore (value : Option Bool) : Core.Store :=
  [admin, corePayload value, .inRight .unit outerClosure]
private def bodyEnvironment : Core.Environment :=
  [.bool true, .unit, .cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 2,
    .cellRef (Core.OptionalCell.cellType .bool) 1]

private theorem core_inner : Core.Evaluates bodyEnvironment (installedStore (some true)) innerCode
    (Core.LocalLoop.fallthroughValue .unit)
    (installedStore (some true) ++ [.inRight .unit innerClosure]) := by
  apply Core.LoopExecution.WhileTrace.whileLoop_evaluates
  apply Core.LoopExecution.WhileTrace.done
  simp only [Core.LoopExecution.conditionCode, Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight .bool

private theorem core_body : Core.Evaluates bodyEnvironment (installedStore (some true))
    (Core.LoopExecution.bodyCode bodyCode) (Core.LocalLoop.continuingValue .unit) successStore := by
  have shifted : Core.LoopExecution.bodyCode bodyCode = Core.LocalLoop.sequence .unit innerCode
      (Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 3)
        (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit)) := by
    simp [Core.LoopExecution.bodyCode, bodyCode, innerCode, ← Core.Expr.rename_insertion,
      Core.LoopRenaming.sequence, Core.LoopRenaming.assign, Core.LoopRenaming.whileLoop,
      Core.LocalLoop.fallthrough, Core.LocalLoop.continuing, Core.LanguageResult.success,
      Core.Expr.rename, Core.Renaming.insertion]
  rw [shifted]
  apply Core.LocalLoop.sequence_fallthrough _ core_inner
  simp [Core.LocalSequence.assign, Core.LanguageResult.bind, Core.Expr.weakenAt,
    Core.LocalLoop.continuing, Core.LanguageResult.success]
  apply Core.Evaluates.letE (boundValue := .cellRef (Core.OptionalCell.cellType .bool) 1) (.var rfl)
  apply Core.Evaluates.caseRight (payload := .bool false) (.inRight .bool)
  apply Core.Evaluates.letE (boundValue := .unit)
  · exact .storeCell (.var rfl) rfl (.inRight (.var rfl)) rfl
  · exact .inRight (.inRight (.inRight .unit))

private theorem core_success : Core.Evaluates coreEnvironment (initialStore (some true)) code
    (.inRight .word .unit) successStore := by
  have trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode escaped 2 coreEnvironment
      (installedStore (some true)) (Core.LocalLoop.fallthroughValue .unit) successStore := by
    apply Core.LoopExecution.WhileTrace.nextContinue (middle := installedStore (some true))
      (nextStore := successStore) (bodyEvaluation := core_body) (installed := rfl)
    · simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
        Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
        (Core.OptionalCell.read_success (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
          (reference := .var 2) (referenceStore := installedStore (some true)) reason (.var rfl) rfl)
    · apply Core.LoopExecution.WhileTrace.done
      simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
        Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
        (Core.OptionalCell.read_success (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
          (reference := .var 2) (referenceStore := successStore) reason (.var rfl) rfl)
  have flowEval : Core.Evaluates coreEnvironment (initialStore (some true)) flow
      (Core.LocalLoop.fallthroughValue .unit) successStore := by
    apply Core.LocalLoop.sequence_fallthrough .unit trace.whileLoop_evaluates
    simp only [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight (.inLeft (.inLeft .unit))
  apply Core.LocalControl.finish_fallthrough .unit (Core.LocalLoop.toControl_normal .unit escaped flowEval)
  simp only [Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight .unit

private theorem core_failure : Core.Evaluates coreEnvironment (initialStore none) code
    (.inLeft .unit (.word reason)) failureStore := by
  have trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode escaped 2 coreEnvironment
      failureStore (.inLeft (Core.LocalLoop.controlType .unit) (.word reason)) failureStore := by
    apply Core.LoopExecution.WhileTrace.conditionFault
    simpa [Core.LoopExecution.conditionCode, conditionCode, Core.OptionalCell.read,
      Core.LanguageResult.failure, Core.LanguageResult.success, Core.Expr.weakenAt, coreEnvironment] using
      (Core.OptionalCell.read_failure (environment := Core.LoopExecution.entryEnvironment .unit 2 coreEnvironment)
        (reference := .var 2) (referenceStore := failureStore) reason (.var rfl) rfl)
  exact Core.LocalControl.finish_failure .unit
    (Core.LocalLoop.toControl_failure .unit escaped
      (Core.LocalLoop.sequence_failure .unit trace.whileLoop_evaluates))

/-- Finite Core derivations alone construct the independent source traces.
The expected Core stores retain both exact nested-loop lexical captures. -/
example (program : Program) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason escaped
      sourceEnvironment (sourceHeap (some true)) [stmtId 0] .unit [1] world (initialStore (some true))
      (.inRight .word .unit) successStore := by
  obtain ⟨fuel, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel core_success
  exact lowerStatements_run_reflects aligned unique noFor accepted .unit valid environments (heaps (some true))
    (completes fuel (Nat.le_refl _))

example (program : Program) :
    LoopStatements.Reflection.FinishedResult program context [] source (fun _ => reason) reason escaped
      sourceEnvironment (sourceHeap none) [stmtId 0] .unit [1] world (initialStore none)
      (.inLeft .unit (.word reason)) failureStore := by
  obtain ⟨fuel, completes⟩ := Core.evaluation_runStateful_complete_with_sufficient_fuel core_failure
  exact lowerStatements_run_reflects aligned unique noFor accepted .unit valid environments (heaps none)
    (completes fuel (Nat.le_refl _))

example (program : Program) :
    (∃ fuel value after, Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done value after) ↔
    (∃ finalContext outcome after, Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment
      (sourceHeap (some true)) [stmtId 0] finalContext outcome after) :=
  lowerStatements_finite_iff aligned unique noFor accepted .unit valid covers environments (heaps (some true))

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore (some true))) ==
    .done (.inRight .word .unit) successStore) "reflected nested loop completion changed"
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore none)) ==
    .done (.inLeft .unit (.word reason)) failureStore) "reflected loop fault completion changed"
  match Core.runStateful 0 (.initial code coreEnvironment (initialStore (some true))) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "reflection treated fuel exhaustion as completion")

end Tests.SourceCoreLoopStatementReflection
