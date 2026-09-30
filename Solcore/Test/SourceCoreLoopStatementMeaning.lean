import Solcore.SourceSemantics.CoreLowering.LoopStatementBridge

/-! Actual compiler acceptance plus independent nested-loop source traces.
The initial store already contains a closure. Source location zero maps to
Core location one; both generated self cells remain administrative. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopStatementMeaning

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open LoopStatements.Default

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"loop_meaning", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : TypedBinder := { id := ⟨owner, 0⟩, name := "flag", scheme := .mono .bool }
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "loop_meaning.solc" }, startByte := 0, endByte := 1 }
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

private theorem guard_contains : ContainsExpression source (exprId 0) guardNode := ⟨by simp [source], rfl⟩
private theorem false_contains : ContainsExpression source (exprId 1) falseNode := ⟨by simp [source], rfl⟩
private theorem outer_contains : ContainsStatement source (stmtId 0) outerNode := ⟨by simp [source], rfl⟩
private theorem inner_contains : ContainsStatement source (stmtId 1) innerNode := ⟨by simp [source], rfl⟩
private theorem assign_contains : ContainsStatement source (stmtId 2) assignNode := ⟨by simp [source], rfl⟩
private theorem continue_contains : ContainsStatement source (stmtId 3) continueNode := ⟨by simp [source], rfl⟩
private theorem source_guard (program : Program) (value : Bool) :
    Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (sourceHeap (some value))
      (exprId 0) (.bool value) (sourceHeap (some value)) :=
  .intro guard_contains (.local rfl .head (.intro .head) rfl rfl) .nil
private theorem source_false (program : Program) :
    Dynamic.ExpressionEvaluates program context [] source sourceEnvironment (sourceHeap (some true))
      (exprId 1) (.bool false) (sourceHeap (some true)) :=
  .intro false_contains (.builtinBoolean rfl) .nil
private theorem source_assignment (program : Program) :
    Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment (sourceHeap (some true)) assignment.target (exprId 1) (.bool false) (sourceHeap (some false)) :=
  .intro (.intro .head (.intro .head) .nil (.intro .head) .initialized .nil)
    (source_false program)
    (.intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head))
private theorem source_body (program : Program) :
    Dynamic.StatementsExecute program context [] source sourceEnvironment (sourceHeap (some true)) [stmtId 1, stmtId 2, stmtId 3]
      context (.continuing sourceEnvironment) (sourceHeap (some false)) :=
  .cons (.whileLoop inner_contains rfl (.done (source_false program)))
    (.cons (.assignValue assign_contains rfl (source_assignment program))
      (.terminal (.continueStmt continue_contains rfl) (.continuing _)))
private theorem source_success (program : Program) :
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (sourceHeap (some true)) [stmtId 0]
      context (.fallthrough sourceEnvironment) (sourceHeap (some false)) :=
  .control (.singleton outer_contains (by intro expression; simp [outerNode])
    (.whileLoop outer_contains rfl
      (.nextContinue (source_guard program true) (source_body program) (.done (source_guard program false)))))
private theorem source_fault (program : Program) :
    Dynamic.FunctionStatementsExecuteOutcome program context [] source sourceEnvironment (sourceHeap none) [stmtId 0]
      context (.fault (.uninitializedLocation ⟨0⟩)) (sourceHeap none) :=
  .fault (.singleton (.whileIteration outer_contains rfl (.condition
    (.form guard_contains (.localUninitialized (owned := []) rfl .head (.intro .head) rfl rfl LocalCell.TypeRepresents.bool.not_mapping)))))

/-- The actual accepted compiler and independently constructed finite nested
source trace imply completion; no child Core execution is provided. -/
example (program : Program) :
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program [] source (fun _ => reason) .unit reason escaped (.fallthrough sourceEnvironment) result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld (sourceHeap (some false)) finalStore ∧
      GeneralHeap.LocationMap.Extends [1] finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved [1] (initialStore (some true)) finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (initialStore (some true))) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (lowerStatements_source_run_preserves aligned unique noFor accepted .unit valid covers
    environments (heaps (some true)) (source_success program)).2

example (program : Program) :
    ∃ result finalStore finalMapping finalWorld required,
      FinishedOutcomeRepresents program [] source (fun _ => reason) .unit reason escaped (.fault (.uninitializedLocation ⟨0⟩)) result ∧
      GeneralHeap.HeapRepresents finalMapping finalWorld (sourceHeap none) finalStore ∧
      GeneralHeap.LocationMap.Extends [1] finalMapping ∧ Core.WorldExtends world finalWorld ∧
      GeneralHeap.AdministrativePreserved [1] (initialStore none) finalMapping finalStore ∧
      (∀ fuel, required ≤ fuel → Core.runStateful fuel (.initial code coreEnvironment (initialStore none)) = .done result finalStore) ∧
      (∀ fuel actual actualStore, Core.runStateful fuel (.initial code coreEnvironment (initialStore none)) = .done actual actualStore →
        actual = result ∧ actualStore = finalStore) :=
  (lowerStatements_source_run_preserves aligned unique noFor accepted .unit valid covers
    environments (heaps none) (source_fault program)).2

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore (some true))) ==
    .done (.inRight .word .unit) [admin, .inRight .unit (.bool false), .inRight .unit outerClosure, .inRight .unit innerClosure])
    "nested loops lost the mutable input or their actual lexical captures"
  assertTrue (Core.runStateful 1000 (.initial code coreEnvironment (initialStore none)) ==
    .done (.inLeft .unit (.word reason)) [admin, .inLeft .bool .unit, .inRight .unit outerClosure])
    "uninitialized guard failed to retain the installed self cell or report its occurrence token"
  match Core.runStateful 0 (.initial code coreEnvironment (initialStore (some true))) with
  | .outOfFuel _ => pure ()
  | _ => throw (IO.userError "zero fuel became a terminal loop result")

end Tests.SourceCoreLoopStatementMeaning
