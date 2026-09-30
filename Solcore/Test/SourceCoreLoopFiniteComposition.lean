import Solcore.SourceSemantics.CoreLowering.LoopFiniteComposition
import Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.HeapEffectsRenaming
import Solcore.Frontend.SourceCoreLoops

/-! A finite independent while trace changes its captured Boolean cell, takes
continue, rechecks the guard, and exits. The concrete compiled Core installs a
self cell and preserves its exact closure across that source write. -/

set_option autoImplicit false

namespace Tests.SourceCoreLoopFiniteComposition

open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"finite_loop", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def binder : Resolved.LocalId := ⟨owner, 0⟩
private def exprId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def stmtId (index : Nat) : StatementId := ⟨⟨owner, index + 10⟩⟩
private def span : Syntax.SourceSpan := {
  source := { origin := .main, path := "finite_loop.solc" }, startByte := 0, endByte := 1
}
private def readReason : Core.Word := Core.Word.ofNatModulo 11
private def selfReason : Core.Word := Core.Word.ofNatModulo 12
private def assignment : AssignmentResolution := { target := { root := binder, projections := [], type := .bool } }
private def guardNode : ExpressionNode := { id := exprId 0, span, type := .bool, form := .reference "flag" (.local binder) }
private def falseNode : ExpressionNode := { id := exprId 1, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def assignNode : StatementNode := { id := stmtId 1, span, type := .unit, form := .assignValue assignment .equal (exprId 1) }
private def continueNode : StatementNode := { id := stmtId 2, span, type := .unit, form := .continueStmt }
private def source : TypedSource := {
  owner, inputs := [{ id := binder, name := "flag", scheme := .mono .bool }]
  roots := [.statement (stmtId 0)]
  nodes := [.expression guardNode, .expression falseNode,
    .statement { id := stmtId 0, span, type := .unit, form := .whileLoop (exprId 0) [stmtId 1, stmtId 2] },
    .statement assignNode, .statement continueNode]
}
private def scope : SourceCoreBasic.Scope := [(binder, .bool)]
private def sourceEnvironment : Dynamic.Environment := [(binder, ⟨0⟩)]
private def sourceHeap (value : Bool) : Dynamic.Heap := ⟨[{ type := .bool, value := some (.bool value) }]⟩
private def coreEnvironment : Core.Environment := [.cellRef (Core.OptionalCell.cellType .bool) 0]
private def conditionCode : Core.Expr := Core.OptionalCell.read .bool (.var 0) readReason
private def bodyCode : Core.Expr := Core.LocalSequence.assign (Core.LocalLoop.controlType .unit) (.var 0)
  (Core.LanguageResult.success (.bool false)) (Core.LocalLoop.continuing .unit)
private def whileCode : Core.Expr := Core.LocalLoop.whileLoop .unit conditionCode bodyCode selfReason
private def code : Core.Expr := Core.LocalLoop.sequence .unit whileCode (Core.LocalLoop.fallthrough .unit)
private def initialStore : Core.Store := [.inRight .unit (.bool true)]
private def selfClosure : Core.Value := Core.LocalLoop.installedClosure .unit conditionCode bodyCode
  (Core.LocalLoop.fallthrough .unit) selfReason 1 coreEnvironment
private def loopStore (value : Bool) : Core.Store := [.inRight .unit (.bool value), .inRight .unit selfClosure]

private theorem accepted : SourceCoreLoops.lowerFlowStatementsWithExpression
    (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel { solvedRequirements := [] } source scope id reasons)
    5 source scope [stmtId 0] .unit (fun _ => readReason) false selfReason = .ok code := by rfl

private theorem guard_contains : ContainsExpression source (exprId 0) guardNode := ⟨by simp [source], rfl⟩
private theorem false_contains : ContainsExpression source (exprId 1) falseNode := ⟨by simp [source], rfl⟩
private theorem assign_contains : ContainsStatement source (stmtId 1) assignNode := ⟨by simp [source], rfl⟩
private theorem continue_contains : ContainsStatement source (stmtId 2) continueNode := ⟨by simp [source], rfl⟩

private theorem source_guard (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (value : Bool) :
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment (sourceHeap value) (exprId 0) (.bool value) (sourceHeap value) :=
  .intro guard_contains (.local rfl .head (.intro .head) rfl rfl) .nil

private theorem source_false (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment (sourceHeap true) (exprId 1) (.bool false) (sourceHeap true) :=
  .intro false_contains (.builtinBoolean rfl) .nil

private theorem source_assignment (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment (sourceHeap true) assignment.target (exprId 1) (.bool false) (sourceHeap false) :=
  .intro (.intro .head (.intro .head) .nil (.intro .head) .initialized .nil)
    (source_false program context evidence)
    (.intro (.intro .head) rfl .initialized (.leaf (.equal _ _)) (.intro (.intro .head) .head))

private theorem source_body (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.StatementsExecute program context evidence source sourceEnvironment (sourceHeap true) [stmtId 1, stmtId 2]
      context (.continuing sourceEnvironment) (sourceHeap false) :=
  .cons (.assignValue assign_contains rfl (source_assignment program context evidence))
    (.terminal (.continueStmt continue_contains rfl) (.continuing _))

/-- The finite source derivation itself supplies the two guard observations. -/
private theorem source_while (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    Dynamic.WhileExecutes program context evidence source sourceEnvironment (sourceHeap true) (exprId 0) [stmtId 1, stmtId 2]
      context (.fallthrough sourceEnvironment) (sourceHeap false) :=
  .nextContinue (source_guard program context evidence true) (source_body program context evidence)
    (.done (source_guard program context evidence false))

private theorem body_restricted : Core.HeapEffects.Expression bodyCode := by
  have rhs : Core.HeapEffects.Expression (Core.LanguageResult.success (.bool false)) := .inRight .bool
  have next : Core.HeapEffects.Expression (Core.LocalLoop.continuing .unit) := .inRight (.inRight (.inRight .unit))
  exact .letE .var (.caseE (rhs.weakenAt 0) (.inLeft .var)
    (.letE (.storeCell .var (.inRight .var)) (((next.weakenAt 0).weakenAt 0).weakenAt 0)))

private theorem condition_evaluates (value : Bool) :
    Core.Evaluates coreEnvironment (loopStore value) conditionCode (.inRight .word (.bool value)) (loopStore value) :=
  Core.OptionalCell.read_success readReason (.var rfl) rfl

private theorem body_evaluates : Core.Evaluates coreEnvironment (loopStore true) bodyCode
    (Core.LocalLoop.continuingValue .unit) (loopStore false) := by
  refine Core.LocalSequence.assign_success (referenceStore := loopStore true) (rhsStore := loopStore true)
    (writtenStore := loopStore false) (oldValue := .inRight .unit (.bool true)) (value := .bool false)
    _ (.var rfl) ?_ rfl rfl ?_
  · simp [Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight .bool
  · simp [Core.LocalLoop.continuing, Core.LanguageResult.success, Core.Expr.weakenAt]
    exact .inRight (.inRight (.inRight .unit))

private theorem core_trace : Core.LoopExecution.WhileTrace .unit conditionCode bodyCode selfReason 1 coreEnvironment
    (loopStore true) (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := by
  have conditionRestricted : Core.ReadOnly.Expression conditionCode := .caseE (.loadCell .var) (.inLeft .word) (.inRight .var)
  have conditionTrue := (conditionRestricted.weakenAt 0).evaluation_weakenAt_zero
    (conditionRestricted.evaluation_weakenAt_zero (condition_evaluates true)
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit
  have conditionFalse := (conditionRestricted.weakenAt 0).evaluation_weakenAt_zero
    (conditionRestricted.evaluation_weakenAt_zero (condition_evaluates false)
      (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit
  have shiftedBody := ((body_restricted.weakenAt 0).weakenAt 0).evaluation_weakenAt_zero
    ((body_restricted.weakenAt 0).evaluation_weakenAt_zero
      (body_restricted.evaluation_weakenAt_zero body_evaluates
        (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType .unit)) 1)) .unit) (.bool true)
  exact .nextContinue conditionTrue shiftedBody rfl (.done conditionFalse)

private theorem core_while : Core.Evaluates coreEnvironment initialStore whileCode
    (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := core_trace.whileLoop_evaluates

private theorem core_flow : Core.Evaluates coreEnvironment initialStore code
    (Core.LocalLoop.fallthroughValue .unit) (loopStore false) := by
  apply Core.LocalLoop.sequence_fallthrough _ core_while
  simp [Core.LocalLoop.fallthrough, Core.LanguageResult.success, Core.Expr.weakenAt]
  exact .inRight (.inLeft (.inLeft .unit))

/-- Actual accepted code, an independent finite source loop, and a finite Core
execution agree on the source cell and retain the installed self closure. -/
example (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) :
    SourceCoreLoops.lowerFlowStatementsWithExpression
      (fun fuel source scope id reasons => SourceCorePrimitive.lowerExpressionWithReasons fuel { solvedRequirements := [] } source scope id reasons)
      5 source scope [stmtId 0] .unit (fun _ => readReason) false selfReason = .ok code ∧
    Dynamic.WhileExecutes program context evidence source sourceEnvironment (sourceHeap true) (exprId 0) [stmtId 1, stmtId 2]
      context (.fallthrough sourceEnvironment) (sourceHeap false) ∧
    Core.Evaluates coreEnvironment initialStore code (Core.LocalLoop.fallthroughValue .unit) (loopStore false) :=
  ⟨accepted, source_while program context evidence, core_flow⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  assertTrue (Core.runStateful 400 (.initial code coreEnvironment initialStore) ==
    .done (Core.LocalLoop.fallthroughValue .unit) (loopStore false))
    "continue did not update its captured cell, recheck the guard, or retain the self closure"

end Tests.SourceCoreLoopFiniteComposition
