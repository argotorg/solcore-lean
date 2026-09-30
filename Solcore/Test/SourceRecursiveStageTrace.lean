import Solcore.SourceSemantics.CoreLowering.RecursiveStageCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveStageRegistry

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Nested callee/argument rejection and closure-body frame propagation in the
independent recursive profile. Closure-body composition takes an independent
static ClosureFrame certificate; it takes no child or body execution premise.
These tests do not claim full compiler admission of this restricted profile. -/

set_option autoImplicit false
namespace Tests.SourceRecursiveStageTrace
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open Solcore.SourceSemantics.Staging

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_stage_trace", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def statement : StatementId := ⟨⟨owner, 6⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive_stage_trace.solc"⟩, 0, 1⟩
private def parameter (marked : Bool) : TypedBinder := {
  id := ⟨owner, 0⟩, name := "input", scheme := .mono .unit, comptime := marked }
private def metadata (count : Nat) : IndirectCallResolution := {
  argumentCount := count, argumentTypeBeforeCoercion := .unit,
  argumentTypeAfterCoercion := .unit, argumentCoercions := [] }
private def node (index : Nat) (form : ExpressionForm) : ExpressionNode := { id := id index, span, type := .unit, form }
private def targetNode : ExpressionNode := node 0 (.lambda [parameter true] .unit [])
private def argumentNode : ExpressionNode := node 1 (.tuple [])
private def innerNode : ExpressionNode := node 2 (.call (id 0) [id 1] (.indirect (metadata 1)))
private def calleeNode : ExpressionNode := node 3 (.call (id 2) [] (.indirect (metadata 0)))
private def ordinaryNode : ExpressionNode := node 4 (.lambda [parameter false] .unit [])
private def argumentCallNode : ExpressionNode := node 5 (.call (id 4) [id 2] (.indirect (metadata 1)))
private def returnNode : StatementNode := { id := statement, span, type := .unit, form := .returnStmt (some (id 2)) }
private def source : TypedSource := {
  owner, inputs := [], roots := [.statement statement], nodes := [
    .expression targetNode, .expression argumentNode, .expression innerNode,
    .expression calleeNode, .expression ordinaryNode, .expression argumentCallNode, .statement returnNode] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def program : Program := ⟨signatures, [], []⟩
private def plan : SourceSpecializationWorklist.Plan := ⟨[], [], [], []⟩
private def guardFrame (effectful : Bool) : CallBoundary.Frame := {
  stages := ⟨effectful, .unit, fun _ => some .runtime⟩
  Binds := CallableLedger.Binds plan
  userCallable := CallableLedger.Binds.userCallable, unique := CallableLedger.Binds.unique }
private def child : Recursive.Scope := {
  origin := ⟨owner, [], [(⟨7⟩, .word)]⟩, source, owned := rfl, context, evidence := [], guards := guardFrame false }
private def caller : Recursive.Scope := {
  child with origin := ⟨owner, [], [(⟨8⟩, .bool)]⟩, guards := guardFrame true }
private def callable (marked : Bool) : Dynamic.Closure := {
  parameters := [parameter marked], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def wrapper : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [statement], source, captured := [], context, evidence := [] }
private def registry : Recursive.Registry := {
  Closure := fun function scope => function = wrapper ∧ scope = child
  source := by rintro _ _ ⟨rfl, rfl⟩; rfl
  context := by rintro _ _ ⟨rfl, rfl⟩; rfl
  evidence := by rintro _ _ ⟨rfl, rfl⟩; rfl }
private def failure : Recursive.Failure := .stage child (id 2) (.argumentStage 0 (id 1) .runtime)

private theorem targetValue (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 0) (.value (.closure (callable true))) heap := by
  apply Recursive.Expression.atomicValue (node := targetNode)
  · exact ⟨by simp [child, source], rfl⟩
  · exact .lambda _ _ _
  · rfl
  · exact .lambda rfl

private theorem ordinaryValue (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 4) (.value (.closure (callable false))) heap := by
  apply Recursive.Expression.atomicValue (node := ordinaryNode)
  · exact ⟨by simp [child, source], rfl⟩
  · exact .lambda _ _ _
  · rfl
  · exact .lambda rfl

private theorem bound (marked : Bool) : child.guards.Binds (.closure (callable marked)) ⟨[parameter marked], false⟩ := by
  apply CallableLedger.Binds.closure rfl
  constructor
  · intro impossible; cases impossible
  · intro impossible; cases impossible

private theorem ordinary : ¬ CallGuard.Effectful child.guards.stages := by
  rintro (marked | only)
  · cases marked
  · cases only

private theorem rejected : CallBoundary.GuardRejects child.guards (id 2) [id 1] (.closure (callable true))
    (.argumentStage 0 (id 1) .runtime) :=
  .contract (bound true) (.arguments ordinary (.head (.wrongStage (.inr (.inl rfl)) rfl (by decide))))

private theorem innerFault (heap : Dynamic.Heap) :
    Recursive.Expression program registry child context [] heap (id 2) (.fault failure) heap := by
  apply Recursive.Expression.rejected (callee := id 0) (arguments := [id 1]) (metadata := metadata 1)
  · exact ⟨innerNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact targetValue heap
  · exact rejected

/-- A failure while computing a callee retains the inner call's coordinates. -/
example (heap : Dynamic.Heap) : Recursive.Expression program registry child context [] heap (id 3) (.fault failure) heap := by
  apply Recursive.Expression.calleeFault (callee := id 2) (arguments := []) (metadata := metadata 0)
  · exact ⟨calleeNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact innerFault heap

private theorem accepted : CallBoundary.GuardAccepts child.guards (id 5) [id 2] (.closure (callable false)) := by
  apply CallBoundary.GuardAccepts.contract (bound false)
  apply CallGuard.Accepts.ordinary ordinary
  · apply CallGuard.ArgumentsAccept.cons
    · apply CallGuard.ArgumentAccepts.ordinary
      rintro (forced | marked | only)
      · cases forced
      · cases marked
      · cases only
    · exact .nil _
  · exact .ordinary rfl

/-- An accepted outer guard does not bypass a nested argument's guard. -/
example (heap : Dynamic.Heap) : Recursive.Expression program registry child context [] heap (id 5) (.fault failure) heap := by
  apply Recursive.Expression.argumentsFault (callee := id 4) (arguments := [id 2]) (metadata := metadata 1)
  · exact ⟨argumentCallNode, ⟨by simp [child, source], rfl⟩, rfl, rfl, rfl⟩
  · exact ordinaryValue heap
  · exact accepted
  · exact .headFault (innerFault heap)

/-- Even an effectful caller enters the closure's retained ordinary frame.
The inner stage fault is built here from atomic rules, not assumed as a body
execution. The independent closure-validity certificate remains explicit. -/
example (heap : Dynamic.Heap) (valid : Dynamic.ClosureFrame program wrapper) :
    Recursive.Applies program registry caller context heap (.closure wrapper) [] (.fault failure) heap := by
  apply Recursive.Applies.closure (child := child) (outcome := .fault failure)
  · exact ⟨rfl, rfl⟩
  · exact valid
  · exact .nil _
  · exact .nil [] heap
  · apply Recursive.Statements.returnFault (node := returnNode) (expression := id 2)
    · exact ⟨by simp [child, source], rfl⟩
    · rfl
    · exact innerFault heap
  · exact .fault

example : child.origin.localSubstitution ≠ caller.origin.localSubstitution := by decide
example : child.guards.stages.callerReturnComptime = false ∧ caller.guards.stages.callerReturnComptime = true := ⟨rfl, rfl⟩

/-- Every propagated rejection is backed by its source guard and occurrence. -/
example (heap : Dynamic.Heap) : Recursive.Generated child (id 2) (.argumentStage 0 (id 1) .runtime) :=
  (innerFault heap).stage_origin rfl

/-- Production scope construction retains the actual sidecar's return marker
and full contextual substitution, even when those are erased by Core types. -/
example (sidecar : SourceCoreStageContracts.Sidecar) (active : TypeSystem.Substitution) (function : Dynamic.Closure) :
    (RecursiveStageRegistry.scope sidecar active function).guards.stages.callerReturnComptime =
      sidecar.caller.function.returnComptime ∧
    (RecursiveStageRegistry.scope sidecar active function).origin.localSubstitution = active := ⟨rfl, rfl⟩

end Tests.SourceRecursiveStageTrace
