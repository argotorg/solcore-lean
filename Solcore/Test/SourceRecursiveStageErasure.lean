import Solcore.SourceSemantics.Staging.RecursiveErasure
import Solcore.SourceSemantics.CoreLowering.RecursiveStageProjection

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! A successful nested conditional/product and a non-callable failure retain
the same independent ordinary meaning. The rejected call's missing argument
is never evaluated. These are source judgment fixtures, not assertions of
whole checker/compiler coverage. The final theorem exercises the generalized
public-factory provenance API without assuming a child execution. -/
set_option autoImplicit false
namespace Tests.SourceRecursiveStageErasure
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.Staging Solcore.SourceSemantics.CoreLowering

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"recursive_stage_erasure", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive_stage_erasure.solc"⟩, 0, 1⟩
private def metadata : IndirectCallResolution := {
  argumentCount := 1, argumentTypeBeforeCoercion := .unit,
  argumentTypeAfterCoercion := .unit, argumentCoercions := [] }
private def node (index : Nat) (form : ExpressionForm) : ExpressionNode := { id := id index, span, type := .unit, form }
private def yes : ExpressionNode := node 0 (.reference "true" (.builtinBoolean true))
private def no : ExpressionNode := node 1 (.reference "false" (.builtinBoolean false))
private def grouped : ExpressionNode := node 2 (.group (id 0))
private def pair : ExpressionNode := node 3 (.tuple [id 2, id 1])
private def choice : ExpressionNode := node 4 (.conditional (id 0) (id 3) (id 5))
private def badCall : ExpressionNode := node 5 (.call (id 0) [id 6] (.indirect metadata))
private def source : TypedSource := {
  owner, inputs := [], roots := [.expression (id 4)],
  nodes := [.expression yes, .expression no, .expression grouped, .expression pair, .expression choice, .expression badCall] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def context : SourceSemantics.Context := Context.ofSignatures signatures
private def program : Program := ⟨signatures, [], []⟩
private def scope : Recursive.Scope := {
  origin := ⟨owner, [], []⟩, source, owned := rfl, context, evidence := [],
  guards := {
    stages := ⟨false, .unit, fun _ => some .runtime⟩
    Binds := fun _ _ => False
    userCallable := by intro _ _ impossible; cases impossible
    unique := by intro _ _ _ impossible; cases impossible } }
private def registry : Recursive.Registry := {
  Closure := fun _ _ => False
  source := by intro _ _ impossible; cases impossible
  context := by intro _ _ impossible; cases impossible
  evidence := by intro _ _ impossible; cases impossible }

private theorem yesTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 0) (.value (.bool true)) heap :=
  .atomicValue (node := yes) ⟨by simp [scope, source], rfl⟩ (.reference _ _) rfl (.builtinBoolean rfl)

private theorem noTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 1) (.value (.bool false)) heap :=
  .atomicValue (node := no) ⟨by simp [scope, source], rfl⟩ (.reference _ _) rfl (.builtinBoolean rfl)

private theorem pairTrace (heap : Dynamic.Heap) :
    Recursive.Expression program registry scope context [] heap (id 3) (.value (.product (.bool true) (.bool false))) heap := by
  apply Recursive.Expression.pair (left := id 2) (right := id 1)
  · exact ⟨pair, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩
  · exact .group ⟨grouped, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap)
  · exact noTrace heap

example (heap : Dynamic.Heap) : Dynamic.ExpressionEvaluates program context [] source [] heap (id 4)
    (.product (.bool true) (.bool false)) heap := by
  apply Recursive.Expression.value_plain (registry := registry) (scope := scope)
  exact .conditional ⟨choice, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap) (pairTrace heap)

/-- The absent argument node cannot be silently evaluated ahead of the
non-callable fault; the ordinary projection keeps the post-callee heap. -/
example (heap : Dynamic.Heap) : Dynamic.ExpressionFaults program context [] source [] heap (id 5) .notCallable heap := by
  apply Recursive.Expression.semanticFault_plain (registry := registry) (scope := scope)
  exact .notCallable ⟨badCall, ⟨by simp [scope, source], rfl⟩, rfl, rfl, rfl⟩ (yesTrace heap) (by intro impossible; cases impossible)

example {checkedProgram : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {projectType : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Core.Ty}
    {limits : SourceCoreStageCodebook.Limits} {firstId : Nat} {table : SourceCoreStageCodebook.Table}
    {key : SourceCoreStageCodebook.Key} {lambda : ExpressionId} {active : TypeSystem.Substitution}
    (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram plan projectType limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda key lambda active)) :
    Nonempty (AuthenticatedCallableLedger.LambdaSite plan table key lambda active descriptor.id) :=
  RecursiveStageProjection.lambda_site_of_descriptor accepted descriptor

end Tests.SourceRecursiveStageErasure
