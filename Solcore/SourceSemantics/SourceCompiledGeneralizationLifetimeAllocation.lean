import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceBodyRetainedTemplatePrivacy

/-! When an initializer contains an earlier generalization, the real outer
allocation must preserve its privacy as well. The completed compilation
supplies the outer binder's template predicate scope, including methods. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

namespace GeneralizationLifetime
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {fuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized fuel}
    {binder : TypedBinder} {initializer : ExpressionId}
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializer}
    {entryNext : Nat} {outputs : List Ty}

theorem finishStatementReceipt
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (outer : LocalLetRequirementTiming.Receipt childFuel context source initial result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (lifetime : GeneralizationLifetime event entryNext outer.ready outputs)
    (valuePresent : outer.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext result.state (outputs ++ [result.type]) ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.binding.1.scheme.quantified := by
  have bodySafe := lifetime.values _ valuePresent
  have added := SourceBodyRetainedTemplatePrivacy.cached_statement_receipt artifact checked position
    outer ready extension retained binder event.binderRetained bodySafe
  have unchanged : SafeTransport binder.scheme.quantified outer.ready result.state :=
    .of_substitution_eq (congrArg InferState.substitution outer.inference_eq)
  have live : LiveBindersSafe binder.scheme.quantified result.state := by
    intro liveBinder present
    rw [outer.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (lifetime.live liveBinder ?_) unchanged
      rw [outer.ready_binders]
      exact old
  have resultType : result.type = .unit :=
    congrArg Detail.StatementResult.type outer.completed
  have requirements : result.state.requirements = outer.ready.requirements :=
    congrArg (fun output : Detail.StatementResult => output.state.requirements) outer.completed
  refine ⟨lifetime.append ?_ unchanged live ?_ ?_, ?_⟩
  · rw [outer.inference_eq]
    exact Nat.le_refl _
  · intro type present
    cases List.mem_singleton.mp present
    rw [resultType]
    exact safe_closed _ _ (by simp [Ty.VariablesBelow, Ty.freeVariables, Ty.unit])
  · intro requirement present fresh
    exact False.elim (fresh (requirements ▸ present))
  · intro q innerQuantified outerQuantified
    exact bodySafe q (List.mem_filter.mp outerQuantified).1 innerQuantified

theorem finishStatement
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {source : Syntax.Statement}
    (outer : BodyInitializerOccurrence selected source)
    (lifetime : GeneralizationLifetime event entryNext outer.receipt.ready outputs)
    (valuePresent : outer.receipt.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext outer.result.state (outputs ++ [outer.result.type]) ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.receipt.binding.1.scheme.quantified :=
  finishStatementReceipt artifact checked position outer.receipt outer.ready
    outer.extension outer.retained lifetime valuePresent

theorem finishHeader
    (artifact : compiled.artifact? = some cached)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {initial : State} {result : ForItemForm × State}
    (outer : SourceInference.LocalHeaderRequirementTiming.Receipt childFuel context source initial result)
    (ready : outer.ready.InferenceReady)
    (extension : selected.body.finalized.substitution.SemanticallyExtends outer.ready.inference.substitution)
    (retained : outer.binding.1 ∈ (evidenceSource selected).initializedLetBinders)
    (lifetime : GeneralizationLifetime event entryNext outer.ready outputs)
    (valuePresent : outer.value.type ∈ outputs) :
    GeneralizationLifetime event entryNext result.2 outputs ∧
      ∀ q ∈ binder.scheme.quantified, q ∉ outer.binding.1.scheme.quantified := by
  have bodySafe := lifetime.values _ valuePresent
  have added := SourceBodyRetainedTemplatePrivacy.cached_header artifact checked position
    outer ready extension retained binder event.binderRetained bodySafe
  have unchanged : SafeTransport binder.scheme.quantified outer.ready result.2 :=
    .of_substitution_eq (congrArg InferState.substitution outer.inference_eq)
  have live : LiveBindersSafe binder.scheme.quantified result.2 := by
    intro liveBinder present
    rw [outer.result_binders] at present
    rcases List.mem_cons.mp present with rfl | old
    · exact added
    · apply BinderSafe.transport (lifetime.live liveBinder ?_) unchanged
      rw [outer.ready_binders]
      exact old
  have requirements : result.2.requirements = outer.ready.requirements :=
    congrArg (fun output : ForItemForm × State => output.2.requirements) outer.completed
  constructor
  · have finished := lifetime.append (newOutputs := []) ?_ unchanged live (by simp) ?_
    · simpa only [List.append_nil] using finished
    · rw [outer.inference_eq]
      exact Nat.le_refl _
    · intro requirement present fresh
      exact False.elim (fresh (requirements ▸ present))
  · intro q innerQuantified outerQuantified
    exact bodySafe q (List.mem_filter.mp outerQuantified).1 innerQuantified

end GeneralizationLifetime
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
