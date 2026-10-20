import Solcore.SourceSemantics.SourceCompiledStatementPrivacyContinuation
import Solcore.SourceSemantics.SourceCompiledTopLevelInitializerContinuation
import Solcore.SourceSemantics.SourceInferenceGeneralizedPrivacyBoundary

/-! An original initialized declaration supplies its actual generalization
receipt, allocator bounds, retained binder and final substitution. The genuine
older-template provenance closes its declaration-boundary privacy condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables

namespace InitializerContinuation
variable {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : Selected compiled row fuel} {source : Syntax.Statement}

theorem retained_binding (continuation : InitializerContinuation selected source) :
    continuation.receipt.binding.1 ∈
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)).initializedLetBinders := by
  unfold TypedSource.initializedLetBinders
  exact List.mem_flatMap.mpr ⟨_,continuation.original_retained,List.mem_singleton_self _⟩

/-- The new quantified variables are actual free variables of the initializer's
resolved output, and therefore lie below its real returned allocator. -/
theorem quantified_below (continuation : InitializerContinuation selected source)
    (valueBelow : continuation.receipt.value.type.VariablesBelow continuation.receipt.ready.inference.next) :
    ∀ q ∈ continuation.receipt.binding.1.scheme.quantified,
      q.index < continuation.result.state.inference.next := by
  intro q member
  have resolvedBelow := continuation.ready.solved.variablesBelow_apply valueBelow
  have occurs : q ∈ (continuation.receipt.ready.resolve continuation.receipt.value.type).freeVariables := by
    exact (List.mem_filter.mp member).1
  have bound := resolvedBelow q occurs
  rwa [continuation.receipt.inference_eq]

/-- Actual finalizer capture checks close the new and older live binder privacy
conditions; no live-privacy or quantifier-disjointness premise is supplied. -/
theorem generalized_live (continuation : InitializerContinuation selected source)
    (origins : ActiveBinderCaptureOrigins continuation.receipt.ready
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (backed : ∀ older ∈ continuation.receipt.ready.localBinders,
      BinderTemplatesBefore continuation.receipt.ready continuation.entry.nextRequirement older) :
    LiveBindersSafe continuation.receipt.binding.1.scheme.quantified continuation.result.state := by
  have live := allocate_generalized_live_from_finalizer selected.body.resources
    continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
    continuation.receipt.name.value (some continuation.receipt.name.span) false
    (origins.withLocals continuation.receipt.locals) continuation.substitution backed continuation.retained_binding
  have same : continuation.result.state.inference = continuation.receipt.binding.2.inference :=
    congrArg (fun result : Detail.StatementResult => result.state.inference) continuation.receipt.completed
  have binders : continuation.result.state.localBinders = continuation.receipt.binding.2.localBinders :=
    congrArg (fun result : Detail.StatementResult => result.state.localBinders) continuation.receipt.completed
  intro binder member
  exact (live binder (binders ▸ member)).transport (.of_substitution_eq (congrArg InferState.substitution same))

end InitializerContinuation

/-- Both the generalization and later privacy use one actual statement call
at the chosen original source position. The remaining producer inputs describe
only the old live binders and their genuine pre-initializer template rows. -/
theorem Selected.initializedStatementPrivacy {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {source : Syntax.Statement}
    (position : selected.signature.source.value.body.value[index]? = some source)
    {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr}
    (form : source.value = .letDecl name annotation (some initializer)) :
    ∃ actual : InitializerContinuation selected source,
      ∀ _origins : ActiveBinderCaptureOrigins actual.receipt.ready
          (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)),
        (∀ older ∈ actual.receipt.ready.localBinders,
          BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older) →
        (∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
          Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) ∧
        (∀ requirement ∈ selected.body.body.state.requirements,
          requirement ∉ actual.receipt.ready.requirements →
          ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
            Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) := by
  have progress := selected.inferenceProgress checked
  have formation := Frontend.checkProgram_success_signature_formation checked
  have canonical : ∀ signature ∈ compiled.program.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes) (Ty.productMany signature.returnTypes) := by
    intro signature member
    exact (Frontend.checkProgram_success_function_signature_shape checked member).2
  obtain ⟨occurrence,privacy⟩ := selected.statementPrivacy checked position
  obtain ⟨childFuel,receipt,ready,bodyContinuation⟩ := occurrence.toOccurrence.initialized form formation canonical
  let actual : InitializerContinuation selected source := {
    childFuel := childFuel,entry := occurrence.entry,result := occurrence.result,receipt := receipt,
    retained := occurrence.retained,ready := ready,bodyContinuation := bodyContinuation,
    finalContinuation := bodyContinuation.trans (progress.returnUnification.trans progress.finalization) }
  refine ⟨actual,?_⟩
  intro origins backed
  have inferred := receipt.initializer_inference occurrence.ready formation canonical
  have bound := actual.quantified_below inferred.2.2
  have live := actual.generalized_live origins backed
  have finished := privacy actual.receipt.binding.1.scheme.quantified bound live
  constructor
  · intro type safe
    apply finished.1 type
    exact SafeTransport.of_substitution_eq (congrArg InferState.substitution receipt.inference_eq) type safe
  · intro requirement member fresh type typeMember
    apply finished.2 requirement member _ type typeMember
    have same : occurrence.result.state.requirements = receipt.ready.requirements :=
      congrArg (fun result : Detail.StatementResult => result.state.requirements) receipt.completed
    simpa only [same] using fresh

/-- Public compilation chooses the same selected checker body before the
initialized-declaration boundary is connected to its actual finalizer. -/
theorem compile_initialized_statement_privacy {raw : Workspace.RawWorkspace}
    {seeds : List SourceCoreCompiler.Seed} {options : SourceCoreCompiler.Options}
    {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∃ selected : Selected compiled row options.checkingFuel,
      ∀ {index : Nat} {source : Syntax.Statement},
        selected.signature.source.value.body.value[index]? = some source →
        ∀ {name : Syntax.Identifier} {annotation : Option Syntax.TypeExpr} {initializer : Syntax.Expr},
          source.value = .letDecl name annotation (some initializer) →
          ∃ actual : InitializerContinuation selected source,
            ∀ _origins : ActiveBinderCaptureOrigins actual.receipt.ready
                (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)),
              (∀ older ∈ actual.receipt.ready.localBinders,
                BinderTemplatesBefore actual.receipt.ready actual.entry.nextRequirement older) →
              (∀ type, Safe actual.receipt.binding.1.scheme.quantified actual.receipt.ready type →
                Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) ∧
              (∀ requirement ∈ selected.body.body.state.requirements,
                requirement ∉ actual.receipt.ready.requirements →
                ∀ type ∈ requirement.predicate.subject :: requirement.predicate.arguments,
                  Avoids actual.receipt.binding.1.scheme.quantified (selected.body.finalized.substitution.apply type)) := by
  obtain ⟨selected⟩ := of_compile accepted member
  refine ⟨selected,?_⟩
  intro index source position name annotation initializer form
  exact selected.initializedStatementPrivacy (SourceCoreCompiler.compile_checked_source accepted) position form

end Solcore.SourceSemantics.SourceCompiledLocalFinalization
