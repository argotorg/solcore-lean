import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimes
import Solcore.SourceSemantics.SourceInferenceSelectedPrivacyReturnFinalization
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts

/-! An actual generalization lifetime transports the entering lexical schemes
through the enclosing computation and its real finalizer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
open Frontend SourceInference TypeSystem SourceInferenceSoundness ProtectedVariables
open SourceCompiledLocalFinalization
open SourceCompiledGeneralizedSoundness

private theorem scheme_variable_origin (substitution : Substitution) (scheme : Scheme)
    {q : TypeVarId} (occurs : q ∈ (scheme.apply substitution).freeVariables) :
    ∃ source, source ∈ scheme.freeVariables ∧
      q ∈ (substitution.apply (.variable source)).freeVariables := by
  obtain ⟨body, outside⟩ := List.mem_filter.mp occurs
  have notQuantified : q ∉ scheme.quantified := by
    intro member
    simp only [Scheme.apply, member, decide_true, Bool.not_true] at outside
    contradiction
  obtain ⟨source, sourceMember, image⟩ := apply_variable_origin
    (substitution.without scheme.quantified) scheme.body q body
  have sourceOutside : source ∉ scheme.quantified := by
    intro member
    have same : q = source := by
      simpa only [Substitution.apply, Substitution.lookup?_without_of_mem substitution member,
        Option.getD_none, Ty.freeVariables, List.mem_singleton] using image
    exact notQuantified (same ▸ member)
  refine ⟨source, List.mem_filter.mpr ⟨sourceMember, ?_⟩, ?_⟩
  · simp [sourceOutside]
  · simpa only [Substitution.apply,
      FlexibleSubstitution.Substitution.lookup?_without_of_not_mem substitution sourceOutside] using image

/-- The final local-variable exclusion consumes the actual lifetime's
transport, including after the original lexical scope has been restored. -/
theorem local_variables {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} (selected : BodySelection compiled row fuel)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {binder : TypedBinder} {initializer : ExpressionId}
    (event : RetainedGeneralization (SourceCompiledGeneralizedSoundness.evidenceSource selected)
      selected.body.finalized.substitution binder initializer)
    {entryNext : Nat} {outputs : List Ty}
    (lifetime : GeneralizationLifetime event entryNext selected.body.body.state outputs)
    (live : LiveBindersSafe binder.scheme.quantified event.readyState)
    {target : SourceSemantics.Context}
    (aligned : LocalEnvironmentAligned event.readyState selected.body.finalized.substitution target) :
    ∀ q ∈ binder.scheme.quantified,
      q ∉ target.locals.flatMap (fun entry => entry.2.freeVariables) := by
  intro q quantified occurs
  obtain ⟨entry, member, free⟩ := List.mem_flatMap.mp occurs
  have originalMember := aligned.locals_perm.mem_iff.mpr member
  obtain ⟨older, olderMember, same⟩ := List.mem_map.mp originalMember
  subst entry
  have free : q ∈ (older.scheme.apply selected.body.finalized.substitution).freeVariables := by
    simpa only [FlexibleSubstitution.applyTypedBinder_scheme] using free
  obtain ⟨metavariable, freeVariable, image⟩ := scheme_variable_origin
    selected.body.finalized.substitution older.scheme free
  have readySafe := (live older olderMember).body metavariable freeVariable
  have finalSafe := selected.finishPrivacy checked binder.scheme.quantified (.variable metavariable)
    (lifetime.transport _ readySafe)
  exact finalSafe q image quantified

/-- The actual statement boundary derives ready-state lexical privacy from
the executable generalizer and retained finalizer checks. -/
theorem statement_ready_live {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}
    (checked : checkProgram raw fuel = .ok compiled.program)
    {source : Syntax.Statement} (occurrence : BodyInitializerOccurrence selected source)
    {expectedReturn : Ty} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : StatementBoundary selected (occurrence.childFuel + 1)
      occurrence.inferenceContext source expectedReturn occurrence.entry occurrence.result frames target) :
    LiveBindersSafe occurrence.receipt.binding.1.scheme.quantified occurrence.receipt.ready := by
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    occurrence.receipt boundary.operational.backed boundary.invariant.ready
    boundary.operational.requirements (boundary.scope.formation checked)
    (boundary.scope.functionsCanonical checked)
  exact generalized_live_from_finalizer selected.body.resources
    (boundary.operational.origins.congr_localBinders occurrence.receipt.ready_binders)
    occurrence.extension occurrence.retained rfl templates

/-- The same derivation uses the literal header binder retained by the actual
for-item boundary. -/
theorem header_ready_live {raw : Workspace.RawWorkspace}
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction}
    {fuel : Nat} {selected : BodySelection compiled row fuel}
    (checked : checkProgram raw fuel = .ok compiled.program)
    {childFuel : Nat} {context : SourceInference.Context} {source : Syntax.ForItem}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (boundary : ForItemBoundary selected (childFuel + 1) context source expectedReturn
      initial inferred final frames target)
    (receipt : LocalHeaderRequirementTiming.Receipt childFuel context source initial (inferred, final)) :
    LiveBindersSafe receipt.binding.1.scheme.quantified receipt.ready := by
  have templates := ProtectedVariables.LocalHeaderRequirementTiming.Receipt.templates_before
    receipt boundary.operational.backed boundary.invariant.ready boundary.operational.requirements
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
  have extension : selected.body.finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    have atResult := boundary.extension
    rwa [receipt.inference_eq] at atResult
  have retained : receipt.binding.1 ∈ (evidenceSource selected).initializedLetBinders := by
    apply (boundary.bindingsRetained ⟨receipt.binding.1, .expression receipt.value.id⟩ ?_).1
    have itemEq : inferred = .letDecl receipt.binding.1 (some receipt.value.id) := receipt.recorded
    rw [congrArg forItemInitializedLetBindings itemEq]
    exact List.mem_singleton_self _
  exact generalized_live_from_finalizer selected.body.resources
    (boundary.operational.origins.congr_localBinders receipt.ready_binders)
    extension retained rfl templates

end Solcore.SourceSemantics.SourceBodyGeneralizationLocalPrivacy
