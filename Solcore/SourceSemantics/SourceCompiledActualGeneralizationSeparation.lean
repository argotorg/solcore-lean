import Solcore.SourceSemantics.SourceCompiledActualGeneralizationLifetime
import Solcore.SourceSemantics.SourceInferenceActualGeneralizationSites
import Solcore.SourceSemantics.SourceInferenceActualCallPathComparison
import Solcore.SourceSemantics.SourceInferenceActualCallOrder

/-! Exact sites, lifetime bounds and actual path divergence compare retained
owners. Ancestors use the real initializer output, siblings use allocator order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open ProtectedVariables SourceCompiledLocalFinalization SourceCompiledGeneralizedSoundness
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {cached : SourceCoreUnifiedCompilation.Compiled} {checkingFuel index : Nat}
    {named : SourceCoreGeneralFunctions.Function}
    {selected : BodySelection compiled named.specialized checkingFuel}

theorem Site.seed
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    {call : CallIndex} {binder : TypedBinder} {initializer : ExpressionId}
    (here : selected.InferenceCall call) (site : Site call binder initializer)
    (retained : ({binder, initializer := .expression initializer} : InitializedLetBinding) ∈
      initializedLetBindings (evidenceSource selected)) :
    ∃ event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution binder initializer,
      GeneralizationLifetime event call.initial.inference.next call.final call.outputTypes := by
  have inputs := selected.actualCall_inputs checked here
  cases site with
  | statement receipt =>
      obtain ⟨ready, extension, seed⟩ := RawStatementLifetime.lifetime selected.body.resources receipt
        inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
        (selected.actualCall_liveTemplatesBacked checked here)
        (selected.actualCall_captureOrigins checked here) retained
        (selected.statementReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
      exact ⟨_, seed⟩
  | header receipt =>
      obtain ⟨ready, extension, seed⟩ := RawHeaderLifetime.lifetime selected.body.resources receipt
        inputs.ready inputs.wellFormed inputs.catalog.catalog inputs.catalog.formation inputs.catalog.canonical
        (selected.actualCall_liveTemplatesBacked checked here)
        (selected.actualCall_captureOrigins checked here) retained
        (selected.headerReceipt_retained here receipt) (selected.actualCall_final_extension checked here)
      exact ⟨_, seed⟩

theorem Site.ancestor_excludes
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    {outerCall innerCall : CallIndex} {outer inner : TypedBinder} {outerId innerId : ExpressionId}
    (here : selected.InferenceCall outerCall)
    (outerSite : Site outerCall outer outerId) (innerSite : Site innerCall inner innerId)
    (path : CallOccurrence outerCall innerCall) (different : outer ≠ inner)
    {event : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution inner innerId}
    (seed : GeneralizationLifetime event innerCall.initial.inference.next innerCall.final innerCall.outputTypes) :
    ∀ q ∈ outer.scheme.quantified, q ∉ inner.scheme.quantified := by
  rcases path.uncons with same | ⟨child, step, rest⟩
  · cases same
    exact False.elim (different (outerSite.unique innerSite).1)
  · obtain ⟨actualChild, actualStep, unique, quantifiedOutputs⟩ := outerSite.initializer_child here.accepted
    have same := unique child step
    cases same
    have life := CallOccurrence.lifetime_at artifact checked position (.child here actualStep) rest seed
    intro q outerQuantified innerQuantified
    obtain ⟨type, member, occurs⟩ := quantifiedOutputs q outerQuantified
    exact (life.values type member) q occurs innerQuantified

theorem Site.excludes_of_child_order
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw checkingFuel = .ok compiled.program)
    (position : cached.indexed.base.functions[index]? = some named)
    (ordered : ∀ {parent first second}, selected.InferenceCall parent →
      ChildStep parent first → ChildStep parent second → first.Ordered second)
    {leftCall rightCall : CallIndex} {left right : TypedBinder} {leftId rightId : ExpressionId}
    (leftHere : selected.InferenceCall leftCall) (rightHere : selected.InferenceCall rightCall)
    (leftSite : Site leftCall left leftId) (rightSite : Site rightCall right rightId)
    (different : left ≠ right)
    {leftEvent : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution left leftId}
    {rightEvent : RetainedGeneralization (evidenceSource selected) selected.body.finalized.substitution right rightId}
    (leftSeed : GeneralizationLifetime leftEvent leftCall.initial.inference.next leftCall.final leftCall.outputTypes)
    (rightSeed : GeneralizationLifetime rightEvent rightCall.initial.inference.next rightCall.final rightCall.outputTypes) :
    ∀ q ∈ left.scheme.quantified, q ∉ right.scheme.quantified := by
  rcases leftHere.compare_paths rightHere with forward | backward |
    ⟨parent, first, second, reached, a, b, distinct, rest, other⟩
  · exact leftSite.ancestor_excludes artifact checked position leftHere rightSite forward different rightSeed
  · have reversed := rightSite.ancestor_excludes artifact checked position rightHere leftSite backward
      (fun same => different same.symm) leftSeed
    exact fun q leftQuantified rightQuantified => reversed q rightQuantified leftQuantified
  · have leftLife := CallOccurrence.lifetime_at artifact checked position (.child reached a) rest leftSeed
    have rightLife := CallOccurrence.lifetime_at artifact checked position (.child reached b) other rightSeed
    rcases ordered reached a b with same | earlier | later
    · exact False.elim (distinct same)
    · intro q leftQuantified rightQuantified
      have lower := Nat.le_trans rightLife.createdAfter (rightLife.allocated q rightQuantified)
      have upper := Nat.lt_of_lt_of_le (leftLife.bound q leftQuantified) earlier
      exact Nat.not_lt_of_ge lower upper
    · intro q leftQuantified rightQuantified
      have lower := Nat.le_trans leftLife.createdAfter (leftLife.allocated q leftQuantified)
      have upper := Nat.lt_of_lt_of_le (rightLife.bound q rightQuantified) later
      exact Nat.not_lt_of_ge lower upper

end Solcore.SourceSemantics.SourceInferenceExecution.ActualGeneralization
