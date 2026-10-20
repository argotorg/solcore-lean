import Solcore.SourceSemantics.SourceCompiledGeneralizedStatementInvariant
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrenceState

/-! The actual generalized binder preserves raw lexical quantifier isolation.
Resolved privacy alone is insufficient: the proof also uses the exact freshly
generalized variables, which the solved initializer substitution leaves fixed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledGeneralizedSoundness ProtectedVariables

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    {selected : Selected compiled row fuel} {source : Syntax.Statement}

theorem schemeIsolation (continuation : InitializerOccurrence selected source)
    (isolated : ActiveSchemeQuantifierIsolation continuation.entry)
    (resultPrivate : ActiveQuantifiersPrivate continuation.result.state) :
    ActiveSchemeQuantifierIsolation continuation.result.state := by
  have body : continuation.receipt.binding.1.scheme.body =
      continuation.receipt.ready.resolve continuation.receipt.value.type := by
    change continuation.receipt.generalized.scheme.body = _
    exact Detail.generalizeValue_scheme_body _ _ _ _
  intro binder member q quantified free
  have casesQuantified :
      q ∈ continuation.receipt.binding.1.scheme.quantified ∨
      q ∈ activeSchemeQuantifiers continuation.entry := by
    simpa only [activeSchemeQuantifiers, continuation.receipt.result_binders,
      List.flatMap_cons, List.mem_append] using quantified
  rcases casesQuantified with fresh | prior
  · have selectedMember : continuation.receipt.binding.1 ∈ continuation.result.state.localBinders := by
      rw [continuation.receipt.result_binders]
      exact List.mem_cons_self
    have safe := (resultPrivate continuation.receipt.binding.1 selectedMember binder member).1 q free
    have occurs : q ∈ (continuation.receipt.ready.resolve continuation.receipt.value.type).freeVariables :=
      (List.mem_filter.mp fresh).1
    have outside := continuation.ready.solved.apply_variables_outside_domain
      continuation.receipt.value.type q occurs
    have fixed : continuation.result.state.resolve (.variable q) = .variable q := by
      simp only [State.resolve, InferState.resolve, continuation.receipt.inference_eq,
        Substitution.apply, (Substitution.lookup?_eq_none_iff_not_mem_domain _ _).mpr outside,
        Option.getD_none]
    exact safe q (by simp only [fixed, Ty.freeVariables, List.mem_singleton]) fresh
  · rw [continuation.receipt.result_binders] at member
    rcases List.mem_cons.mp member with rfl | member
    · have occurs := (List.mem_filter.mp free).1
      rw [body] at occurs
      exact continuation.priorAvoided q occurs prior
    · exact isolated binder member q prior free

theorem statement_of_child_recursive
    {raw : Workspace.RawWorkspace} {expectedReturn : Ty}
    (continuation : InitializerOccurrence selected source)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context} {frames : List InitializedLetBinding}
    (scope : CheckingScope selected continuation.inferenceContext)
    (entering : GeneralizedActualStateInvariant continuation.entry
      (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)))
    (invariant : RecursiveStatementInvariant
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      expectedReturn selected.body.finalized continuation.entry target)
    (actual : ActualContext
      (context compiled.program.environment compiled.program.signatures
        selected.signature selected.body.declaration)
      selected.body.finalized frames target)
    (covered : ActualContext.Covers selected.body.finalized frames
      (.statement continuation.entry.allocateStatementId.1))
    (barrier : GeneralizationBarrierTransport continuation.receipt.ready continuation.receipt.locals
      continuation.entry.nextRequirement (continuation.receipt.ready.resolve continuation.receipt.value.type)
      selected.body.finalized.substitution target
      (localSchemeTemplateIds (continuation.receipt.binding.1.applySubstitution selected.body.finalized.substitution)))
    (child :
      RecursiveExpressionInvariant
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized continuation.entry.allocateStatementId.2
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized (frames ++ [continuation.initializerBinding])
        (localSchemeInitializerContext target continuation.initializerBinding.binder) →
      ActualContext.Covers selected.body.finalized (frames ++ [continuation.initializerBinding])
        (.expression continuation.receipt.value.id) →
      ExpressionHasType selected.body.finalized.typedSource
        (localSchemeInitializerContext target continuation.initializerBinding.binder)
        continuation.receipt.value.id
        (selected.body.finalized.substitution.apply continuation.receipt.value.type)) :
    ∃ finalContext,
      RecursiveStatementInvariant (checkingContext selected) expectedReturn
        selected.body.finalized continuation.result.state finalContext ∧
      ActualContext
        (context compiled.program.environment compiled.program.signatures
          selected.signature selected.body.declaration)
        selected.body.finalized frames finalContext ∧
      GeneralizedActualStateInvariant continuation.result.state
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement)) ∧
      StatementHasType selected.body.finalized.typedSource
        { returnType := selected.body.finalized.substitution.apply expectedReturn,
          loopDepth := continuation.inferenceContext.loopDepth } target continuation.result.id finalContext {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      StatementResultMatchesFactsAfterSubstitution selected.body.finalized.substitution continuation.result {
        type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } := by
  obtain ⟨finalContext, active, actualFinal, operational, typed, matching⟩ :=
    continuation.statement_of_child_with_state checked scope.signatures entering
      (.ofStatement invariant) actual covered barrier child
  have accepted := initializedReceipt_accepted continuation.receipt expectedReturn
  have extension : selected.body.finalized.substitution.SemanticallyExtends
      continuation.result.state.inference.substitution := by
    rw [continuation.receipt.inference_eq]
    exact continuation.substitution
  have finalInvariant := invariant.of_retained_statement_typing accepted
    (scope.formation checked) (scope.functionsCanonical checked) active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
    extension (continuation.schemeIsolation invariant.schemeIsolation operational.privacy) typed
  exact ⟨finalContext, finalInvariant, actualFinal, operational, typed, matching⟩

end Solcore.SourceSemantics.SourceCompiledLocalFinalization.InitializerOccurrence
