import Solcore.SourceSemantics.SourceInferenceSelectedLetState
import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicGeneralization
import Solcore.SourceSemantics.SourceInferenceSelectedMonomorphicLocalPresence

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem ActualStateInvariant.monomorphicBinders {state : State} {source : TypedSource}
    (invariant : ActualStateInvariant state source) :
    ∀ binder ∈ state.localBinders, binder.scheme.quantified = [] := by
  intro binder member
  rcases invariant.origins.origin binder member with mono | retained
  · exact mono
  · exact invariant.sourceMonomorphic binder retained

theorem monomorphicBinders_isolation {state : State}
    (monomorphic : ∀ binder ∈ state.localBinders, binder.scheme.quantified = []) :
    ActiveSchemeQuantifierIsolation state := by
  intro binder member metavariable quantified
  obtain ⟨owner, ownerMember, ownerQuantified⟩ := List.mem_flatMap.mp quantified
  rw [monomorphic owner ownerMember] at ownerQuantified
  cases ownerQuantified

theorem monomorphicBinders_bound {state : State}
    (monomorphic : ∀ binder ∈ state.localBinders, binder.scheme.quantified = []) :
    ActiveQuantifiersBelowNext state := by
  intro binder member metavariable quantified
  rw [monomorphic binder member] at quantified
  cases quantified

theorem actual_letUnannotatedInitialized
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {name : Syntax.Identifier} {initializer : Syntax.Expr}
    {expectedReturn : Ty} {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding} {semanticContext : SourceSemantics.Context} {roots : List NodeId}
    (form : statement.value = .letDecl name none (some initializer))
    (allocation : initial.allocateStatementId = (id, allocated))
    (accepted : Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn initial = .ok result)
    {wholeReturn : Ty}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (formation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functions : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes) (Ty.productMany candidate.returnTypes))
    (invariant : RecursiveStatementInvariant wholeContext expectedReturn finalized initial semanticContext)
    (contextAt : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (rawResult : RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (requirementsSubset : result.state.requirements ⊆ evidenceState.requirements)
    (initializerSound : ∀ {inferred : InferredExpression} {initializerState : State},
      Detail.inferExprFuel fuel inferenceContext initializer none allocated = .ok (inferred, initializerState) →
      ExpressionHasType ((initializerState.toTypedSource roots).applySubstitution finalized.substitution)
        semanticContext inferred.id (finalized.substitution.apply inferred.type)) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  have initialMonomorphic := operational.monomorphicBinders
  obtain ⟨inferred, initializerState, locals, valueType, generalized, binding,
    childSuccess, localsEq, valueEq, generalizedEq, bindingEq, resultEq, contains⟩ :=
    inferStatementFuel_success_letUnannotatedInitialized_facts form allocation accepted roots
  have retained : ContainsStatement (evidenceState.toTypedSource roots) result.id {
      id := result.id, span := statement.span, type := result.type, form := .letDecl binding.1 (some inferred.id) } := by
    refine ⟨rawResult.nodes _ contains.1 (.inl ?_), contains.2⟩
    rfl
  have rawMono : binding.1.scheme.quantified = [] := operational.sourceMonomorphic _
    (retained.initializedLetBinder_mem (by simp [StatementForm.initializedLetBinders]))
  have binderEq := congrArg Prod.fst bindingEq
  have generalizedMono : generalized.scheme.quantified = [] := by
    rw [← binderEq] at rawMono
    exact rawMono
  have schemeEq : generalized.scheme = .mono valueType := by
    have bodyEq : generalized.scheme.body = valueType := by rw [generalizedEq]; rfl
    cases scheme : generalized.scheme with
    | mk quantified body =>
      simp only [scheme] at generalizedMono bodyEq
      simp only [generalizedMono, bodyEq, Scheme.mono]
  have requirementsEq : generalized.requirements = [] := by
    rw [generalizedEq]
    apply Detail.generalizeValue_requirements_empty_of_quantified_eq_nil
    rwa [← generalizedEq]
  have bindersEq : initializerState.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocatedEq := congrArg (fun state : State => state.localBinders) (congrArg Prod.snd allocation)
    exact childEq.trans allocatedEq.symm
  have resultMonomorphic : ∀ binder ∈ result.state.localBinders, binder.scheme.quantified = [] := by
    intro binder member
    rw [resultEq, ← bindingEq] at member
    change binder ∈ _ :: initializerState.localBinders at member
    rcases List.mem_cons.mp member with rfl | member
    · exact generalizedMono
    · exact initialMonomorphic binder (bindersEq ▸ member)
  have statementSound : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution finalContext ∧
      StatementHasType ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn, loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
    apply inferStatementFuel_success_letUnannotatedInitialized_sound form allocation accepted invariant.active
      invariant.bindersBelow roots
    intro actualInferred actualState actualLocals actualValue actualGeneralized actualBinding actualSuccess
      actualLocalsEq actualValueEq actualGeneralizedEq actualBindingEq
    have same := Except.ok.inj (childSuccess.symm.trans actualSuccess)
    cases same
    have sameLocals : actualLocals = locals := actualLocalsEq.trans localsEq.symm
    cases sameLocals
    have sameValue : actualValue = valueType := actualValueEq.trans valueEq.symm
    cases sameValue
    have sameGeneralized : actualGeneralized = generalized := actualGeneralizedEq.trans generalizedEq.symm
    cases sameGeneralized
    have sameBinding : actualBinding = binding := actualBindingEq.symm.trans bindingEq
    cases sameBinding
    have rawScheme : binding.1.scheme = .mono valueType := by
      rw [← binderEq]
      exact schemeEq
    have rawRequirements : binding.1.schemeRequirements = [] := by
      rw [← binderEq]
      exact requirementsEq
    have contextEq : localSchemeInitializerContext semanticContext
        (binding.1.applySubstitution finalized.substitution) = semanticContext := by
      rw [localSchemeInitializerContext_eq_withTypeVariables _ _ (by simp [rawRequirements])]
      rw [show (binding.1.applySubstitution finalized.substitution).scheme.quantified = [] from rawMono]
      exact Context.withTypeVariables_nil _
    have substitutionEq : result.state.inference.substitution = initializerState.inference.substitution := by
      rw [resultEq, ← bindingEq]
      rfl
    have childExtension : finalized.substitution.SemanticallyExtends initializerState.inference.substitution := by
      rwa [substitutionEq] at extension
    have bodyEq : (binding.1.applySubstitution finalized.substitution).scheme.body =
        finalized.substitution.apply inferred.type := by
      simpa [TypedBinder.applySubstitution, rawScheme, Scheme.apply, Scheme.mono, Substitution.without,
        valueEq, State.resolve, InferState.resolve] using childExtension inferred.type
    obtain ⟨otherInferred, otherState, otherSuccess, provenance⟩ :=
      inferStatementFuel_success_letUnannotatedInitialized_child_provenance form allocation accepted invariant.nodesBelow roots
    have same := Except.ok.inj (childSuccess.symm.trans otherSuccess)
    cases same
    have localsFacts := MonomorphicGeneralization.initializer_locals allocation childSuccess localsEq
      invariant.active.aligned initialMonomorphic childExtension
    have childRequirements : initializerState.requirements ⊆ evidenceState.requirements := by
      have requirementEq : result.state.requirements = initializerState.requirements := by
        rw [resultEq, ← bindingEq]
        rfl
      rwa [requirementEq] at requirementsSubset
    apply unannotatedInitializedLetCertificate_of_finalMonomorphic resources generalizedEq bindingEq
      rawMono localsFacts.1 localsFacts.2 childRequirements childExtension invariant.solvedRequirementsEq
    rw [contextEq, bodyEq]
    exact ExpressionHasType.weakenSource (provenance.sourceExtension.applySubstitution finalized.substitution)
      (initializerSound childSuccess)
  obtain ⟨finalContext, facts, finalInvariant, typed, matching⟩ :=
    invariant.close_statement_branch accepted formation functions
      (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow accepted)
      extension (monomorphicBinders_isolation resultMonomorphic) statementSound
  exact ⟨finalContext, facts, finalInvariant, contextAt.of_statement typed,
    operational.ofStatementWithScope accepted (ActiveBinderCaptureOrigins.of_monomorphic resultMonomorphic)
      (monomorphicBinders_bound resultMonomorphic), typed, matching⟩


end Solcore.SourceSemantics.SourceInferenceSoundness
