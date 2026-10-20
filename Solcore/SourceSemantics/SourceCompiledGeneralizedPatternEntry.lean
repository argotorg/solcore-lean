import Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts

/-! An accepted pattern call provides its declarative pattern typing, the
actual arm context, and both recursive invariants for entering that arm. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization
open ProtectedVariables

private theorem binder_context_fields {owner : Resolved.DeclarationId}
    {before after : SourceSemantics.Context} {binders : List TypedBinder}
    (extension : BindersExtend owner before binders after) :
    after.signatures = before.signatures ∧ after.typeParameters = before.typeParameters ∧
      after.currentDeclaration = before.currentDeclaration ∧
      after.residualTypeVariables = before.residualTypeVariables ∧
      after.solvedRequirements = before.solvedRequirements ∧ after.assumptions = before.assumptions := by
  induction extension with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases head
    simpa only [SourceSemantics.Context.withLocal] using ih

theorem patternEntered
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {patternSource : Syntax.Pattern}
    {expected : Ty} {initial resultState : State} {inferred : TypedMatchPattern}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expected))
    (expectedSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel childFuel inferenceContext patternSource expected initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution expected inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have semanticSignatures : target.signatures = inferenceContext.signatures :=
    invariant.signatures_eq_whole.trans scope.signatures.symm
  have finalOwner : selected.body.finalized.typedSource.owner =
      (checkingContext selected).scope.genericOwner := by
    rw [selected.body.resources.source_eq]
    change selected.body.returned.owner = selected.body.declaration.id
    exact (congrArg State.Header.owner (Detail.unify_state_header selected.body.unified)).trans
      (Detail.inferStatementsFuel_preserves_owner selected.body.inferred)
  have evidence := selected.body.resources.integerPatternEvidenceAt
    invariant.signaturesEq invariant.solvedRequirementsEq invariant.assumptionsMono covered
  obtain ⟨certificate⟩ := inferMatchPatternFuel_success_sound_at formation
    (by simpa only [semanticSignatures] using catalog) semanticSignatures evidence
    invariant.ready expectedBelow invariant.bindersBelow (finalOwner.trans owner.symm)
    (invariant.declarationEq.trans (congrArg some finalOwner.symm)) expectedAdmissible invariant.active
    extension integerPatterns requirements occurs accepted
  have properties := Detail.inferMatchPatternFuel_inferenceProperties invariant.ready expectedBelow
    formation accepted
  have isolated := inferMatchPatternFuel_active_isolation invariant.ready expectedBelow formation
    operational.quantifiersBelow invariant.schemeIsolation operational.privacy expectedSafe accepted
  obtain ⟨signatures, parameters, declaration, residual, solved, assumptions⟩ :=
    binder_context_fields certificate.binders_extend
  refine ⟨certificate, ?_, actual.binders certificate.binders_extend,
    operational.ofPattern invariant.ready formation expectedBelow expectedSafe accepted⟩
  exact {
    active := certificate.pattern_invariant
    ready := properties.2.1
    bindersBelow := certificate.pattern_below
    nodesBelow := (Detail.inferMatchPatternFuel_occurrenceBoundExtends accepted).nodesBelowNextOccurrence
      invariant.nodesBelow
    schemeIsolation := isolated.1
    substitutionExtension := extension
    signaturesEq := signatures.trans invariant.signaturesEq
    typeParametersEq := parameters.trans invariant.typeParametersEq
    declarationEq := declaration.trans invariant.declarationEq
    residual := residual.trans invariant.residual
    solvedRequirementsEq := solved.trans invariant.solvedRequirementsEq
    assumptionsMono := by simpa only [assumptions] using invariant.assumptionsMono }

/-- The single-scrutinee branch enters its first pattern using privacy from the
actual scrutinee call. Reserving the hidden local changes no lexical scheme. -/
theorem patternEntered_after_expression
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel expressionFuel patternFuel : Nat}
    {selected : Selected compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr}
    {patternSource : Syntax.Pattern} {entry scrutineeState initial resultState : State}
    {scrutinee : InferredExpression} {inferred : TypedMatchPattern}
    {hidden : Resolved.LocalId} {frames : List InitializedLetBinding}
    {target : SourceSemantics.Context} {occurrence : NodeId}
    (scope : CheckingScope selected inferenceContext)
    (entryReady : entry.InferenceReady)
    (entryOperational : GeneralizedActualStateInvariant entry (evidenceSource selected))
    (expressionAccepted : Detail.inferExprFuel expressionFuel inferenceContext expression none entry =
      .ok (scrutinee, scrutineeState))
    (allocation : scrutineeState.allocateHiddenLocal = (hidden, initial))
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (actual : ActualContext (checkingContext selected) selected.body.finalized frames target)
    (owner : initial.owner = (checkingContext selected).scope.genericOwner)
    (expectedAdmissible : TypeAdmissible target
      (selected.body.finalized.substitution.apply scrutinee.type))
    (extension : selected.body.finalized.substitution.SemanticallyExtends resultState.inference.substitution)
    (integerPatterns : resultState.integerPatterns ⊆ selected.body.returned.integerPatterns)
    (requirements : resultState.requirements ⊆ selected.body.returned.requirements)
    (occurs : ∀ requirement ∈ inferred.requirements,
      PrimaryRequirementOccursAt selected.body.finalized.typedSource occurrence requirement)
    (covered : TemplateScopeCovered selected.body.finalized.typedSource target occurrence)
    (accepted : Detail.inferMatchPatternFuel patternFuel inferenceContext patternSource scrutinee.type initial =
      .ok (inferred, resultState)) :
    ∃ certificate : MatchPatternInferenceCertificate selected.body.finalized.typedSource target
        selected.body.finalized.substitution scrutinee.type inferred resultState,
      RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized
        resultState certificate.armContext ∧
      ActualContext (checkingContext selected) selected.body.finalized frames certificate.armContext ∧
      GeneralizedActualStateInvariant resultState (evidenceSource selected) := by
  have formation := scope.formation checked
  have catalog := scope.catalog checked
  have canonical := scope.functionsCanonical checked
  have properties := Detail.inferExprFuel_inferenceProperties entryReady formation canonical
    (by simp) expressionAccepted
  have privacy := entryOperational.expression_result_private entryReady catalog formation canonical expressionAccepted
  have operational := (entryOperational.ofExpression entryReady catalog formation canonical
    (by simp) (by simp) expressionAccepted).allocateHiddenLocal
  have initialEq := congrArg Prod.snd allocation
  simp only at initialEq
  subst initial
  exact patternEntered checked scope invariant actual operational owner properties.2.2
    expectedAdmissible privacy extension integerPatterns requirements occurs covered accepted

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
