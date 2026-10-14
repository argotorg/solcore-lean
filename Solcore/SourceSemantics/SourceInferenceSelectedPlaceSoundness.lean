import Solcore.SourceSemantics.SourceInferenceActualRootedContracts
import Solcore.SourceSemantics.SourceInferenceSelectedStatementState

/-! Mapping-key inference retains the actual generalized-initializer scope.
Each recursive key is selected by its original place reference. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem sourcePlace_type_admissible {source : TypedSource} {context : SourceSemantics.Context}
    {place : PlaceResolution} {type : Ty} (typed : SourcePlaceHasType source context place type) :
    TypeAdmissible context type := by
  have projections {before after : Ty} {projections : List PlaceProjection}
      (typed : SourceProjectionsHaveType source context before projections after)
      (valid : TypeAdmissible context before) : TypeAdmissible context after := by
    induction projections generalizing before after with
    | nil => cases typed; exact valid
    | cons projection rest induction =>
      cases typed with
      | index key tail => exact induction tail (TypeAdmissible.mapping_value valid)
      | member selected tail => exact induction tail selected.member_type_admissible
  cases typed with
  | intro root rest _ => exact projections rest root.type_admissible

theorem ActualStateInvariant.ofPlace
    {fuel : Nat} {context : Frontend.SourceInference.Context} {target : Syntax.Expr}
    {initial final : State} {place : PlaceResolution} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferPlaceFuel fuel context target initial = .ok (place, final))
    (nextLe : initial.inference.next ≤ final.inference.next) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have bindersEq := congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq success)
  exact ⟨⟨pending, (actualLedgerFamily fuel).place success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

def ActualInferPlaceFuelRootedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {targetExpression : Syntax.Expr}
    {initial final parentState evidenceState : State}
    {place : PlaceResolution} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    Detail.inferPlaceFuel fuel inferenceContext targetExpression initial =
      .ok (place, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext →
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    finalized.substitution.SemanticallyExtends
      final.inference.substitution →
    TypingSourceExtends (final.toTypedSource roots)
      (parentState.toTypedSource roots) →
    (∀ key, .expression key ∈ place.references →
      RawSubtreePreserved (parentState.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.expression key)) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    (∀ key, .expression key ∈ place.references →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.expression key)) →
    (∀ key, .expression key ∈ place.references →
      ActualContext.Covers finalized frames (.expression key)) →
    SourcePlaceHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext (place.applySubstitution finalized.substitution)
      (finalized.substitution.apply place.type)

theorem actualInferPlaceFuelRootedSoundness :
    ∀ fuel, (∀ childFuel, childFuel < fuel →
      ActualInferExprFuelRootedSoundness childFuel) →
      ActualInferPlaceFuelRootedSoundness fuel := by
  intro fuel
  induction fuel with
  | zero =>
      intro _ wholeContext inferenceContext wholeReturn targetExpression
        initial final parentState evidenceState place roots finalized
        frames semanticContext success
      simp [Detail.inferPlaceFuel] at success
  | succ fuel induction =>
      intro expressionSound wholeContext inferenceContext wholeReturn
        targetExpression initial final parentState evidenceState place roots
        finalized frames semanticContext success resources interfaces signaturesEq ownerEq
        parametersEq assumptionsEq signatureFormation functionsCanonical
        catalog signatureParameters invariant actual operational finalSubstitutionExtension
        finalToParent rawParentToEvidence patternsSubset literalsSubset
        requirementsSubset keysCovered keysActualCovered
      cases targetEq : targetExpression.value
      case identifier name =>
        exact inferPlaceFuel_success_identifier_sound targetEq success
          invariant.active finalSubstitutionExtension
      case group inner =>
        have innerSuccess : Detail.inferPlaceFuel fuel inferenceContext inner
            initial = .ok (place, final) := by
          simpa only [Detail.inferPlaceFuel, targetEq] using success
        exact induction
          (fun childFuel childLt => expressionSound childFuel
            (Nat.lt_trans childLt (Nat.lt_succ_self fuel)))
          innerSuccess resources interfaces signaturesEq ownerEq parametersEq
          assumptionsEq signatureFormation functionsCanonical catalog
          signatureParameters invariant actual operational finalSubstitutionExtension
          finalToParent rawParentToEvidence patternsSubset literalsSubset
          requirementsSubset keysCovered keysActualCovered
      case index base brackets key =>
        obtain ⟨basePlace, baseState, keyInitial, inferredKey, baseSuccess,
            baseInvariant, unifySuccess, keySuccess, placeEq, keyInvariant,
            keyExpectedBelow, keyMember⟩ :=
          inferPlaceFuel_index_key_invariant targetEq success
            signatureFormation functionsCanonical invariant
            finalSubstitutionExtension
        obtain ⟨actualBasePlace, actualBaseState, actualBaseSuccess,
            _baseBelow, baseToFinal, baseLiteralsToFinal,
            basePatternsToFinal, baseRequirementsToFinal⟩ :=
          inferPlaceFuel_success_index_base_state_provenance targetEq
            success invariant.nodesBelow roots
        rw [baseSuccess] at actualBaseSuccess
        obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualBaseSuccess).symm
        have baseToParent : TypingSourceExtends
            (baseState.toTypedSource roots)
            (parentState.toTypedSource roots) :=
          baseToFinal.trans finalToParent
        have baseKeysCovered : ∀ keyId,
            .expression keyId ∈ basePlace.references →
              TemplateScopeCovered finalized.typedSource semanticContext
                (.expression keyId) := by
          intro keyId member
          exact keysCovered keyId
            (inferPlaceFuel_index_base_references_subset targetEq
              baseSuccess success member)
        have baseTyped : SourcePlaceHasType
            ((parentState.toTypedSource roots).applySubstitution
              finalized.substitution) semanticContext
            (basePlace.applySubstitution finalized.substitution)
            (finalized.substitution.apply basePlace.type) :=
          induction
            (fun childFuel childLt => expressionSound childFuel
              (Nat.lt_trans childLt (Nat.lt_succ_self fuel)))
            baseSuccess resources interfaces signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters invariant actual operational baseInvariant.substitutionExtension
            baseToParent (fun keyId member => rawParentToEvidence keyId
              (inferPlaceFuel_index_base_references_subset targetEq baseSuccess success member))
            (List.Subset.trans basePatternsToFinal patternsSubset)
            (List.Subset.trans baseLiteralsToFinal literalsSubset)
            (List.Subset.trans baseRequirementsToFinal requirementsSubset)
            baseKeysCovered (fun keyId member => keysActualCovered keyId
              (inferPlaceFuel_index_base_references_subset targetEq baseSuccess success member))
        have baseProperties := Detail.inferPlaceFuel_inferenceProperties invariant.ready signatureFormation functionsCanonical baseSuccess
        have baseOperational := operational.ofPlace baseSuccess baseProperties.1.next_le
        have keyOperational := baseOperational.fresh.fresh.unify unifySuccess
        have baseEq : finalized.substitution.apply basePlace.type =
            .mapping (finalized.substitution.apply baseState.fresh.1)
              (finalized.substitution.apply baseState.fresh.2.fresh.1) := by
          calc
            finalized.substitution.apply basePlace.type = finalized.substitution.apply (keyInitial.resolve basePlace.type) := by
              simpa only [State.resolve, InferState.resolve] using (keyInvariant.substitutionExtension basePlace.type).symm
            _ = finalized.substitution.apply (keyInitial.resolve (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)) :=
              congrArg finalized.substitution.apply (Detail.unify_resolve_eq unifySuccess)
            _ = .mapping (finalized.substitution.apply baseState.fresh.1)
                  (finalized.substitution.apply baseState.fresh.2.fresh.1) := by
              simpa only [State.resolve, InferState.resolve, Substitution.apply] using
                keyInvariant.substitutionExtension (.mapping baseState.fresh.1 baseState.fresh.2.fresh.1)
        have keyExpectedAdmissible : ∀ type ∈ (some (keyInitial.resolve baseState.fresh.1) : Option Ty),
            TypeAdmissible semanticContext (finalized.substitution.apply type) := by
          intro type member
          have same : type = keyInitial.resolve baseState.fresh.1 := Option.some.inj member.symm
          subst type
          have resolved : finalized.substitution.apply (keyInitial.resolve baseState.fresh.1) =
              finalized.substitution.apply baseState.fresh.1 := by
            simpa only [State.resolve, InferState.resolve] using keyInvariant.substitutionExtension baseState.fresh.1
          rw [resolved]
          have valid := sourcePlace_type_admissible baseTyped
          rw [baseEq] at valid
          exact TypeAdmissible.mapping_key valid
        have keyExpectedBound :
            ∀ expectedType ∈
              (some (keyInitial.resolve baseState.fresh.1) : Option Ty),
              expectedType.VariablesBelow keyInitial.inference.next := by
          intro expectedType member
          simp only [Option.mem_def] at member
          cases member
          exact keyExpectedBelow
        have keyTyped : ExpressionHasType
            ((parentState.toTypedSource roots).applySubstitution
              finalized.substitution) semanticContext inferredKey.id
            (finalized.substitution.apply inferredKey.type) :=
          expressionSound fuel (Nat.lt_succ_self fuel) keySuccess resources interfaces
            finalSubstitutionExtension signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters keyInvariant actual keyOperational keyExpectedBound keyExpectedAdmissible
            (SubtreePreserved.ofTypingSourceExtends
              (finalToParent.applySubstitution finalized.substitution))
            ((rawParentToEvidence inferredKey.id keyMember).monoBefore finalToParent)
            patternsSubset literalsSubset requirementsSubset
            (keysCovered inferredKey.id keyMember) (keysActualCovered inferredKey.id keyMember)
        exact inferPlaceFuel_index_sound_of_actual_typed_children
          baseSuccess unifySuccess keySuccess placeEq
          keyInvariant.substitutionExtension finalSubstitutionExtension
          baseTyped keyTyped
      all_goals simp [Detail.inferPlaceFuel, targetEq] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
