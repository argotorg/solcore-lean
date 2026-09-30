import Solcore.SourceSemantics.SourceInferenceStatementExpressionSoundness
import Solcore.SourceSemantics.SourceInferenceUnannotatedLetCertificate

/-!
Actual-success source-place inference.  The recursive index case is tied to
its own inferred mapping key, so the statement proof never assumes that an
unrelated expression is well typed.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- A place traversal cannot change visible scheme quantifiers: indexed keys
and grouping restore the caller's lexical binder stack. -/
theorem activeSchemeQuantifierIsolation_inferPlaceFuel
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression : Syntax.Expr} {initial final : State}
    {place : PlaceResolution}
    (isolated : ActiveSchemeQuantifierIsolation initial)
    (success : Detail.inferPlaceFuel fuel inferenceContext targetExpression
      initial = .ok (place, final)) :
    ActiveSchemeQuantifierIsolation final := by
  apply activeSchemeQuantifierIsolation_transport isolated
  have scopeEq := Detail.inferPlaceFuel_success_lexicalScope_eq success
  simpa only [State.lexicalScope] using
    congrArg LexicalScope.binders scopeEq

/-- The expression invariant can cross a successful place traversal when the
whole final substitution is known to extend its result. -/
theorem RecursiveExpressionInvariant.ofPlace
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {place : PlaceResolution}
    {targetExpression : Syntax.Expr}
    {semanticContext : SourceSemantics.Context} {fuel : Nat}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      final.inference.substitution)
    (success : Detail.inferPlaceFuel fuel inferenceContext targetExpression
      initial = .ok (place, final)) :
    RecursiveExpressionInvariant wholeContext finalized final
      semanticContext := by
  have properties := Detail.inferPlaceFuel_inferenceProperties
    invariant.ready signatureFormation functionsCanonical success
  refine {
    active := invariant.active.inferPlaceFuel success
    ready := properties.2.1
    bindersBelow := Detail.inferPlaceFuel_preserves_localBindersBelowNextLocal
      invariant.bindersBelow success
    nodesBelow := (Detail.inferPlaceFuel_occurrenceBoundExtends success
      ).nodesBelowNextOccurrence invariant.nodesBelow
    substitutionExtension
    signaturesEq := invariant.signaturesEq
    typeParametersEq := invariant.typeParametersEq
    declarationEq := invariant.declarationEq
    residual := invariant.residual
    solvedRequirementsEq := invariant.solvedRequirementsEq
    assumptionsMono := invariant.assumptionsMono
  }

/-- Fresh metavariable allocation changes no executable binders or
occurrences, but advances the type allocator and preserves readiness. -/
theorem RecursiveExpressionInvariant.fresh
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial : State} {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      initial.fresh.2.inference.substitution) :
    RecursiveExpressionInvariant wholeContext finalized initial.fresh.2
      semanticContext := {
  active := invariant.active.congr_localBinders (by rfl)
  ready := State.InferenceReady.fresh invariant.ready
  bindersBelow := State.fresh_preserves_localBindersBelowNextLocal initial
    invariant.bindersBelow
  nodesBelow := (State.OccurrenceBoundExtends.fresh initial
    ).nodesBelowNextOccurrence invariant.nodesBelow
  substitutionExtension
  signaturesEq := invariant.signaturesEq
  typeParametersEq := invariant.typeParametersEq
  declarationEq := invariant.declarationEq
  residual := invariant.residual
  solvedRequirementsEq := invariant.solvedRequirementsEq
  assumptionsMono := invariant.assumptionsMono
}

/-- A successful unification leaves executable binders untouched.  Its
readiness and occurrence bounds are preserved under the usual input-type
allocator bounds. -/
theorem RecursiveExpressionInvariant.unify
    {wholeContext : Frontend.SourceInference.Context}
    {finalized : Frontend.SourceInference.Result}
    {initial final : State} {left right : Ty}
    {semanticContext : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized initial
      semanticContext)
    (leftBelow : left.VariablesBelow initial.inference.next)
    (rightBelow : right.VariablesBelow initial.inference.next)
    (substitutionExtension : finalized.substitution.SemanticallyExtends
      final.inference.substitution)
    (success : Detail.unify initial left right = .ok final) :
    RecursiveExpressionInvariant wholeContext finalized final
      semanticContext := {
  active := invariant.active.unify success
  ready := Detail.unify_preserves_inferenceReady invariant.ready leftBelow
    rightBelow success
  bindersBelow := Detail.unify_preserves_localBindersBelowNextLocal
    invariant.bindersBelow success
  nodesBelow := (Detail.unify_occurrenceBoundExtends success
    ).nodesBelowNextOccurrence invariant.nodesBelow
  substitutionExtension
  signaturesEq := invariant.signaturesEq
  typeParametersEq := invariant.typeParametersEq
  declarationEq := invariant.declarationEq
  residual := invariant.residual
  solvedRequirementsEq := invariant.solvedRequirementsEq
  assumptionsMono := invariant.assumptionsMono
}

/-- The proof obligation for a source place is indexed by the exact parent
statement source.  Every mapping-key occurrence must have coverage in the
whole finalized graph. -/
def InferPlaceFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {targetExpression : Syntax.Expr}
    {initial final parentState evidenceState : State}
    {place : PlaceResolution} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context},
    Detail.inferPlaceFuel fuel inferenceContext targetExpression initial =
      .ok (place, final) →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
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
    finalized.substitution.SemanticallyExtends
      final.inference.substitution →
    TypingSourceExtends (final.toTypedSource roots)
      (parentState.toTypedSource roots) →
    TypingSourceExtends (parentState.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    final.integerPatterns ⊆ evidenceState.integerPatterns →
    final.integerLiterals ⊆ evidenceState.integerLiterals →
    final.requirements ⊆ evidenceState.requirements →
    (∀ key, .expression key ∈ place.references →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.expression key)) →
    SourcePlaceHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext (place.applySubstitution finalized.substitution)
      (finalized.substitution.apply place.type)

/-- The actual mapping-key call inside a successful indexed place starts in
an inference state satisfying the expression recursion invariant.  This
inversion follows the two fresh type variables and intervening unification,
so no arbitrary key-inference callback is needed. -/
theorem inferPlaceFuel_index_key_invariant
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {targetExpression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {initial final : State} {place : PlaceResolution}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (targetEq : targetExpression.value = .index base brackets key)
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final))
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (initialInvariant : RecursiveExpressionInvariant wholeContext finalized
      initial semanticContext)
    (finalSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        final.inference.substitution) :
    ∃ basePlace baseState expected keyInitial inferredKey,
      Detail.inferPlaceFuel fuel inferenceContext base initial =
        .ok (basePlace, baseState) ∧
      RecursiveExpressionInvariant wholeContext finalized baseState
        semanticContext ∧
      Detail.inferExprFuel fuel inferenceContext key (some expected)
        keyInitial = .ok (inferredKey, final) ∧
      RecursiveExpressionInvariant wholeContext finalized keyInitial
        semanticContext ∧
      expected.VariablesBelow keyInitial.inference.next ∧
      .expression inferredKey.id ∈ place.references := by
  unfold Detail.inferPlaceFuel at success
  simp only [targetEq, bind, Except.bind] at success
  cases baseResult : Detail.inferPlaceFuel fuel inferenceContext base
      initial with
  | error error => simp [baseResult] at success
  | ok basePair =>
      rcases basePair with ⟨basePlace, baseState⟩
      simp only [baseResult] at success
      let keyAllocation := baseState.fresh
      let valueAllocation := keyAllocation.2.fresh
      cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
          (.mapping keyAllocation.1 valueAllocation.1) with
      | error error =>
          simp [keyAllocation, valueAllocation, unifyResult] at success
      | ok unifiedState =>
          simp only [keyAllocation, valueAllocation, unifyResult] at success
          cases keyResult : Detail.inferExprFuel fuel inferenceContext key
              (some (unifiedState.resolve keyAllocation.1)) unifiedState with
          | error error =>
              simp [keyAllocation, keyResult] at success
          | ok keyPair =>
              rcases keyPair with ⟨inferredKey, keyState⟩
              simp only [keyAllocation, keyResult, pure, Pure.pure,
                Except.pure] at success
              injection success with resultEq
              injection resultEq with placeEq finalEq
              subst place
              subst final
              have baseProperties := Detail.inferPlaceFuel_inferenceProperties
                initialInvariant.ready signatureFormation functionsCanonical
                baseResult
              have keyProperties := Detail.fresh_eq_inferenceProperties
                baseProperties.2.1 (initial := baseState)
                  (type := keyAllocation.1) (next := keyAllocation.2) rfl
              have valueProperties := Detail.fresh_eq_inferenceProperties
                keyProperties.2.1 (initial := keyAllocation.2)
                  (type := valueAllocation.1) (next := valueAllocation.2) rfl
              have baseAtValue : basePlace.type.VariablesBelow
                  valueAllocation.2.inference.next :=
                baseProperties.2.2.weaken
                  (keyProperties.1.trans valueProperties.1).next_le
              have keyAtValue : keyAllocation.1.VariablesBelow
                  valueAllocation.2.inference.next :=
                keyProperties.2.2.weaken valueProperties.1.next_le
              have mappingBelow :
                  (Ty.mapping keyAllocation.1 valueAllocation.1
                    ).VariablesBelow valueAllocation.2.inference.next :=
                (Ty.variablesBelow_mapping_iff _ _ _).2
                  ⟨keyAtValue, valueProperties.2.2⟩
              have unifyProgress := Detail.unify_inferenceProgress
                valueProperties.2.1.solved baseAtValue mappingBelow
                unifyResult
              have unifiedReady := Detail.unify_preserves_inferenceReady
                valueProperties.2.1 baseAtValue mappingBelow unifyResult
              have keyAtUnified : keyAllocation.1.VariablesBelow
                  unifiedState.inference.next :=
                keyAtValue.weaken unifyProgress.next_le
              have expectedBelow :
                  (unifiedState.resolve keyAllocation.1).VariablesBelow
                    unifiedState.inference.next :=
                unifiedReady.solved.variablesBelow_apply keyAtUnified
              have keyExpressionProperties :=
                Detail.inferExprFuel_inferenceProperties unifiedReady
                  signatureFormation functionsCanonical (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    injection member with typeEq
                    subst expectedType
                    exact expectedBelow) keyResult
              have outerUnified : finalized.substitution.SemanticallyExtends
                  unifiedState.inference.substitution :=
                Substitution.SemanticallyExtends.trans
                  finalSubstitutionExtension
                  keyExpressionProperties.1.substitution_extends
              have baseToUnified :=
                (keyProperties.1.trans valueProperties.1).trans unifyProgress
              have outerBase : finalized.substitution.SemanticallyExtends
                  baseState.inference.substitution :=
                Substitution.SemanticallyExtends.trans outerUnified
                  baseToUnified.substitution_extends
              have baseInvariant : RecursiveExpressionInvariant wholeContext
                  finalized baseState semanticContext :=
                initialInvariant.ofPlace signatureFormation
                  functionsCanonical outerBase baseResult
              have outerKeyFresh : finalized.substitution.SemanticallyExtends
                  keyAllocation.2.inference.substitution := by
                simpa [keyAllocation, State.fresh] using outerBase
              have keyFreshInvariant : RecursiveExpressionInvariant
                  wholeContext finalized keyAllocation.2 semanticContext :=
                baseInvariant.fresh outerKeyFresh
              have outerValueFresh :
                  finalized.substitution.SemanticallyExtends
                    valueAllocation.2.inference.substitution := by
                simpa [valueAllocation, State.fresh] using outerKeyFresh
              have valueFreshInvariant : RecursiveExpressionInvariant
                  wholeContext finalized valueAllocation.2 semanticContext :=
                keyFreshInvariant.fresh outerValueFresh
              have unifiedInvariant : RecursiveExpressionInvariant
                  wholeContext finalized unifiedState semanticContext :=
                valueFreshInvariant.unify baseAtValue mappingBelow
                  outerUnified unifyResult
              refine ⟨basePlace, baseState,
                unifiedState.resolve keyAllocation.1, unifiedState,
                inferredKey, rfl, baseInvariant, keyResult,
                unifiedInvariant, expectedBelow, ?_⟩
              simp [PlaceResolution.references, PlaceProjection.references]

/-- Extending a place by one mapping index retains every reference of the
recursive base place. -/
theorem inferPlaceFuel_index_base_references_subset
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {targetExpression base key : Syntax.Expr}
    {brackets : Syntax.SourceSpan}
    {initial final baseState : State}
    {place basePlace : PlaceResolution}
    (targetEq : targetExpression.value = .index base brackets key)
    (baseSuccess : Detail.inferPlaceFuel fuel inferenceContext base initial =
      .ok (basePlace, baseState))
    (success : Detail.inferPlaceFuel (fuel + 1) inferenceContext
      targetExpression initial = .ok (place, final)) :
    basePlace.references ⊆ place.references := by
  unfold Detail.inferPlaceFuel at success
  simp only [targetEq, baseSuccess, bind, Except.bind] at success
  let keyAllocation := baseState.fresh
  let valueAllocation := keyAllocation.2.fresh
  cases unifyResult : Detail.unify valueAllocation.2 basePlace.type
      (.mapping keyAllocation.1 valueAllocation.1) with
  | error error =>
      simp [keyAllocation, valueAllocation, unifyResult] at success
  | ok unifiedState =>
      simp only [keyAllocation, valueAllocation, unifyResult] at success
      cases keyResult : Detail.inferExprFuel fuel inferenceContext key
          (some (unifiedState.resolve keyAllocation.1)) unifiedState with
      | error error =>
          simp [keyAllocation, keyResult] at success
      | ok keyPair =>
          rcases keyPair with ⟨inferredKey, keyState⟩
          simp only [keyAllocation, keyResult, pure, Pure.pure,
            Except.pure] at success
          injection success with resultEq
          injection resultEq with placeEq finalEq
          subst place
          intro reference member
          change reference ∈
            (basePlace.projections ++ [PlaceProjection.index inferredKey.id]).flatMap
              PlaceProjection.references
          rw [List.flatMap_append]
          exact List.mem_append.mpr (Or.inl member)

end Solcore.SourceSemantics.SourceInferenceSoundness
