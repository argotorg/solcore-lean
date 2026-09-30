import Solcore.SourceSemantics.SourceInferencePlaceRecursiveSoundness

/-!
Actual-success semantic resources for assignment.  A place is inferred first;
the value starts either in that place state or in its successful `Word`
unification state.  Both routes preserve the recursive expression invariant.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The actual place and RHS of an assignment each start with the recursive
invariants needed by their scoped soundness theorems. -/
theorem inferAssignedValueFuel_children_invariants
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial final : State}
    {assignment : AssignmentResolution}
    {inferred : InferredExpression}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferred, final))
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
    ∃ place placeState expected valueInitial,
      Detail.inferPlaceFuel fuel inferenceContext targetExpression initial =
        .ok (place, placeState) ∧
      RecursiveExpressionInvariant wholeContext finalized placeState
        semanticContext ∧
      Detail.inferExprFuel fuel inferenceContext value (some expected)
        valueInitial = .ok (inferred, final) ∧
      RecursiveExpressionInvariant wholeContext finalized valueInitial
        semanticContext ∧
      expected.VariablesBelow valueInitial.inference.next ∧
      assignment.target.references = place.references ∧
      assignment.target = { place with type := final.resolve place.type } := by
  unfold Detail.inferAssignedValueFuel at success
  cases placeResult : Detail.inferPlaceFuel fuel inferenceContext
      targetExpression initial with
  | error error => simp [placeResult, bind, Except.bind] at success
  | ok placePair =>
      rcases placePair with ⟨place, placeState⟩
      simp only [placeResult, bind, Except.bind, Prod.eta] at success
      have placeProperties := Detail.inferPlaceFuel_inferenceProperties
        initialInvariant.ready signatureFormation functionsCanonical
        placeResult
      have placeTypeBelow : place.type.VariablesBelow
          placeState.inference.next := placeProperties.2.2
      have finishNonEqual
          (tailSuccess :
            (do
              let fittedState ← Detail.unify placeState place.type .word
              let (inferredValue, finalState) ←
                Detail.inferExprFuel fuel inferenceContext value (some .word)
                  fittedState
              pure (({ target := { place with
                type := finalState.resolve place.type } } :
                  AssignmentResolution), inferredValue, finalState)) =
              .ok (assignment, inferred, final)) :
          ∃ actualPlace actualPlaceState expected valueInitial,
            (Except.ok (place, placeState) : Except
              Frontend.SourceInference.Error (PlaceResolution × State)) =
              .ok (actualPlace, actualPlaceState) ∧
            RecursiveExpressionInvariant wholeContext finalized
              actualPlaceState semanticContext ∧
            Detail.inferExprFuel fuel inferenceContext value (some expected)
              valueInitial = .ok (inferred, final) ∧
            RecursiveExpressionInvariant wholeContext finalized valueInitial
              semanticContext ∧
            expected.VariablesBelow valueInitial.inference.next ∧
            assignment.target.references = actualPlace.references ∧
            assignment.target =
              { actualPlace with type := final.resolve actualPlace.type } := by
        cases unifyResult : Detail.unify placeState place.type .word with
        | error error =>
            simp [unifyResult, bind, Except.bind] at tailSuccess
        | ok fittedState =>
            simp only [unifyResult, bind, Except.bind] at tailSuccess
            cases valueResult : Detail.inferExprFuel fuel inferenceContext
                value (some .word) fittedState with
            | error error => simp [valueResult] at tailSuccess
            | ok valuePair =>
                rcases valuePair with ⟨inferredValue, finalState⟩
                simp only [valueResult, pure, Pure.pure, Except.pure]
                  at tailSuccess
                injection tailSuccess with resultEq
                injection resultEq with assignmentEq valueEq
                injection valueEq with inferredEq finalEq
                subst assignment
                subst inferred
                subst final
                have fittedReady : fittedState.InferenceReady :=
                  Detail.unify_preserves_inferenceReady
                    placeProperties.2.1 placeTypeBelow
                    (Ty.variablesBelow_constructor _ _)
                    unifyResult
                have valueProperties := Detail.inferExprFuel_inferenceProperties
                  fittedReady signatureFormation functionsCanonical (by
                    intro expectedType member
                    simp only [Option.mem_def] at member
                    cases member
                    exact Ty.variablesBelow_constructor _ _) valueResult
                have outerFitted :
                    finalized.substitution.SemanticallyExtends
                      fittedState.inference.substitution :=
                  Substitution.SemanticallyExtends.trans
                    finalSubstitutionExtension
                    valueProperties.1.substitution_extends
                have unifyProgress := Detail.unify_inferenceProgress
                  placeProperties.2.1.solved placeTypeBelow
                  (Ty.variablesBelow_constructor _ _)
                  unifyResult
                have outerPlace : finalized.substitution.SemanticallyExtends
                    placeState.inference.substitution :=
                  Substitution.SemanticallyExtends.trans outerFitted
                    unifyProgress.substitution_extends
                have placeInvariant : RecursiveExpressionInvariant
                    wholeContext finalized placeState semanticContext :=
                  initialInvariant.ofPlace signatureFormation
                    functionsCanonical outerPlace placeResult
                have fittedInvariant : RecursiveExpressionInvariant
                    wholeContext finalized fittedState semanticContext :=
                  placeInvariant.unify placeTypeBelow
                    (Ty.variablesBelow_constructor _ _)
                    outerFitted unifyResult
                exact ⟨place, placeState, .word, fittedState, rfl,
                  placeInvariant, valueResult, fittedInvariant,
                  Ty.variablesBelow_constructor _ _, rfl, rfl⟩
      cases operator with
      | equal =>
          simp only [pure, Pure.pure, Except.pure] at success
          cases valueResult : Detail.inferExprFuel fuel inferenceContext value
              (some (placeState.resolve place.type)) placeState with
          | error error => simp [valueResult] at success
          | ok valuePair =>
              rcases valuePair with ⟨inferredValue, finalState⟩
              simp only [valueResult] at success
              injection success with resultEq
              injection resultEq with assignmentEq valueEq
              injection valueEq with inferredEq finalEq
              subst assignment
              subst inferred
              subst final
              have expectedBelow :
                  (placeState.resolve place.type).VariablesBelow
                    placeState.inference.next :=
                placeProperties.2.1.solved.variablesBelow_apply placeTypeBelow
              have valueProperties := Detail.inferExprFuel_inferenceProperties
                placeProperties.2.1 signatureFormation functionsCanonical (by
                  intro expectedType member
                  simp only [Option.mem_def] at member
                  cases member
                  exact expectedBelow) valueResult
              have outerPlace : finalized.substitution.SemanticallyExtends
                  placeState.inference.substitution :=
                Substitution.SemanticallyExtends.trans
                  finalSubstitutionExtension
                  valueProperties.1.substitution_extends
              have placeInvariant : RecursiveExpressionInvariant wholeContext
                  finalized placeState semanticContext :=
                initialInvariant.ofPlace signatureFormation
                  functionsCanonical outerPlace placeResult
              exact ⟨place, placeState, placeState.resolve place.type,
                placeState, rfl, placeInvariant, valueResult, placeInvariant,
                expectedBelow, rfl, rfl⟩
      | add => exact finishNonEqual success
      | subtract => exact finishNonEqual success
      | multiply => exact finishNonEqual success
      | divide => exact finishNonEqual success
      | modulo => exact finishNonEqual success
      | bitAnd => exact finishNonEqual success
      | bitXor => exact finishNonEqual success
      | bitOr => exact finishNonEqual success

/-- The actual inferred place and RHS are typed in one enclosing statement
source.  The place is inferred before the RHS; its recorded type is finally
resolved, but final semantic substitution makes that update observationally
identical to the original place type. -/
theorem inferAssignedValueFuel_children_scopedSound
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial assignmentState parentState evidenceState : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferred, assignmentState))
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ signature ∈
      inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveExpressionInvariant wholeContext finalized
      initial semanticContext)
    (assignmentSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        assignmentState.inference.substitution)
    (assignmentToParent : TypingSourceExtends
      (assignmentState.toTypedSource roots)
      (parentState.toTypedSource roots))
    (parentToEvidence : TypingSourceExtends
      (parentState.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (parentToFinal : TypingSourceExtends
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (assignmentPatternsSubset : assignmentState.integerPatterns ⊆
      evidenceState.integerPatterns)
    (assignmentLiteralsSubset : assignmentState.integerLiterals ⊆
      evidenceState.integerLiterals)
    (assignmentRequirementsSubset : assignmentState.requirements ⊆
      evidenceState.requirements)
    (keysCovered : ∀ key, .expression key ∈ assignment.references →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.expression key))
    (rhsCovered : TemplateScopeCovered finalized.typedSource semanticContext
      (.expression inferred.id))
    (placeSound : InferPlaceFuelScopedSoundness fuel)
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    SourcePlaceHasType
        ((parentState.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext
        (assignment.target.applySubstitution finalized.substitution)
        (finalized.substitution.apply assignment.target.type) ∧
      ExpressionHasType
        ((parentState.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferred.id
        (finalized.substitution.apply inferred.type) := by
  obtain ⟨place, placeState, expected, valueInitial, placeSuccess,
      placeInvariant, valueSuccess, valueInvariant, expectedBelow,
      referencesEq, targetEq⟩ :=
    inferAssignedValueFuel_children_invariants success signatureFormation
      functionsCanonical initialInvariant assignmentSubstitutionExtension
  obtain ⟨actualPlace, actualPlaceState, actualPlaceSuccess, _,
      placeToAssignment, placeLiteralsSubset, placePatternsSubset,
      placeRequirementsSubset⟩ :=
    inferAssignedValueFuel_success_place_state_provenance success
      initialInvariant.nodesBelow roots
  rw [placeSuccess] at actualPlaceSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualPlaceSuccess).symm
  have placeToParent : TypingSourceExtends
      (placeState.toTypedSource roots) (parentState.toTypedSource roots) :=
    placeToAssignment.trans assignmentToParent
  have placeKeysCovered : ∀ key,
      .expression key ∈ place.references →
        TemplateScopeCovered finalized.typedSource semanticContext
          (.expression key) := by
    intro key member
    exact keysCovered key (by simpa [AssignmentResolution.references,
      referencesEq] using member)
  have placeTyped : SourcePlaceHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext (place.applySubstitution finalized.substitution)
      (finalized.substitution.apply place.type) :=
    placeSound placeSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters initialInvariant placeInvariant.substitutionExtension
      placeToParent parentToEvidence
      (List.Subset.trans placePatternsSubset assignmentPatternsSubset)
      (List.Subset.trans placeLiteralsSubset assignmentLiteralsSubset)
      (List.Subset.trans placeRequirementsSubset
        assignmentRequirementsSubset) placeKeysCovered
  have targetTypeEq : finalized.substitution.apply assignment.target.type =
      finalized.substitution.apply place.type := by
    rw [targetEq]
    simpa [State.resolve, InferState.resolve] using
      assignmentSubstitutionExtension place.type
  have targetSubstEq :
      assignment.target.applySubstitution finalized.substitution =
        place.applySubstitution finalized.substitution := by
    rw [targetEq]
    have storedEq : finalized.substitution.apply
        (assignmentState.resolve place.type) =
        finalized.substitution.apply place.type := by
      simpa [State.resolve, InferState.resolve] using
        assignmentSubstitutionExtension place.type
    simpa [PlaceResolution.applySubstitution] using
      congrArg (fun type => ({ place with type := type } : PlaceResolution))
        storedEq
  have valueTyped : ExpressionHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound valueSuccess resources assignmentSubstitutionExtension
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters valueInvariant
      (by intro candidate member
          simp only [Option.mem_def] at member
          cases member
          exact expectedBelow)
      (assignmentToParent.applySubstitution finalized.substitution)
      parentToFinal (assignmentToParent.trans parentToEvidence)
      assignmentPatternsSubset assignmentLiteralsSubset
      assignmentRequirementsSubset rhsCovered
  exact ⟨by simpa only [targetSubstEq, targetTypeEq] using placeTyped,
    valueTyped⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
