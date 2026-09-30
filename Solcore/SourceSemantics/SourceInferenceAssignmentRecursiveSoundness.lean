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

end Solcore.SourceSemantics.SourceInferenceSoundness
