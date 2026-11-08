import Solcore.SourceSemantics.Internal.Inference.ExpressionRetained
import Solcore.SourceSemantics.Internal.Privacy.Active
import Solcore.SourceSemantics.Internal.Inference.LedgerSoundness
import Solcore.SourceSemantics.Internal.Inference.CaptureOrigins
import Solcore.SourceSemantics.Internal.Inference.ExpressionLedgers
import Solcore.SourceSemantics.Internal.Inference.StatementResources
import Solcore.SourceSemantics.Internal.Inference.StatementControl

/-!
# The statement dispatcher

The one-statement recursive dispatcher, with assignment and the operational state of generalized
checking.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceAssignmentRecursiveSoundness
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
      | shiftLeft => exact finishNonEqual success
      | shiftRight => exact finishNonEqual success
      | uncheckedAdd => exact finishNonEqual success
      | uncheckedSubtract => exact finishNonEqual success
      | uncheckedMultiply => exact finishNonEqual success

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
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceAssignmentStatementBridge
/-!
The assignment branches of statement inference delegate to place and
expression inference.  This bridge discharges the branch-local child-typing
callback with the *actual* successful assignment traversal, in the final
parent statement source.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The value-assignment statement is well typed when the actual delegated
place and expression traversals satisfy their recursive soundness contracts. -/
theorem inferStatementFuel_success_assignValue_recursive_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (statementEq : statement.value =
      .assignValue targetExpression operator value)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
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
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (ready : initial.InferenceReady)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial finalized.substitution
      semanticContext)
    (allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext)
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (parentToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (placeSound : InferPlaceFuelScopedSoundness fuel)
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ActiveLocalContextInvariant result.state finalized.substitution
        semanticContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        control semanticContext result.id semanticContext {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  apply inferStatementFuel_success_assignValue_bounded_scoped
    statementEq allocationEq success ready initialBelow signatureFormation
    functionsCanonical invariant outerExtension roots parentCovered closed
    resultExtension resultIntegerPatternsSubset resultIntegerLiteralsSubset
    resultRequirementsSubset
  intro assignment inferred assignmentState assignmentSuccess
    _assignmentExtension assignmentPatternsSubset assignmentLiteralsSubset
    assignmentRequirementsSubset keysCovered rhsCovered
  obtain ⟨actualAssignment, actualInferred, actualState, actualSuccess,
      resultEq, _⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq
      success roots
  rw [assignmentSuccess] at actualSuccess
  obtain ⟨rfl, rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have assignmentToParent : TypingSourceExtends
      (assignmentState.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    constructor
    · rfl
    · exact State.recordNode_nodesPrefix assignmentState _
  have assignmentSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        assignmentState.inference.substitution := by
    rw [resultEq] at outerExtension
    simpa [State.recordNode] using outerExtension
  exact inferAssignedValueFuel_children_scopedSound assignmentSuccess
    resources signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    allocatedInvariant assignmentSubstitutionExtension assignmentToParent
    parentToEvidence resultExtension assignmentPatternsSubset
    assignmentLiteralsSubset assignmentRequirementsSubset keysCovered
    rhsCovered placeSound expressionSound

/-- Bit-not assignment traverses an actual place, then unifies its type with
`Word`.  The place's indexed keys are typed before that final unification. -/
theorem inferStatementFuel_success_assignBitNot_recursive_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr}
    {operatorSpan : Syntax.SourceSpan}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    {control : ControlContext}
    (statementEq : statement.value =
      .assignBitNot targetExpression operatorSpan)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
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
    (functionsCanonical : ∀ signature ∈ inferenceContext.signatures.functions,
      signature.scheme.body = .function
        (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (invariant : ActiveLocalContextInvariant initial finalized.substitution
      semanticContext)
    (allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext)
    (outerExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (closed : OccurrenceGraphClosed finalized.typedSource)
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (parentToEvidence : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (resultIntegerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (resultIntegerLiteralsSubset :
      result.state.integerLiterals ⊆ evidenceState.integerLiterals)
    (resultRequirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (placeSound : InferPlaceFuelScopedSoundness fuel) :
    ActiveLocalContextInvariant result.state finalized.substitution
        semanticContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        control semanticContext result.id semanticContext {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result {
          type := .unit
          hasValue := false
          sawReturn := false
          control := .ordinary .unit
        } := by
  apply inferStatementFuel_success_assignBitNot_bounded_scoped
    statementEq allocationEq success initialBelow invariant outerExtension
    roots parentCovered closed resultExtension resultIntegerPatternsSubset
    resultIntegerLiteralsSubset resultRequirementsSubset
  intro place placeState placeSuccess _placeExtension placePatternsSubset
    placeLiteralsSubset placeRequirementsSubset keysCovered
  obtain ⟨actualPlace, actualState, unified, actualSuccess,
      unifySuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq
      success roots
  rw [placeSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have placeToUnified : TypingSourceExtends
      (placeState.toTypedSource roots) (unified.toTypedSource roots) := by
    constructor
    · have headerEq := Detail.unify_state_header unifySuccess
      have ownerEq := congrArg State.Header.owner headerEq
      simpa [State.toTypedSource, State.header] using ownerEq
    · have nodesEq := (Detail.unify_occurrenceState_eq unifySuccess).1
      change placeState.nodes <+: unified.nodes
      rw [nodesEq]
      exact List.prefix_rfl
  have unifiedToParent : TypingSourceExtends
      (unified.toTypedSource roots)
      (result.state.toTypedSource roots) := by
    rw [resultEq]
    constructor
    · rfl
    · exact State.recordNode_nodesPrefix unified _
  have placeToParent := placeToUnified.trans unifiedToParent
  have unifiedSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        unified.inference.substitution := by
    rw [resultEq] at outerExtension
    simpa [State.recordNode] using outerExtension
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    placeSuccess
  have unifyProgress := Detail.unify_inferenceProgress
    placeProperties.2.1.solved placeProperties.2.2
    (Ty.variablesBelow_constructor _ _) unifySuccess
  have placeSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        placeState.inference.substitution :=
    Substitution.SemanticallyExtends.trans unifiedSubstitutionExtension
      unifyProgress.substitution_extends
  exact placeSound placeSuccess resources signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters allocatedInvariant placeSubstitutionExtension
    placeToParent parentToEvidence placePatternsSubset placeLiteralsSubset
    placeRequirementsSubset keysCovered

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedActualStateInvariant
/-! Operational state for generalized recursive checking. Privacy and actual
template rows replace the restriction to monomorphic source binders. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

structure GeneralizedActualStateInvariant (state : State) (evidenceSource : TypedSource) : Prop where
  ledger : ∃ pending, RecursiveLedgerInvariant state pending
  origins : ActiveBinderCaptureOrigins state evidenceSource
  quantifiersBelow : ActiveQuantifiersBelowNext state
  privacy : ActiveQuantifiersPrivate state
  backed : LiveTemplatesBacked state

namespace GeneralizedActualStateInvariant

theorem requirements {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    state.RequirementsWellFormed := by
  obtain ⟨_, ledger⟩ := invariant.ledger
  exact ledger.requirements

theorem initial (owner : Resolved.DeclarationId) (locals : Environment)
    (comptime : List Bool) (evidenceSource : TypedSource)
    (monomorphic : ∀ entry ∈ locals, entry.2.quantified = []) :
    GeneralizedActualStateInvariant (State.initial owner locals comptime) evidenceSource :=
  ⟨⟨[], RecursiveLedgerInvariant.initial owner locals comptime⟩,
    activeBinderCaptureOrigins_initial_mono owner locals comptime evidenceSource monomorphic,
    activeQuantifiersBelowNext_initial_mono owner locals comptime monomorphic,
    ActiveQuantifiersPrivate.initial owner locals comptime monomorphic,
    LiveTemplatesBacked.initial owner locals comptime⟩

private theorem privacy_congr {before after : State}
    (privacy : ActiveQuantifiersPrivate before)
    (binders : after.localBinders = before.localBinders)
    (substitution : after.inference.substitution = before.inference.substitution) :
    ActiveQuantifiersPrivate after := by
  intro binder member
  exact (privacy binder (binders ▸ member)).transport binders
    (.of_substitution_eq substitution)

theorem allocateStatementId {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateStatementId.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateStatementId⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem allocateExpressionId {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateExpressionId.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateExpressionId⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem fresh {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.fresh.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.fresh⟩, invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_succ _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

theorem withLocals {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) (locals : Environment) :
    GeneralizedActualStateInvariant (state.withLocals locals) source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ⟨ledger.requirements,
    ⟨ledger.templates.classified, ledger.templates.unique, ledger.templates.covered⟩⟩⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    privacy_congr invariant.privacy rfl rfl, invariant.backed.congr rfl rfl rfl⟩

/-- The actual expression call preserves every active scheme. Its optional
expected type must avoid those existing scheme quantifiers at child entry. -/
theorem ofExpression
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {expected : Option Ty} {initial final : State} {value : InferredExpression}
    {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (expectedSafe : ∀ binder ∈ initial.localBinders, ∀ type ∈ expected,
      Safe binder.scheme.quantified initial type)
    (accepted : Detail.inferExprFuel fuel context expression expected initial = .ok (value, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have properties := Detail.inferExprFuel_inferenceProperties ready formation canonical expectedBelow accepted
  have binders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  change final.localBinders = initial.localBinders at binders
  refine ⟨⟨pending, (actualLedgerFamily fuel).expression accepted ledger⟩,
    invariant.origins.inferExprFuel accepted,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow binders properties.1.next_le,
    ?_, invariant.backed.inferExprFuel ready formation canonical expectedBelow accepted⟩
  intro binder member
  have entering : binder ∈ initial.localBinders := binders ▸ member
  exact (inferExprFuel_private binder.scheme.quantified fuel context expression expected initial
    ready ledger.requirements (invariant.quantifiersBelow binder entering)
    (invariant.privacy binder entering) catalog formation canonical expectedBelow
    (expectedSafe binder entering) _ accepted).2.2.1

/-- At an original function statement, the actual finalizer provides the
capture checks needed for newly generalized binders. The original return type
is closed; lambda return metavariables need a separate continuation. -/
theorem ofStatement
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {expected : Ty} {initial : State} {result : Detail.StatementResult}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expectedClosed : expected.VariablesBelow 0)
    (retained : result.state.nodes <+: evidenceState.nodes)
    (sourceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution)
    (accepted : Detail.inferStatementFuel fuel context statement expected initial = .ok result) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have expectedBelow := expectedClosed.weaken (Nat.zero_le initial.inference.next)
  exact ⟨⟨pending, (actualLedgerFamily fuel).statements.statement accepted ledger⟩,
    inferStatementFuel_captureOrigins accepted invariant.origins sourceExtension,
    activeQuantifiersBelowNext_inferStatementFuel invariant.quantifiersBelow ready
      formation canonical expectedBelow accepted,
    invariant.privacy.inferStatementFuel resources ready ledger.requirements invariant.quantifiersBelow
      catalog formation canonical expectedClosed invariant.backed invariant.origins retained extension accepted,
    invariant.backed.inferStatementFuel ready formation canonical expectedBelow accepted⟩

end GeneralizedActualStateInvariant
end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedInitializerState
/-! The actual initialized declaration does not inspect its enclosing return
type. Its state transition therefore supports generalized lambda bodies too. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Reconstruct the exact executed declaration for any enclosing return type.
Both annotation branches reuse the same child and completed result. -/
theorem initializedReceipt_accepted
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (expectedReturn : Ty) :
    Detail.inferStatementFuel (fuel + 1) context statement expectedReturn initial = .ok result := by
  rcases receipt with ⟨name, initializer, annotation, expected, annotationAccepted,
    form, value, ready, child, completed⟩
  cases annotationAccepted with
  | none =>
    simp [Detail.inferStatementFuel, form, child, completed,
      LocalLetRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    rfl
  | some annotationAccepted =>
    simp [Detail.inferStatementFuel, form, annotationAccepted, child, completed,
      LocalLetRequirementTiming.finish, bind, Except.bind, pure, Pure.pure, Except.pure]
    rfl

/-- This exact initializer preserves the generalized operational state without
a restriction on the enclosing function or lambda's expected return type. -/
theorem GeneralizedActualStateInvariant.ofInitializer
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (retained : result.state.nodes <+: evidenceState.nodes)
    (sourceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  exact invariant.ofStatement resources ready catalog formation canonical
    (show Ty.unit.VariablesBelow 0 from by simp [Ty.VariablesBelow, Ty.unit, Ty.freeVariables])
    retained sourceExtension extension (initializedReceipt_accepted receipt .unit)

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceGeneralizedPatternState
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

theorem GeneralizedActualStateInvariant.allocateHiddenLocal
    {state : State} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant state source) :
    GeneralizedActualStateInvariant state.allocateHiddenLocal.2 source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending, ledger.allocateHiddenLocal⟩,
    invariant.origins.congr_localBinders rfl,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow rfl (Nat.le_refl _),
    invariant.privacy.congr rfl rfl,
    invariant.backed.congr rfl rfl rfl⟩

theorem GeneralizedActualStateInvariant.ofPattern
    {fuel : Nat} {context : SourceInference.Context} {pattern : Syntax.Pattern}
    {expected : Ty} {initial final : State} {inferred : TypedMatchPattern} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (expectedBelow : expected.VariablesBelow initial.inference.next)
    (expectedSafe : Safe (activeSchemeQuantifiers initial) initial expected)
    (accepted : Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final)) :
    GeneralizedActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have active := inferMatchPatternFuel_active_state ready expectedBelow formation
    invariant.quantifiersBelow invariant.privacy invariant.backed invariant.origins expectedSafe accepted
  exact ⟨⟨pending, inferMatchPatternFuel_ledgerPreservation accepted ledger⟩,
    active.2.2.2, active.2.1, active.1, active.2.2.1⟩

/-- The scrutinee's actual inference supplies privacy for its returned type
with respect to every surviving active scheme. -/
theorem GeneralizedActualStateInvariant.expression_result_private
    {fuel : Nat} {context : SourceInference.Context} {expression : Syntax.Expr}
    {initial final : State} {inferred : InferredExpression} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (accepted : Detail.inferExprFuel fuel context expression none initial = .ok (inferred, final)) :
    Safe (activeSchemeQuantifiers final) final inferred.type := by
  have privacy := inferExprFuel_private (activeSchemeQuantifiers initial) fuel context expression none initial
    ready invariant.requirements (activeSchemeQuantifiers_below_next invariant.quantifiersBelow)
    invariant.privacy.all_live catalog formation canonical (by simp) (by simp) _ accepted
  have binders : final.localBinders = initial.localBinders :=
    congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq accepted)
  simpa only [activeSchemeQuantifiers, binders] using privacy.2.1

/-- Pattern entry after a real scrutinee call derives its expected-type
privacy from that call, then carries the full generalized operational state. -/
theorem GeneralizedActualStateInvariant.pattern_after_expression
    {expressionFuel patternFuel : Nat} {context : SourceInference.Context}
    {expression : Syntax.Expr} {patternSource : Syntax.Pattern}
    {initial scrutineeState final : State} {scrutinee : InferredExpression}
    {pattern : TypedMatchPattern} {source : TypedSource}
    (invariant : GeneralizedActualStateInvariant initial source)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (expressionAccepted : Detail.inferExprFuel expressionFuel context expression none initial =
      .ok (scrutinee, scrutineeState))
    (patternAccepted : Detail.inferMatchPatternFuel patternFuel context patternSource scrutinee.type
      scrutineeState = .ok (pattern, final)) :
    GeneralizedActualStateInvariant final source := by
  have properties := Detail.inferExprFuel_inferenceProperties ready formation canonical
    (by simp) expressionAccepted
  have after := invariant.ofExpression ready catalog formation canonical (by simp) (by simp) expressionAccepted
  exact after.ofPattern properties.2.1 formation properties.2.2
    (invariant.expression_result_private ready catalog formation canonical expressionAccepted) patternAccepted

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceRetainedInitializerState
/-! An initialized binder needs its own final source origin. Unrelated
expression nodes may change during later coercion selection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem ProtectedVariables

/-- Finalizer privacy uses the retained allocated binder and the actual older
template rows. It does not require a prefix of the whole node table. -/
theorem initializedBinder_privacy
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (backed : LiveTemplatesBacked initial)
    (origins : ActiveBinderCaptureOrigins initial (evidenceState.toTypedSource roots))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    LiveBindersSafe receipt.binding.1.scheme.quantified result.state := by
  have readyOrigins := origins.congr_localBinders receipt.ready_binders
  have templates := ProtectedVariables.LocalLetRequirementTiming.Receipt.templates_before
    receipt backed ready wellFormed formation canonical
  have readyExtension : finalized.substitution.SemanticallyExtends receipt.ready.inference.substitution := by
    rwa [receipt.inference_eq] at extension
  have live := allocate_generalized_live_from_finalizer resources initial.nextRequirement
    (receipt.ready.resolve receipt.value.type) receipt.name.value (some receipt.name.span) false
    (readyOrigins.withLocals receipt.locals) readyExtension templates retained
  exact live.transport
    (congrArg (fun result : Detail.StatementResult => result.state.localBinders) receipt.completed)
    (.of_substitution_eq
      (congrArg (fun result : Detail.StatementResult => result.state.inference.substitution) receipt.completed))

/-- The exact initialized binder's retained source origin suffices to carry
all generalized operational fields through its real completed statement. -/
theorem GeneralizedActualStateInvariant.ofRetainedInitializer
    {wholeContext : SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId} {finalized : SourceInference.Result}
    {fuel : Nat} {context : SourceInference.Context} {statement : Syntax.Statement}
    {initial : State} {result : Detail.StatementResult}
    (invariant : GeneralizedActualStateInvariant initial (evidenceState.toTypedSource roots))
    (receipt : LocalLetRequirementTiming.Receipt fuel context statement initial result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized)
    (ready : initial.InferenceReady)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (formation : ProgramSignatureFormationValidated context.signatures)
    (canonical : ∀ signature ∈ context.signatures.functions,
      signature.scheme.body = .function (Ty.productMany signature.parameterTypes)
        (Ty.productMany signature.returnTypes))
    (retained : receipt.binding.1 ∈ (evidenceState.toTypedSource roots).initializedLetBinders)
    (extension : finalized.substitution.SemanticallyExtends result.state.inference.substitution) :
    GeneralizedActualStateInvariant result.state (evidenceState.toTypedSource roots) := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  have accepted := initializedReceipt_accepted receipt .unit
  have closed : Ty.unit.VariablesBelow 0 := by
    simp [Ty.VariablesBelow, Ty.unit, Ty.freeVariables]
  have readyOrigins := invariant.origins.congr_localBinders receipt.ready_binders
  have allocatedOrigins : ActiveBinderCaptureOrigins receipt.binding.2 (evidenceState.toTypedSource roots) :=
    (readyOrigins.withLocals receipt.locals).allocateBinder rfl (.inr retained)
  refine ⟨⟨pending, (actualLedgerFamily (fuel + 1)).statements.statement accepted ledger⟩,
    allocatedOrigins.congr_localBinders
      (congrArg (fun result : Detail.StatementResult => result.state.localBinders) receipt.completed),
    activeQuantifiersBelowNext_inferStatementFuel invariant.quantifiersBelow ready formation canonical
      (closed.weaken (Nat.zero_le _)) accepted,
    ?_, invariant.backed.inferStatementFuel ready formation canonical (closed.weaken (Nat.zero_le _)) accepted⟩
  intro binder member
  rw [receipt.result_binders] at member
  rcases List.mem_cons.mp member with rfl | entering
  · exact initializedBinder_privacy resources receipt ready ledger.requirements formation canonical
      invariant.backed invariant.origins retained extension
  · exact (inferStatementFuel_private binder.scheme.quantified (fuel + 1) context statement .unit initial
      ready ledger.requirements (invariant.quantifiersBelow binder entering)
      (invariant.privacy binder entering) catalog formation canonical
      (closed.weaken (Nat.zero_le _)) (safe_closed _ _ closed) result accepted).2.2.1

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceStatementRecursiveDispatcher
/-!
The one-statement recursive soundness dispatcher.  Let and match forms are
kept as explicit, actual-success obligations while their specialized
certificate and pattern proofs are completed.  Every other accepted form is
closed here from the smaller-fuel expression, statement-list, header-item,
and place soundness theorems.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The only statement forms whose semantic branch proofs still require a
specialized certificate or match-pattern invariant. -/
def DeferredStatementForm (statement : Syntax.Statement) : Prop :=
  match statement.value with
  | .letDecl _ _ _ => True
  | .matchWith _ _ => True
  | _ => False

/-- A scoped soundness contract restricted to the two deferred syntax forms.
Its success premise is still the actual parent statement computation. -/
def InferDeferredStatementFuelScopedSoundness (fuel : Nat) : Prop :=
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context},
    DeferredStatementForm statement →
    Detail.inferStatementFuel fuel inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    inferenceContext.signatures = wholeContext.signatures →
    inferenceContext.scope.genericOwner = wholeContext.scope.genericOwner →
    inferenceContext.typeParameters = wholeContext.typeParameters →
    inferenceContext.assumptions = wholeContext.assumptions →
    ProgramSignatureFormationValidated inferenceContext.signatures →
    (∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes)) →
    SignatureCatalogWellFormed inferenceContext.signatures →
    SignatureParametersWellFormed inferenceContext.scope.genericOwner
      inferenceContext.typeParameters →
    RecursiveStatementInvariant wholeContext expectedReturn finalized
      initial semanticContext →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource →
    TypingSourceExtends semanticSource finalized.typedSource →
    TypingSourceExtends (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts

/-- Every non-let, non-match statement branch closes from actual smaller-fuel
child soundness.  The deferred premise is used only when the successful
statement's constructor is a local declaration or a match. -/
theorem inferStatementFuelScopedSoundness_step_of_deferred
    {fuel : Nat}
    (expressionSound : InferExprFuelScopedSoundness fuel)
    (statementsSound : InferStatementsFuelScopedSoundness fuel)
    (forItemsSound : InferForItemsFuelScopedSoundness fuel)
    (placeSound : InferPlaceFuelScopedSoundness fuel)
    (deferred : InferDeferredStatementFuelScopedSoundness (fuel + 1)) :
    InferStatementFuelScopedSoundness (fuel + 1) := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement
    initial result evidenceState roots finalized semanticSource
    semanticContext success resources signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters initialInvariant resultSubstitutionExtension
    resultSemanticExtension semanticCoverageExtension rawResultExtension
    integerPatternsSubset integerLiteralsSubset requirementsSubset
    parentCovered
  by_cases isDeferred : DeferredStatementForm statement
  · exact deferred isDeferred success resources signaturesEq ownerEq
      parametersEq assumptionsEq signatureFormation functionsCanonical
      catalog signatureParameters initialInvariant
      resultSubstitutionExtension resultSemanticExtension
      semanticCoverageExtension rawResultExtension integerPatternsSubset
      integerLiteralsSubset requirementsSubset parentCovered
  have notLet : ∀ name sourceType initializer,
      statement.value ≠ .letDecl name sourceType initializer := by
    intro name sourceType initializer statementEq
    exact isDeferred (by simp [DeferredStatementForm, statementEq])
  have notMatch : ∀ scrutinees arms,
      statement.value ≠ .matchWith scrutinees arms := by
    intro scrutinees arms statementEq
    exact isDeferred (by simp [DeferredStatementForm, statementEq])
  rcases allocationEq : initial.allocateStatementId with ⟨id, allocated⟩
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      initialInvariant.schemeIsolation
    have sameScope := inferStatementFuel_success_nonbinding_sameScope
      allocationEq success notLet notMatch
    simpa [State.lexicalScope] using
      congrArg LexicalScope.binders sameScope
  have closeOrdinary (branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts) :
      ∃ finalContext facts,
        RecursiveStatementInvariant wholeContext expectedReturn finalized
          result.state finalContext ∧
        StatementHasType
          ((result.state.toTypedSource roots).applySubstitution
            finalized.substitution)
          { returnType := finalized.substitution.apply expectedReturn
            loopDepth := inferenceContext.loopDepth }
          semanticContext result.id finalContext facts ∧
        StatementResultMatchesFactsAfterSubstitution finalized.substitution
          result facts :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal
        initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource :=
    resultSemanticExtension.trans semanticCoverageExtension
  cases statementEq : statement.value with
  | letDecl name sourceType initializer =>
      exact False.elim (notLet name sourceType initializer statementEq)
  | matchWith scrutinees arms =>
      exact False.elim (notMatch scrutinees arms statementEq)
  | returnStmt value =>
      cases value with
      | none =>
          apply closeOrdinary
          exact inferStatementFuel_returnUnit_atomicBranch statementEq
            allocationEq success initialInvariant.active
            resultSubstitutionExtension
      | some value =>
          apply closeOrdinary
          exact inferStatementFuel_returnValue_scopedBranch statementEq
            allocationEq success resources signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters initialInvariant resultSubstitutionExtension
            resultSemanticExtension semanticCoverageExtension
            rawResultExtension integerPatternsSubset integerLiteralsSubset
            requirementsSubset parentCovered expressionSound
  | expression expression trailingSemicolon =>
      apply closeOrdinary
      exact inferStatementFuel_expression_scopedBranch statementEq
        allocationEq success resources signaturesEq ownerEq parametersEq
        assumptionsEq signatureFormation functionsCanonical catalog
        signatureParameters initialInvariant resultSubstitutionExtension
        resultSemanticExtension semanticCoverageExtension rawResultExtension
        integerPatternsSubset integerLiteralsSubset requirementsSubset
        parentCovered expressionSound
  | assignValue target operator value =>
      apply closeOrdinary
      obtain ⟨active, typing, agreement⟩ :=
        inferStatementFuel_success_assignValue_recursive_scoped
          statementEq allocationEq success resources signaturesEq ownerEq
          parametersEq assumptionsEq signatureFormation functionsCanonical
          catalog signatureParameters initialInvariant.ready
          initialInvariant.nodesBelow initialInvariant.active
          (RecursiveExpressionInvariant.ofStatement
            (initialInvariant.allocateStatementId allocationEq))
          resultSubstitutionExtension parentCovered resources.graph_closed
          resultExtension rawResultExtension integerPatternsSubset
          integerLiteralsSubset requirementsSubset placeSound expressionSound
      exact ⟨semanticContext, _, active, typing, agreement⟩
  | assignBitNot target operatorSpan =>
      apply closeOrdinary
      obtain ⟨active, typing, agreement⟩ :=
        inferStatementFuel_success_assignBitNot_recursive_scoped
          statementEq allocationEq success resources signaturesEq ownerEq
          parametersEq assumptionsEq signatureFormation functionsCanonical
          catalog signatureParameters initialInvariant.nodesBelow
          initialInvariant.active
          (RecursiveExpressionInvariant.ofStatement
            (initialInvariant.allocateStatementId allocationEq))
          resultSubstitutionExtension parentCovered resources.graph_closed
          resultExtension rawResultExtension integerPatternsSubset
          integerLiteralsSubset requirementsSubset placeSound
      exact ⟨semanticContext, _, active, typing, agreement⟩
  | block body =>
      exact inferStatementFuel_success_block_of_scoped_body statementEq
        allocationEq success resources signaturesEq ownerEq parametersEq
        assumptionsEq signatureFormation functionsCanonical catalog
        signatureParameters initialInvariant resultSubstitutionExtension
        resultExtension rawResultExtension integerPatternsSubset
        integerLiteralsSubset requirementsSubset parentCovered
        statementsSound
  | whileLoop condition body =>
      exact inferStatementFuel_success_whileLoop_of_scoped_body statementEq
        allocationEq success resources signaturesEq ownerEq parametersEq
        assumptionsEq signatureFormation functionsCanonical catalog
        signatureParameters initialInvariant resultSubstitutionExtension
        resultExtension rawResultExtension integerPatternsSubset
        integerLiteralsSubset requirementsSubset parentCovered
        (inferStatementFuel_success_whileLoop_condition_scoped statementEq
          allocationEq success resources signaturesEq ownerEq parametersEq
          assumptionsEq signatureFormation functionsCanonical catalog
          signatureParameters initialInvariant resultSubstitutionExtension
          resultExtension rawResultExtension integerPatternsSubset
          integerLiteralsSubset requirementsSubset parentCovered
          expressionSound)
        statementsSound
  | ifThen condition thenBody elseBody =>
      cases elseBody with
      | none =>
          exact inferStatementFuel_success_ifWithoutElse_of_scoped_body
            statementEq allocationEq success resources signaturesEq ownerEq
            parametersEq assumptionsEq signatureFormation functionsCanonical
            catalog signatureParameters initialInvariant
            resultSubstitutionExtension resultExtension rawResultExtension
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            parentCovered
            (inferStatementFuel_success_ifWithoutElse_condition_scoped
              statementEq allocationEq success resources signaturesEq ownerEq
              parametersEq assumptionsEq signatureFormation
              functionsCanonical catalog signatureParameters initialInvariant
              resultSubstitutionExtension resultExtension rawResultExtension
              integerPatternsSubset integerLiteralsSubset requirementsSubset
              parentCovered expressionSound)
            statementsSound
      | some elseBody =>
          exact inferStatementFuel_success_ifWithElse_of_scoped_bodies
            statementEq allocationEq success resources signaturesEq ownerEq
            parametersEq assumptionsEq signatureFormation functionsCanonical
            catalog signatureParameters initialInvariant
            resultSubstitutionExtension resultExtension rawResultExtension
            integerPatternsSubset integerLiteralsSubset requirementsSubset
            parentCovered
            (inferStatementFuel_success_ifWithElse_condition_scoped
              statementEq allocationEq success resources signaturesEq ownerEq
              parametersEq assumptionsEq signatureFormation
              functionsCanonical catalog signatureParameters initialInvariant
              resultSubstitutionExtension resultExtension rawResultExtension
              integerPatternsSubset integerLiteralsSubset requirementsSubset
              parentCovered expressionSound)
            statementsSound
  | forLoop headerSpan initializer condition post body =>
      exact inferStatementFuel_success_forLoop_scoped statementEq
        allocationEq success resources signaturesEq ownerEq parametersEq
        assumptionsEq signatureFormation functionsCanonical catalog
        signatureParameters initialInvariant resultSubstitutionExtension
        resultExtension rawResultExtension integerPatternsSubset
        integerLiteralsSubset requirementsSubset parentCovered forItemsSound
        expressionSound statementsSound forItemsSound
  | breakStmt =>
      apply closeOrdinary
      exact inferStatementFuel_break_atomicBranch statementEq allocationEq
        success initialInvariant.active
  | continueStmt =>
      apply closeOrdinary
      exact inferStatementFuel_continue_atomicBranch statementEq allocationEq
        success initialInvariant.active
  | assembly body =>
      simp [Detail.inferStatementFuel, statementEq] at success
  | error =>
      simp [Detail.inferStatementFuel, statementEq] at success

end Solcore.SourceSemantics.SourceInferenceSoundness
end
