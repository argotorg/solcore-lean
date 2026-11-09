import Solcore.SourceSemantics.Internal.Selected.Children
import Solcore.SourceSemantics.Internal.Inference.RootedContracts
import Solcore.SourceSemantics.Internal.Selected.StatementReferences
import Solcore.SourceSemantics.Internal.Selected.State
import Solcore.SourceSemantics.Internal.Inference.ExpressionCalls
import Solcore.SourceSemantics.Internal.Inference.StatementResources

/-!
# Selected statements

Statements keep their occurrence subtrees, and blocks, conditions and assignments follow from that.
-/

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedAssignmentChildren
/-!
Actual-success semantic resources for assignment.  A place is inferred first;
the value starts either in that place state or in its successful `Word`
unification state.  Both routes preserve the recursive expression invariant.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- The actual place and RHS of an assignment each start with the recursive
invariants needed by their scoped soundness theorems. -/
theorem inferAssignedValueFuel_children_actual_invariants
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
      assignment.target = { place with type := final.resolve place.type } ∧
      ((valueInitial = placeState ∧ expected = placeState.resolve place.type) ∨
        (Detail.unify placeState place.type .word = .ok valueInitial ∧ expected = .word)) := by
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
              { actualPlace with type := final.resolve actualPlace.type } ∧
            ((valueInitial = actualPlaceState ∧ expected = actualPlaceState.resolve actualPlace.type) ∨
              (Detail.unify actualPlaceState actualPlace.type .word = .ok valueInitial ∧ expected = .word)) := by
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
                  Ty.variablesBelow_constructor _ _, rfl, rfl, .inr ⟨unifyResult, rfl⟩⟩
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
                expectedBelow, rfl, rfl, .inl ⟨rfl, rfl⟩⟩
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
      | uncheckedDivide => exact finishNonEqual success
      | uncheckedModulo => exact finishNonEqual success

/-- The actual inferred place and RHS are typed in one enclosing statement
source.  The place is inferred before the RHS; its recorded type is finally
resolved, but final semantic substitution makes that update observationally
identical to the original place type. -/
theorem actualInferAssignedValueFuel_children_rootedSound
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn : Ty} {targetExpression value : Syntax.Expr}
    {operator : Syntax.ValueAssignOp}
    {initial assignmentState parentState evidenceState : State}
    {assignment : AssignmentResolution} {inferred : InferredExpression}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (success : Detail.inferAssignedValueFuel fuel inferenceContext
      targetExpression operator value initial =
        .ok (assignment, inferred, assignmentState))
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures finalized.solvedRequirements finalized.typedSource)
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
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (assignmentSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        assignmentState.inference.substitution)
    (assignmentToParent : TypingSourceExtends
      (assignmentState.toTypedSource roots)
      (parentState.toTypedSource roots))
    (rawKeys : ∀ key, .expression key ∈ assignment.references →
      RawSubtreePreserved (parentState.toTypedSource roots) (evidenceState.toTypedSource roots) (.expression key))
    (rawValue : RawSubtreePreserved (parentState.toTypedSource roots) (evidenceState.toTypedSource roots) (.expression inferred.id))
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
    (keysActualCovered : ∀ key, .expression key ∈ assignment.references → ActualContext.Covers finalized frames (.expression key))
    (valueActualCovered : ActualContext.Covers finalized frames (.expression inferred.id))
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
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
      referencesEq, targetEq, valueOrigin⟩ :=
    inferAssignedValueFuel_children_actual_invariants success signatureFormation
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
    placeSound placeSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters initialInvariant actual operational placeInvariant.substitutionExtension
      placeToParent (fun key member => rawKeys key (by simpa [AssignmentResolution.references, referencesEq] using member))
      (List.Subset.trans placePatternsSubset assignmentPatternsSubset)
      (List.Subset.trans placeLiteralsSubset assignmentLiteralsSubset)
      (List.Subset.trans placeRequirementsSubset
        assignmentRequirementsSubset) placeKeysCovered
      (fun key member => keysActualCovered key (by simpa [AssignmentResolution.references, referencesEq] using member))
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
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties initialInvariant.ready signatureFormation functionsCanonical placeSuccess
  have placeOperational := operational.ofPlace placeSuccess placeProperties.1.next_le
  have valueOperational : ActualStateInvariant valueInitial (evidenceState.toTypedSource roots) := by
    rcases valueOrigin with ⟨rfl, _⟩ | ⟨unified, _⟩
    · exact placeOperational
    · exact placeOperational.unify unified
  have expectedAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expected) := by
    rcases valueOrigin with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have resolved : finalized.substitution.apply (placeState.resolve place.type) = finalized.substitution.apply place.type := by
        simpa only [State.resolve, InferState.resolve] using placeInvariant.substitutionExtension place.type
      rw [resolved]
      exact sourcePlace_type_admissible placeTyped
    · exact TypeAdmissible.word (initialInvariant.typeParameterBinders (by simpa only [ownerEq, parametersEq] using signatureParameters))
  have valueTyped : ExpressionHasType
      ((parentState.toTypedSource roots).applySubstitution
        finalized.substitution)
      semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound valueSuccess resources interfaces assignmentSubstitutionExtension
      signaturesEq ownerEq parametersEq assumptionsEq signatureFormation
      functionsCanonical catalog signatureParameters valueInvariant actual valueOperational
      (by intro candidate member
          simp only [Option.mem_def] at member
          cases member
          exact expectedBelow)
      (by intro candidate member; have same : candidate = expected := Option.some.inj member.symm; simpa only [same] using expectedAdmissible)
      (SubtreePreserved.ofTypingSourceExtends (assignmentToParent.applySubstitution finalized.substitution))
      (rawValue.monoBefore assignmentToParent)
      assignmentPatternsSubset assignmentLiteralsSubset
      assignmentRequirementsSubset rhsCovered valueActualCovered
  exact ⟨by simpa only [targetSubstEq, targetTypeEq] using placeTyped,
    valueTyped⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedRootedStatementSequencing
/-! Statement sequencing carries a source occurrence predicate alongside
whole-body evidence coverage. Actual generalized-initializer ancestry can
therefore follow each returned root without an unrelated child premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualStatementsFuel_with_selected_rooted_sources
    (invariant : Frontend.SourceInference.State →
      SourceSemantics.Context → Prop)
    (extra : Frontend.SourceInference.State → Prop)
    (rootScope : NodeId → Prop)
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statements : List Syntax.Statement}
    {expectedReturn : TypeSystem.Ty}
    {state : Frontend.SourceInference.State} {result : Detail.BlockResult}
    {evidenceState : Frontend.SourceInference.State}
    {ambientSource coverageSource : TypedSource}
    {control : ControlContext}
    {substitution : TypeSystem.Substitution}
    {semanticContext : SourceSemantics.Context}
    (roots : List NodeId := [])
    (initialInvariant : invariant state semanticContext)
    (initialBelow : state.NodesBelowNextOccurrence)
    (resultExtension : ∀ id ∈ result.statements,
      SubtreePreserved substitution (result.state.toTypedSource roots)
        ambientSource (.statement id))
    (rawPreserved : ∀ id ∈ result.statements,
      RawSubtreePreserved (result.state.toTypedSource roots)
        (evidenceState.toTypedSource roots) (.statement id))
    (integerPatternsSubset :
      result.state.integerPatterns ⊆ evidenceState.integerPatterns)
    (requirementsSubset :
      result.state.requirements ⊆ evidenceState.requirements)
    (extraResult : extra result.state)
    (extraHead : ∀ {headFuel childFuel : Nat}
        {headInitial : Frontend.SourceInference.State}
        {headContext : SourceSemantics.Context}
        {headStatement : Syntax.Statement}
        {head : Detail.StatementResult} {tail : Detail.BlockResult}
        {remaining : List Syntax.Statement},
      invariant headInitial headContext →
      Detail.inferStatementFuel headFuel inferenceContext headStatement
        expectedReturn headInitial = .ok head →
      Detail.inferStatementsFuel childFuel inferenceContext remaining
        expectedReturn head.state = .ok tail →
      extra tail.state → extra head.state)
    (coveredStatements : ∀ id, id ∈ result.statements →
      TemplateScopeCovered coverageSource semanticContext (.statement id) ∧ rootScope (.statement id))
    (statementSound :
      ∀ {childFuel : Nat} {input : Frontend.SourceInference.State}
        {inputContext : SourceSemantics.Context}
        {statement : Syntax.Statement} {head : Detail.StatementResult},
        childFuel < fuel →
        invariant input inputContext →
        Detail.inferStatementFuel childFuel inferenceContext statement
          expectedReturn input = .ok head →
        SubtreePreserved substitution (head.state.toTypedSource roots)
          ambientSource (.statement head.id) →
        RawSubtreePreserved (head.state.toTypedSource roots)
          (evidenceState.toTypedSource roots) (.statement head.id) →
        head.state.integerPatterns ⊆ evidenceState.integerPatterns →
        head.state.requirements ⊆ evidenceState.requirements →
        extra head.state →
        TemplateScopeCovered coverageSource inputContext (.statement head.id) ∧ rootScope (.statement head.id) →
        ∃ outputContext facts,
          invariant head.state outputContext ∧
          StatementHasType
            ((head.state.toTypedSource roots).applySubstitution substitution)
            control inputContext head.id outputContext facts ∧
          StatementResultMatchesFactsAfterSubstitution substitution head facts)
    (success : Detail.inferStatementsFuel fuel inferenceContext statements
      expectedReturn state = .ok result) :
    ∃ finalContext facts,
      invariant result.state finalContext ∧
      StatementsHaveType ambientSource control semanticContext
        result.statements finalContext facts ∧
      BlockResultMatchesFactsAfterSubstitution substitution result facts := by
  induction fuel generalizing statements state semanticContext result with
  | zero =>
      simp [Detail.inferStatementsFuel] at success
  | succ fuel induction =>
      cases statements with
      | nil =>
          have resultEq := inferStatementsFuel_success_nil_facts success
          subst result
          exact ⟨semanticContext, .empty, initialInvariant,
            .nil control semanticContext,
            BlockResultMatchesFactsAfterSubstitution.empty substitution state⟩
      | cons statement rest =>
          cases rest with
          | nil =>
              obtain ⟨head, headSuccess, resultEq⟩ :=
                inferStatementsFuel_success_singleton_facts success
              subst result
              have headCovered : TemplateScopeCovered coverageSource
                  semanticContext (.statement head.id) ∧ rootScope (.statement head.id) :=
                coveredStatements head.id (by simp)
              obtain ⟨finalContext, headFacts, finalInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess (resultExtension head.id (by simp))
                  (rawPreserved head.id (by simp)) integerPatternsSubset
                  requirementsSubset extraResult headCovered
              have headTypingAmbient :=
                (resultExtension head.id (by simp)).subgraph.statement headTyping (.inl rfl)
              exact ⟨finalContext, .singleton headFacts, finalInvariant,
                .singleton headTypingAmbient,
                BlockResultMatchesFactsAfterSubstitution.singleton headMatches⟩
          | cons next rest =>
              obtain ⟨head, tail, headSuccess, tailSuccess, resultEq⟩ :=
                inferStatementsFuel_success_cons_facts success
              subst result
              have headBelow : head.state.NodesBelowNextOccurrence :=
                (Detail.inferStatementFuel_occurrenceBoundExtends headSuccess
                  ).nodesBelowNextOccurrence initialBelow
              have headToTail : TypingSourceExtends
                  (head.state.toTypedSource roots) (tail.state.toTypedSource roots) :=
                inferStatementsFuel_success_typingSourceExtends tailSuccess headBelow roots
              have headExtension : SubtreePreserved substitution
                  (head.state.toTypedSource roots) ambientSource (.statement head.id) :=
                (resultExtension head.id (by simp)).monoBefore headToTail
              have headRawPreserved : RawSubtreePreserved
                  (head.state.toTypedSource roots) (evidenceState.toTypedSource roots)
                  (.statement head.id) :=
                (rawPreserved head.id (by simp)).monoBefore headToTail
              have headIntegerPatternsSubset :
                  head.state.integerPatterns ⊆
                    evidenceState.integerPatterns :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_integerPatterns_subset
                    tailSuccess)
                  integerPatternsSubset
              have headRequirementsSubset :
                  head.state.requirements ⊆ evidenceState.requirements :=
                List.Subset.trans
                  (Detail.inferStatementsFuel_requirements_subset tailSuccess)
                  requirementsSubset
              have headExtra : extra head.state :=
                extraHead initialInvariant headSuccess tailSuccess extraResult
              have headCovered : TemplateScopeCovered coverageSource
                  semanticContext (.statement head.id) ∧ rootScope (.statement head.id) :=
                coveredStatements head.id (by simp)
              obtain ⟨middleContext, headFacts, middleInvariant, headTyping,
                  headMatches⟩ :=
                statementSound (Nat.lt_succ_self fuel) initialInvariant
                  headSuccess headExtension headRawPreserved headIntegerPatternsSubset
                  headRequirementsSubset headExtra headCovered
              have headTypingAmbient :=
                headExtension.subgraph.statement headTyping (.inl rfl)
              have middleAssumptionsEq :
                  middleContext.assumptions = semanticContext.assumptions :=
                statementHasType_assumptions_eq headTypingAmbient
              have tailCovered : ∀ id, id ∈ tail.statements →
                  TemplateScopeCovered coverageSource middleContext
                    (.statement id) ∧ rootScope (.statement id) := by
                intro id member
                refine ⟨?_, (coveredStatements id (by simp [member])).2⟩
                intro owner scopes
                change owner.requirement.predicate ∈ middleContext.assumptions
                rw [middleAssumptionsEq]
                exact (coveredStatements id (by simp [member])).1 owner scopes
              obtain ⟨finalContext, tailFacts, finalInvariant, tailTyping,
                  tailMatches⟩ :=
                induction (statements := next :: rest)
                  (state := head.state) (result := tail)
                  (semanticContext := middleContext)
                  middleInvariant headBelow
                  (fun id member => resultExtension id (by simp [member]))
                  (fun id member => rawPreserved id (by simp [member]))
                  integerPatternsSubset requirementsSubset extraResult
                  tailCovered
                  (fun childBound childInvariant childSuccess childExtension childRawPreserved
                    childIntegerPatternsSubset childRequirementsSubset
                    childExtra childCovered =>
                    statementSound (Nat.lt_trans childBound
                      (Nat.lt_succ_self fuel)) childInvariant childSuccess
                      childExtension childRawPreserved childIntegerPatternsSubset
                      childRequirementsSubset childExtra childCovered)
                  tailSuccess
              obtain ⟨tailHead, tailRest, tailStatementsEq⟩ :=
                inferStatementsFuel_success_statements_eq_cons tailSuccess
              have sequenceTyping : StatementsHaveType ambientSource control
                  semanticContext (head.id :: tail.statements) finalContext
                  (.cons headFacts tailFacts) := by
                rw [tailStatementsEq]
                exact .cons headTypingAmbient
                  (by simpa [tailStatementsEq] using tailTyping)
              exact ⟨finalContext, .cons headFacts tailFacts, finalInvariant,
                sequenceTyping,
                BlockResultMatchesFactsAfterSubstitution.cons headMatches
                  tailMatches⟩

/-- Sequential statements preserve the type scope of the expected return. -/
theorem selected_statement_return_admissible
    {source : TypedSource} {control : ControlContext}
    {before after : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {type : Ty}
    (typing : StatementHasType source control before id after facts)
    (admissible : TypeAdmissible before type) :
    TypeAdmissible after type := by
  have fields := statementHasType_nonlocal_fields_eq typing
  have variables : after.typeVariables = before.typeVariables := by
    cases typing <;> try rfl
    all_goals
      exact BinderExtends.typeVariables_eq
        (by assumption : BinderExtends source.owner before _ after)
  exact StructuralSubstitution.TypeAdmissible.transportContext
    fields.1 fields.2.1 fields.2.2.1 variables fields.2.2.2.1 admissible

theorem actualInferStatementsFuelRootedSoundness_of_selected_statementSoundness
    {fuel : Nat}
    (statementSound : ∀ childFuel, childFuel < fuel →
      ActualInferStatementFuelRootedSoundness childFuel) :
    ActualInferStatementsFuelRootedSoundness fuel := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statements
    initial result evidenceState roots finalized semanticSource frames semanticContext
    success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    signatureFormation functionsCanonical catalog signatureParameters
    initialInvariant actual operational returnAdmissible finalSubstitutionExtension resultExtension
    rawResultExtension integerPatternsSubset
    integerLiteralsSubset requirementsSubset covered actualCovered
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    actualStatementsFuel_with_selected_rooted_sources
      (fun state context => RecursiveStatementInvariant wholeContext
        expectedReturn finalized state context ∧ ActualContext wholeContext finalized frames context ∧
        ActualStateInvariant state (evidenceState.toTypedSource roots) ∧
        TypeAdmissible context (finalized.substitution.apply expectedReturn))
      (fun state => finalized.substitution.SemanticallyExtends
        state.inference.substitution ∧
        state.integerLiterals ⊆ evidenceState.integerLiterals)
      (ActualContext.Covers finalized frames)
      (roots := roots) ⟨initialInvariant, actual, operational, returnAdmissible⟩ initialInvariant.nodesBelow
      resultExtension rawResultExtension integerPatternsSubset requirementsSubset
      ⟨finalSubstitutionExtension, integerLiteralsSubset⟩
      (by
        intro headFuel childFuel headInitial headContext headStatement head
          tail remaining headInvariant headSuccess tailSuccess tailExtra
        have headProperties := Detail.inferStatementFuel_inferenceProperties
          headInvariant.1.ready signatureFormation functionsCanonical
          headInvariant.1.returnBelow headSuccess
        have tailProperties := Detail.inferStatementsFuel_inferenceProperties
          headProperties.2.1 signatureFormation functionsCanonical
          (headInvariant.1.returnBelow.weaken headProperties.1.next_le)
          tailSuccess
        exact ⟨TypeSystem.Substitution.SemanticallyExtends.trans
            tailExtra.1 tailProperties.1.substitution_extends,
          List.Subset.trans
            (Detail.inferStatementsFuel_integerLiterals_subset tailSuccess)
            tailExtra.2⟩)
      (fun id member => ⟨covered id member, actualCovered id member⟩)
      (by
        intro childFuel input inputContext statement head childBound childInvariant childSuccess childExtension childRawPreserved
          childIntegerPatternsSubset childRequirementsSubset childExtra childCovered
        obtain ⟨context, facts, invariant, actual, operational, typed, agreement⟩ :=
          statementSound _ childBound childSuccess resources interfaces signaturesEq
            ownerEq parametersEq assumptionsEq signatureFormation
            functionsCanonical catalog signatureParameters childInvariant.1 childInvariant.2.1 childInvariant.2.2.1 childInvariant.2.2.2
            childExtra.1 childExtension childRawPreserved
            childIntegerPatternsSubset childExtra.2
            childRequirementsSubset childCovered.1 childCovered.2
        have admissible := selected_statement_return_admissible typed childInvariant.2.2.2
        exact ⟨context, facts, ⟨invariant, actual, operational, admissible⟩, typed, agreement⟩)
      success
  exact ⟨finalContext, facts, finalInvariant.1, finalInvariant.2.1, finalInvariant.2.2.1, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementAssignmentSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuelRootedSoundness_assignValue {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel)
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression value : Syntax.Expr}
    {operator : Syntax.Located Syntax.ValueAssignOp} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .assignValue targetExpression operator value →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement targetExpression value operator initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have allocatedInvariant := invariant.allocateStatementId allocationEq
  have allocatedOperational := operational.allocateStatementId allocationEq
  obtain ⟨assignment, inferred, assignmentState, assignmentSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_assignValue_facts statementEq allocationEq success roots
  have assignedToParent : TypingSourceExtends (assignmentState.toTypedSource roots) (result.state.toTypedSource roots) := by
    rw [resultEq]
    exact ⟨rfl, State.recordNode_nodesPrefix _ _⟩
  have assignedExtension : finalized.substitution.SemanticallyExtends assignmentState.inference.substitution := by
    simpa only [resultEq, State.recordNode] using extension
  have final := raw.finalized resources
  have reference : ∀ key, .expression key ∈ assignment.references →
      (.expression key : NodeId) ∈ (StatementForm.assignValue assignment operator.value inferred.id).references := by
    intro key member
    simp only [StatementForm.references]
    exact List.mem_append_left _ member
  have keysCovered : ∀ key, .expression key ∈ assignment.references →
      TemplateScopeCovered finalized.typedSource semanticContext (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
        PlaceResolution.references] using reference key member
  have rhsCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  obtain ⟨placeTyped, valueTyped⟩ := actualInferAssignedValueFuel_children_rootedSound assignmentSuccess resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical
    (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual allocatedOperational assignedExtension assignedToParent
    (fun key member => raw.child (directChild_statement_reference contains (reference key member)))
    (raw.child (directChild_statement_reference contains (by simp [StatementForm.references])))
    (by simpa only [resultEq, State.recordNode] using patterns)
    (by simpa only [resultEq, State.recordNode] using literals)
    (by simpa only [resultEq, State.recordNode] using requirements)
    keysCovered rhsCovered
    (fun key member => actualCovered.preserved_statement_reference contains final (reference key member))
    (actualCovered.preserved_statement_reference contains final (by simp [StatementForm.references])) placeSound expressionSound
  obtain ⟨active, typing, agreement⟩ := inferStatementFuel_success_assignValue_sound_of_typed_children
    statementEq allocationEq success assignmentSuccess invariant.ready formation functions invariant.active extension roots
    placeTyped valueTyped
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have assignedBinders := congrArg LexicalScope.binders (Detail.inferAssignedValueFuel_success_lexicalScope_eq assignmentSuccess)
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using assignedBinders.trans allocatedBinders
  have properties := Detail.inferStatementFuel_inferenceProperties invariant.ready formation functions invariant.returnBelow success
  have finalInvariant := invariant.of_statement_typing success formation functions active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success) extension
    (activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq) typing
  exact ⟨semanticContext, _, finalInvariant, actual, operational.ofStatementPreservingBinders success bindersEq
    properties.1.next_le, typing, agreement⟩

theorem actualInferStatementFuelRootedSoundness_assignBitNot {fuel : Nat}
    (placeSound : ActualInferPlaceFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {targetExpression : Syntax.Expr} {operatorSpan : Syntax.SourceSpan} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .assignBitNot targetExpression operatorSpan →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement targetExpression operatorSpan initial result
    evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    _returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have allocatedInvariant := invariant.allocateStatementId allocationEq
  have allocatedOperational := operational.allocateStatementId allocationEq
  obtain ⟨place, placeState, unified, placeSuccess, unifySuccess, _, resultEq, contains⟩ :=
    inferStatementFuel_success_assignBitNot_facts statementEq allocationEq success roots
  have placeToParent : TypingSourceExtends (placeState.toTypedSource roots) (result.state.toTypedSource roots) := by
    constructor
    · change result.state.owner = placeState.owner
      rw [resultEq]
      exact congrArg State.Header.owner (Detail.unify_state_header unifySuccess)
    · change placeState.nodes <+: result.state.nodes
      rw [resultEq]
      change placeState.nodes <+: (unified.recordNode _).nodes
      rw [← (Detail.unify_occurrenceState_eq unifySuccess).1]
      exact State.recordNode_nodesPrefix _ _
  have placeProperties := Detail.inferPlaceFuel_inferenceProperties allocatedInvariant.ready formation functions placeSuccess
  have unifiedExtension : finalized.substitution.SemanticallyExtends unified.inference.substitution := by
    simpa only [resultEq, State.recordNode] using extension
  have placeExtension := unifiedExtension.trans
    (Detail.unify_inferenceProgress placeProperties.2.1.solved placeProperties.2.2
      (Ty.variablesBelow_constructor _ _) unifySuccess).substitution_extends
  have final := raw.finalized resources
  have reference : ∀ key, .expression key ∈ place.references →
      (.expression key : NodeId) ∈ (StatementForm.assignBitNot
        { target := { place with type := unified.resolve place.type }}).references := by
    intro key member
    simpa [StatementForm.references, AssignmentResolution.references, PlaceResolution.references] using member
  have keysCovered : ∀ key, .expression key ∈ place.references →
      TemplateScopeCovered finalized.typedSource semanticContext (.expression key) := by
    intro key member
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference covered resources.graph_closed
      (final.containsStatement contains)
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simpa [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references,
        AssignmentResolution.references, AssignmentResolution.applySubstitution, PlaceResolution.applySubstitution,
        PlaceResolution.references] using reference key member
  have placePatterns : placeState.integerPatterns ⊆ evidenceState.integerPatterns := by
    simpa only [resultEq, State.recordNode, Detail.unify_integerPatterns unifySuccess] using patterns
  have placeLiterals : placeState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa only [resultEq, State.recordNode, Detail.unify_integerLiterals unifySuccess] using literals
  have placeRequirements : placeState.requirements ⊆ evidenceState.requirements := by
    simpa only [resultEq, State.recordNode, Detail.unify_requirements_eq unifySuccess] using requirements
  have placeTyped := placeSound placeSuccess resources interfaces signaturesEq ownerEq parametersEq assumptionsEq
    formation functions catalog canonical (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual allocatedOperational
    placeExtension placeToParent
    (fun key member => raw.child (directChild_statement_reference contains (reference key member)))
    placePatterns placeLiterals placeRequirements keysCovered
    (fun key member => actualCovered.preserved_statement_reference contains final (reference key member))
  obtain ⟨active, typing, agreement⟩ := inferStatementFuel_success_assignBitNot_sound_of_actual_child
    statementEq allocationEq success invariant.active extension roots placeSuccess placeTyped
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have placeBinders := congrArg LexicalScope.binders (Detail.inferPlaceFuel_success_lexicalScope_eq placeSuccess)
    have unifiedBinders := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifySuccess)
    have allocatedBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using unifiedBinders.trans (placeBinders.trans allocatedBinders)
  have properties := Detail.inferStatementFuel_inferenceProperties invariant.ready formation functions invariant.returnBelow success
  have finalInvariant := invariant.of_statement_typing success formation functions active
    (inferStatementFuel_preserves_localBindersBelowNextLocal invariant.bindersBelow success) extension
    (activeSchemeQuantifierIsolation_transport invariant.schemeIsolation bindersEq) typing
  exact ⟨semanticContext, _, finalInvariant, actual, operational.ofStatementPreservingBinders success bindersEq
    properties.1.next_le, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementAtomicSoundness
/-! Actual control statements without child inference retain the current
source context and operational state conditions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferStatementFuel_returnUnit_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_returnUnit_sound statementEq allocationEq success
      initialInvariant.active resultSubstitutionExtension roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨unified, unifiedSuccess, _, resultEq, _⟩ :=
    inferStatementFuel_success_returnUnit_facts statementEq allocationEq success roots
  have unifiedScope := congrArg LexicalScope.binders (Detail.unify_preserves_lexicalScope unifiedSuccess)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using unifiedScope.trans allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

theorem actualInferStatementFuel_break_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .breakStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_break_sound statementEq allocationEq success
      initialInvariant.active roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_break_facts statementEq allocationEq success roots
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

theorem actualInferStatementFuel_continue_atomicBranch
    {fuel : Nat} {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .continueStmt)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (signatureFormation : ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext expectedReturn
      finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution result facts := by
  obtain ⟨active, statementType, agreement⟩ :=
    inferStatementFuel_success_continue_sound statementEq allocationEq success
      initialInvariant.active roots
  have allocationScope := congrArg LexicalScope.binders
    (Detail.allocateStatementId_success_lexicalScope allocationEq)
  obtain ⟨_, resultEq, _⟩ :=
    inferStatementFuel_success_continue_facts statementEq allocationEq success roots
  have bindersEq : result.state.localBinders = initial.localBinders := by
    simpa only [resultEq, State.recordNode, State.lexicalScope] using allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementBodies
/-! Blocks and branches retain only their own actual occurrence subtrees.
Their local typing still uses the completed parent statement source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuel_success_block_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .block body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨bodyResult, bodySuccess, resultEq, parentNode⟩ :=
    inferStatementFuel_success_block_facts statementEq allocationEq success
      roots
  obtain ⟨bodyResult', bodySuccess', _allocatedBelow, bodyExtension,
      bodyIntegerPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_block_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  have bodyResultEq : bodyResult' = bodyResult := by
    rw [bodySuccess] at bodySuccess'
    exact (Except.ok.inj bodySuccess').symm
  subst bodyResult'
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childEdge : DirectChild (result.state.toTypedSource roots)
        (.statement result.id) (.statement child) := by
      refine ⟨.statement {
        id := result.id
        span := statement.span
        type := result.type
        form := .block bodyResult.statements
      }, ?_, ?_⟩
      · refine ⟨parentNode.1, ?_⟩
        exact congrArg NodeId.statement parentNode.2
      · simpa [nodeChildIds, Node.references, StatementForm.references] using
          (List.mem_map.mpr ⟨child, member, rfl⟩ :
            NodeId.statement child ∈
              bodyResult.statements.map NodeId.statement)
    have coveredEdge : DirectChild finalized.typedSource
        (.statement result.id) (.statement child) :=
      resultExtension.directChild childEdge
    exact TemplateScopeCovered.statementChild parentCovered
      resources.graph_closed coveredEdge (fun _ membership => membership)
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have blockSound := inferStatementFuel_success_block_sound
      statementEq allocationEq success initialInvariant.active roots
      (by
        intro actualBody actualSuccess
        have actualEq : actualBody = bodyResult := by
          rw [bodySuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        subst actualBody
        obtain ⟨bodyContext, bodyFacts, bodyInvariant, _bodyActual, _bodyOperational, bodyTyping,
            bodyAgreement⟩ :=
          bodySound bodySuccess resources interfaces signaturesEq ownerEq parametersEq
            assumptionsEq signatureFormation functionsCanonical catalog
            signatureParameters allocatedInvariant actual (operational.allocateStatementId allocationEq) returnAdmissible bodySubstitutionExtension
            (fun child _ => SubtreePreserved.ofTypingSourceExtends
              (bodyExtension.applySubstitution finalized.substitution))
            (fun child member => (rawResultExtension.child
              (directChild_statement_reference parentNode (by simp [StatementForm.references, member]))).monoBefore bodyExtension)
            (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
            (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
            (List.Subset.trans bodyRequirementsSubset requirementsSubset)
            bodyCovered (fun child member => parentActualCovered.preserved_statement_reference
              parentNode resultExtension (by simp [StatementForm.references, member]))
        exact ⟨bodyContext, bodyFacts, bodyInvariant.active, bodyTyping,
          bodyAgreement⟩)
    obtain ⟨facts, active, typing, agreement⟩ := blockSound
    exact ⟨semanticContext, facts, active, typing, agreement⟩
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      allocatedInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- The while-loop body is checked at the actual condition-result state and
typed under the loop-depth increment.  Its semantic source is the completed
while statement, while coverage and requirements remain anchored to the
whole finalized body. -/
theorem actualInferStatementFuel_success_whileLoop_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  let loopContext : Frontend.SourceInference.Context := {
    inferenceContext with loopDepth := inferenceContext.loopDepth + 1 }
  obtain ⟨inferredCondition, conditionState, bodyResult, conditionSuccess,
      actualBodySuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension, bodyIntegerPatternsSubset,
      bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [actualBodySuccess] at actualBodySuccess'
    exact (Except.ok.inj actualBodySuccess').symm
  subst actualBodyResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := loopContext) conditionProperties.2.1 signatureFormation
    functionsCanonical conditionReturnBelow actualBodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      bodySubstitutionExtension bodyProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have bodyIntegerLiteralsSubset :
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyCovered : ∀ child, child ∈ bodyResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.whileLoop inferredCondition.id
          bodyResult.statements).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨bodyFinal, bodyFacts, bodyInvariant, _bodyActual, _bodyOperational, bodyTyping,
      bodyAgreement⟩ :=
    bodySound actualBodySuccess resources interfaces (by simpa [loopContext] using signaturesEq)
      (by simpa [loopContext] using ownerEq)
      (by simpa [loopContext] using parametersEq)
      (by simpa [loopContext] using assumptionsEq)
      signatureFormation functionsCanonical catalog signatureParameters
      conditionInvariant actual conditionOperational returnAdmissible bodySubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (bodySourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore bodySourceExtension)
      (List.Subset.trans bodyIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans bodyIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans bodyRequirementsSubset requirementsSubset)
      bodyCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := .loop bodyFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact whileLoopStatementHasType_afterSubstitution contains
        conditionTyping conditionEq bodyTyping
    · exact StatementResultMatchesFactsAfterSubstitution.whileLoop
        finalized.substitution bodyFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- The no-else conditional consumes only its actual then-body traversal;
the missing else branch contributes the ordinary unit control fact. -/
theorem actualInferStatementFuel_success_ifWithoutElse_of_scoped_body
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (thenSound : ActualInferStatementsFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, conditionSuccess,
      thenSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      _conditionBelow, thenSourceExtension, thenIntegerPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      thenSubstitutionExtension thenProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          none).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, _thenActual, _thenOperational, thenTyping,
      thenAgreement⟩ :=
    thenSound thenSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant actual conditionOperational returnAdmissible thenSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (thenSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore thenSourceExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := .unit
        hasValue := false
        sawReturn := false
        control := thenFacts.control.branches (.ordinary .unit)
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithoutElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithoutElse
        finalized.substitution thenFacts id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

/-- Both branches of a successful conditional are typed from their concrete
traces.  The second branch starts from the restored condition scope, while
both branches' roots remain direct children of the completed parent node. -/
theorem actualInferStatementFuel_success_ifWithElse_of_scoped_bodies
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody
      (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions =
      wholeContext.assumptions)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (conditionSound : ∀ {inferredCondition : InferredExpression}
      {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type))
    (branchSound : ActualInferStatementsFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  obtain ⟨inferredCondition, conditionState, thenResult, elseResult,
      conditionSuccess, thenSuccess, elseSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  obtain ⟨actualConditionState, actualThenResult, actualElseResult,
      ⟨actualCondition, actualConditionSuccess⟩, actualThenSuccess,
      actualElseSuccess, _conditionBelow, _elseInputBelow,
      thenSourceExtension, elseSourceExtension,
      thenIntegerPatternsSubset, elseIntegerPatternsSubset,
      thenRequirementsSubset, elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess)).symm
  subst actualConditionState
  have thenResultEq : actualThenResult = thenResult := by
    rw [thenSuccess] at actualThenSuccess
    exact (Except.ok.inj actualThenSuccess).symm
  subst actualThenResult
  have elseResultEq : actualElseResult = elseResult := by
    rw [elseSuccess] at actualElseSuccess
    exact (Except.ok.inj actualElseSuccess).symm
  subst actualElseResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenBelow : thenResult.state.NodesBelowNextOccurrence :=
    (Detail.inferStatementsFuel_occurrenceBoundExtends thenSuccess
      ).nodesBelowNextOccurrence
        ((Detail.inferExprFuel_occurrenceBoundExtends conditionSuccess
          ).nodesBelowNextOccurrence allocatedInvariant.nodesBelow)
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    conditionProperties.2.1 thenProperties.1
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties
    restoredProperties.2 signatureFormation functionsCanonical
    elseReturnBelow elseSuccess
  have elseSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have elseInputSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseSubstitutionExtension elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    TypeSystem.Substitution.SemanticallyExtends.trans
      elseInputSubstitutionExtension restoredProperties.1.substitution_extends
  have conditionInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized conditionState semanticContext :=
    allocatedInvariant.inferExprFuel conditionSuccess signatureFormation
      functionsCanonical (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool]) conditionSubstitutionExtension
  have conditionOperational := (operational.allocateStatementId allocationEq).ofExpression conditionSuccess conditionProperties.1.next_le
  have elseInputInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope)
      semanticContext :=
    conditionInvariant.restoreLexicalScope thenProperties.1 thenBelow
      (Detail.inferStatementsFuel_nextLocal_le thenSuccess)
      elseInputSubstitutionExtension
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [State.restoreLexicalScope] using
      elseInputSubstitutionExtension
  have elseIntegerLiteralsSubset :
      elseResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have thenIntegerLiteralsSubset :
      thenResult.state.integerLiterals ⊆ result.state.integerLiterals := by
    have throughElse : thenResult.state.integerLiterals ⊆
        elseResult.state.integerLiterals := by
      simpa [State.restoreLexicalScope] using
        (Detail.inferStatementsFuel_integerLiterals_subset elseSuccess)
    exact List.Subset.trans throughElse elseIntegerLiteralsSubset
  have thenCovered : ∀ child, child ∈ thenResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  obtain ⟨thenFinal, thenFacts, thenInvariant, _thenActual, _thenOperational, thenTyping,
      thenAgreement⟩ :=
    branchSound thenSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters conditionInvariant actual conditionOperational returnAdmissible thenSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (thenSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore thenSourceExtension)
      (List.Subset.trans thenIntegerPatternsSubset integerPatternsSubset)
      (List.Subset.trans thenIntegerLiteralsSubset integerLiteralsSubset)
      (List.Subset.trans thenRequirementsSubset requirementsSubset)
      thenCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have elseIntegerPatternsSubset' :=
    List.Subset.trans elseIntegerPatternsSubset integerPatternsSubset
  have elseIntegerLiteralsSubset' :=
    List.Subset.trans elseIntegerLiteralsSubset integerLiteralsSubset
  have elseRequirementsSubset' :=
    List.Subset.trans elseRequirementsSubset requirementsSubset
  have elseCovered : ∀ child, child ∈ elseResult.statements →
      TemplateScopeCovered finalized.typedSource semanticContext
        (.statement child) := by
    intro child member
    have childReference : (.statement child : NodeId) ∈
        (StatementForm.ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)).references := by
      simp [StatementForm.references, member]
    exact rooted_statement_child_covered
      contains childReference resultExtension parentCovered
      resources.graph_closed (fun _ membership => membership)
  have elseOperational : ActualStateInvariant
      (thenResult.state.restoreLexicalScope conditionState.lexicalScope) (evidenceState.toTypedSource roots) := by
    obtain ⟨pending, ledger⟩ := conditionOperational.ledger
    refine ⟨⟨pending, ((actualLedgerFamily fuel).statements.statements thenSuccess ledger).restoreLexicalScope _⟩,
      conditionOperational.origins.congr_localBinders rfl, ?_, conditionOperational.sourceMonomorphic⟩
    exact activeQuantifiersBelowNext_transport conditionOperational.quantifiersBelow rfl thenProperties.1.next_le
  obtain ⟨elseFinal, elseFacts, elseInvariant, _elseActual, _elseOperational, elseTyping,
      elseAgreement⟩ :=
    branchSound elseSuccess resources interfaces signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters elseInputInvariant actual elseOperational returnAdmissible elseSubstitutionExtension
      (fun child _ => SubtreePreserved.ofTypingSourceExtends
        (elseSourceExtension.applySubstitution finalized.substitution))
      (fun child member => (rawResultExtension.child
        (directChild_statement_reference contains (by simp [StatementForm.references, member]))).monoBefore elseSourceExtension)
      elseIntegerPatternsSubset' elseIntegerLiteralsSubset'
      elseRequirementsSubset' elseCovered (fun child member => parentActualCovered.preserved_statement_reference
        contains resultExtension (by simp [StatementForm.references, member]))
  have branch : ∃ finalContext facts,
      ActiveLocalContextInvariant result.state finalized.substitution
        finalContext ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
    have conditionTyping := conditionSound conditionSuccess
    have conditionEq : finalized.substitution.apply inferredCondition.type =
        .bool := by
      simpa using Detail.inferExprFuel_expected_type_apply_eq
        conditionSuccess conditionSubstitutionExtension
    subst result
    refine ⟨semanticContext, {
        type := if thenFacts.sawReturn && elseFacts.sawReturn then
          finalized.substitution.apply expectedReturn
        else
          .unit
        hasValue := thenFacts.sawReturn && elseFacts.sawReturn
        sawReturn := thenFacts.sawReturn && elseFacts.sawReturn
        control := thenFacts.control.branches elseFacts.control
      }, conditionInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact ifWithElseStatementHasType_afterSubstitution contains
        conditionTyping conditionEq thenTyping elseTyping thenAgreement
        elseAgreement elseSubstitutionExtension
    · exact StatementResultMatchesFactsAfterSubstitution.ifWithElse
        thenAgreement elseAgreement elseSubstitutionExtension id _
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation
      result.state := by
    apply activeSchemeQuantifierIsolation_transport
      conditionInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
  obtain ⟨finalContext, facts, finalInvariant, typing, agreement⟩ :=
    RecursiveStatementInvariant.close_statement_branch initialInvariant
      success signatureFormation functionsCanonical
      (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
      resultSubstitutionExtension resultSchemeIsolation branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have conditionBinders := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq conditionSuccess)
    have allocationBinders := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.restoreLexicalScope, State.recordNode, State.lexicalScope] using conditionBinders.trans allocationBinders
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready signatureFormation
    functionsCanonical initialInvariant.returnBelow success
  exact ⟨finalContext, facts, finalInvariant, actual.of_statement typing,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, typing, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementConditionSoundness
/-!
Actual-success condition-expression typing for statement branches.  The
condition is checked in the completed parent statement source; the proof
tracks its precise inference state through the body and the final record.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The condition of a successful `while` statement is typed by the actual
expression-inference call, with all evidence and template coverage inherited
from its enclosing completed statement. -/
theorem actualInferStatementFuel_success_whileLoop_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, bodyResult,
      actualConditionSuccess, bodySuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_whileLoop_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨actualConditionState, actualBodyResult,
      ⟨actualCondition', actualConditionSuccess'⟩, actualBodySuccess',
      conditionBelow, bodySourceExtension,
      bodyPatternsSubset, bodyRequirementsSubset⟩ :=
    inferStatementFuel_success_whileLoop_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : actualConditionState = conditionState := by
    rw [conditionSuccess] at actualConditionSuccess'
    exact (congrArg Prod.snd
      (Except.ok.inj actualConditionSuccess')).symm
  subst actualConditionState
  have bodyResultEq : actualBodyResult = bodyResult := by
    rw [bodySuccess] at actualBodySuccess'
    exact (Except.ok.inj actualBodySuccess').symm
  subst actualBodyResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans bodySubstitutionExtension
      bodyProperties.1.substitution_extends
  have conditionToBody : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (bodyResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends bodySuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToBody.trans bodySourceExtension
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .whileLoop inferredCondition.id bodyResult.statements
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement containsRaw
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources interfaces
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) actual (operational.allocateStatementId allocationEq) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (by
      intro type member
      have same : type = .bool := Option.some.inj member.symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initialInvariant).typeParameterBinders
        (by simpa only [ownerEq, parametersEq] using signatureParameters)))
    (SubtreePreserved.ofTypingSourceExtends
      (conditionToParent.applySubstitution finalized.substitution))
    ((rawResultExtension.child (directChild_statement_reference containsRaw
      (by simp [StatementForm.references]))).monoBefore conditionToParent)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset bodySuccess)
        bodyPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
        bodyLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset bodySuccess)
        bodyRequirementsSubset) requirementsSubset)
    conditionCovered
    (parentActualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]))

/-- The with-else `if` condition remains typed after both branch traversals.
The else branch starts from the restored condition scope, but the occurrence
and requirement ledgers continue to extend the original condition state. -/
theorem actualInferStatementFuel_success_ifWithElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, thenResult, elseResult,
      actualConditionSuccess, thenSuccess, elseSuccess, resultEq,
      containsRaw⟩ :=
    inferStatementFuel_success_ifWithElse_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨provenanceConditionState, provenanceThenResult,
      provenanceElseResult, ⟨_, provenanceConditionSuccess⟩,
      provenanceThenSuccess, provenanceElseSuccess, conditionBelow,
      _elseInputBelow, thenSourceExtension, _elseSourceExtension,
      thenPatternsSubset, _elsePatternsSubset,
      thenRequirementsSubset, _elseRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : provenanceConditionState = conditionState := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj provenanceConditionSuccess)).symm
  subst provenanceConditionState
  have thenResultEq : provenanceThenResult = thenResult := by
    rw [thenSuccess] at provenanceThenSuccess
    exact (Except.ok.inj provenanceThenSuccess).symm
  subst provenanceThenResult
  have elseResultEq : provenanceElseResult = elseResult := by
    rw [elseSuccess] at provenanceElseSuccess
    exact (Except.ok.inj provenanceElseSuccess).symm
  subst provenanceElseResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have restoredProperties := State.restoreLexicalScope_inferenceProperties
    conditionProperties.2.1 thenProperties.1
  have elseReturnBelow : expectedReturn.VariablesBelow
      (thenResult.state.restoreLexicalScope
        conditionState.lexicalScope).inference.next :=
    conditionReturnBelow.weaken restoredProperties.1.next_le
  have elseProperties := Detail.inferStatementsFuel_inferenceProperties
    restoredProperties.2 signatureFormation functionsCanonical
    elseReturnBelow elseSuccess
  have elseSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        elseResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have elseInputSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).inference.substitution :=
    Substitution.SemanticallyExtends.trans elseSubstitutionExtension
      elseProperties.1.substitution_extends
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans elseInputSubstitutionExtension
      restoredProperties.1.substitution_extends
  have conditionToThen : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (thenResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends thenSuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToThen.trans thenSourceExtension
  have thenLiteralsSubset : thenResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    have inElseInput : literal ∈
        (thenResult.state.restoreLexicalScope
          conditionState.lexicalScope).integerLiterals := by
      simpa [State.restoreLexicalScope] using member
    have inElse := Detail.inferStatementsFuel_integerLiterals_subset
      elseSuccess inElseInput
    simpa [State.restoreLexicalScope, State.recordNode] using inElse
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements
          (some elseResult.statements)
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement containsRaw
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources interfaces
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) actual (operational.allocateStatementId allocationEq) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (by
      intro type member
      have same : type = .bool := Option.some.inj member.symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initialInvariant).typeParameterBinders
        (by simpa only [ownerEq, parametersEq] using signatureParameters)))
    (SubtreePreserved.ofTypingSourceExtends
      (conditionToParent.applySubstitution finalized.substitution))
    ((rawResultExtension.child (directChild_statement_reference containsRaw
      (by simp [StatementForm.references]))).monoBefore conditionToParent)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset thenSuccess)
        thenPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset thenSuccess)
        thenLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset thenSuccess)
        thenRequirementsSubset) requirementsSubset)
    conditionCovered
    (parentActualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]))

/-- The no-else `if` condition is typed in its enclosing statement source,
using the precise condition-to-then-to-parent execution trace. -/
theorem actualInferStatementFuel_success_ifWithoutElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn
      evidenceState roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultExtension : SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) finalized.typedSource (.statement result.id))
    (rawResultExtension : RawSubtreePreserved
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ∀ {inferredCondition : InferredExpression} {conditionState : State},
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        allocated = .ok (inferredCondition, conditionState) →
      ExpressionHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        semanticContext inferredCondition.id
        (finalized.substitution.apply inferredCondition.type) := by
  intro inferredCondition conditionState conditionSuccess
  obtain ⟨actualCondition, actualConditionState, thenResult,
      actualConditionSuccess, thenSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_ifWithoutElse_facts statementEq allocationEq
      success roots
  rw [conditionSuccess] at actualConditionSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualConditionSuccess).symm
  obtain ⟨provenanceConditionState, provenanceThenResult,
      ⟨_, provenanceConditionSuccess⟩, provenanceThenSuccess,
      conditionBelow, thenSourceExtension, thenPatternsSubset,
      thenRequirementsSubset⟩ :=
    inferStatementFuel_success_ifWithoutElse_child_provenance statementEq
      allocationEq success initialInvariant.nodesBelow roots
  have conditionStateEq : provenanceConditionState = conditionState := by
    rw [conditionSuccess] at provenanceConditionSuccess
    exact (congrArg Prod.snd
      (Except.ok.inj provenanceConditionSuccess)).symm
  subst provenanceConditionState
  have thenResultEq : provenanceThenResult = thenResult := by
    rw [thenSuccess] at provenanceThenSuccess
    exact (Except.ok.inj provenanceThenSuccess).symm
  subst provenanceThenResult
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have conditionReturnBelow :
      expectedReturn.VariablesBelow conditionState.inference.next :=
    allocatedInvariant.returnBelow.weaken conditionProperties.1.next_le
  have thenProperties := Detail.inferStatementsFuel_inferenceProperties
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow thenSuccess
  have thenSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        thenResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans thenSubstitutionExtension
      thenProperties.1.substitution_extends
  have conditionToThen : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (thenResult.state.toTypedSource roots) :=
    inferStatementsFuel_success_typingSourceExtends thenSuccess
      conditionBelow roots
  have conditionToParent : TypingSourceExtends
      (conditionState.toTypedSource roots)
      (result.state.toTypedSource roots) :=
    conditionToThen.trans thenSourceExtension
  have thenLiteralsSubset : thenResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have containsFinal : ContainsStatement finalized.typedSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .ifThen inferredCondition.id thenResult.statements none
      } : StatementNode).applySubstitution finalized.substitution) :=
    resultExtension.containsStatement containsRaw
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources interfaces
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) actual (operational.allocateStatementId allocationEq) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (by
      intro type member
      have same : type = .bool := Option.some.inj member.symm
      subst type
      exact TypeAdmissible.bool ((RecursiveExpressionInvariant.ofStatement initialInvariant).typeParameterBinders
        (by simpa only [ownerEq, parametersEq] using signatureParameters)))
    (SubtreePreserved.ofTypingSourceExtends
      (conditionToParent.applySubstitution finalized.substitution))
    ((rawResultExtension.child (directChild_statement_reference containsRaw
      (by simp [StatementForm.references]))).monoBefore conditionToParent)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerPatterns_subset thenSuccess)
        thenPatternsSubset) integerPatternsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_integerLiterals_subset thenSuccess)
        thenLiteralsSubset) integerLiteralsSubset)
    (List.Subset.trans
      (List.Subset.trans
        (Detail.inferStatementsFuel_requirements_subset thenSuccess)
        thenRequirementsSubset) requirementsSubset)
    conditionCovered
    (parentActualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]))

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementControlSoundness
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem actualInferStatementFuelRootedSoundness_block {fuel : Nat}
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {body : List Syntax.Statement} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .block body →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_block_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered bodySound

theorem actualInferStatementFuelRootedSoundness_whileLoop {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .whileLoop condition body →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_whileLoop_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_whileLoop_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

theorem actualInferStatementFuelRootedSoundness_ifWithoutElse {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .ifThen condition body none →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_ifWithoutElse_of_scoped_body statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_ifWithoutElse_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

theorem actualInferStatementFuelRootedSoundness_ifWithElse {fuel : Nat}
    (expressionSound : ActualInferExprFuelRootedSoundness fuel)
    (bodySound : ActualInferStatementsFuelRootedSoundness fuel) :
  ∀ {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr} {body elseBody : Syntax.Block} {initial : State}
    {result : Detail.StatementResult} {evidenceState : State}
    {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context},
    statement.value = .ifThen condition body (some elseBody) →
    Detail.inferStatementFuel (fuel + 1) inferenceContext statement expectedReturn
      initial = .ok result →
    FinalInferenceResources wholeContext wholeReturn evidenceState roots
      finalized →
    ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource →
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
    ActualContext wholeContext finalized frames semanticContext →
    ActualStateInvariant initial (evidenceState.toTypedSource roots) →
    TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn) →
    finalized.substitution.SemanticallyExtends
      result.state.inference.substitution →
    SubtreePreserved finalized.substitution
      (result.state.toTypedSource roots) semanticSource (.statement result.id) →
    RawSubtreePreserved (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots) (.statement result.id) →
    result.state.integerPatterns ⊆ evidenceState.integerPatterns →
    result.state.integerLiterals ⊆ evidenceState.integerLiterals →
    result.state.requirements ⊆ evidenceState.requirements →
    TemplateScopeCovered finalized.typedSource semanticContext
      (.statement result.id) →
    ActualContext.Covers finalized frames (.statement result.id) →
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized
        result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  intro wholeContext inferenceContext wholeReturn expectedReturn statement condition body elseBody initial result evidenceState roots finalized semanticSource frames semanticContext statementEq success resources interfaces
    signaturesEq ownerEq parametersEq assumptionsEq formation functions catalog canonical invariant actual operational
    returnAdmissible extension _semantic raw patterns literals requirements covered actualCovered
  generalize allocationEq : initial.allocateStatementId = pair
  obtain ⟨id, allocated⟩ := pair
  have final := raw.finalized resources
  exact actualInferStatementFuel_success_ifWithElse_of_scoped_bodies statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational returnAdmissible extension final raw patterns literals requirements
    actualCovered covered (actualInferStatementFuel_success_ifWithElse_condition_scoped statementEq allocationEq success resources interfaces signaturesEq ownerEq parametersEq assumptionsEq formation
    functions catalog canonical invariant actual operational extension final raw patterns literals requirements covered actualCovered expressionSound) bodySound

end Solcore.SourceSemantics.SourceInferenceSoundness
end

section
-- leanmerge: from Solcore.SourceSemantics.SourceInferenceSelectedStatementExpressionSoundness
/-! The actual return and expression children retain their initializer scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem actualInferStatementFuel_expression_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (_returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (rawEvidenceExtension : RawSubtreePreserved
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots) (.statement result.id))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_expression_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  obtain ⟨actualInferred, actualState, actualSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq success roots
  rw [childSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have childSubstitutionEq : childState.inference.substitution = result.state.inference.substitution := by
    simp [resultEq, State.recordNode]
  have childParentExtension := provenance.sourceExtension.applySubstitution finalized.substitution
  have childEdge : DirectChild (result.state.toTypedSource roots) (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have rawChildEvidenceExtension := (rawEvidenceExtension.child childEdge).monoBefore provenance.sourceExtension
  have childPatternsSubset := List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset
  have childLiteralsSubset : childState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa [resultEq, State.recordNode] using resultLiteralsSubset
  have childRequirementsSubset := List.Subset.trans provenance.requirementsSubset resultRequirementsSubset
  have containsFinal := (rawEvidenceExtension.finalized resources).containsStatement containsRaw
  have childCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  have childActualCovered : ActualContext.Covers finalized frames (.expression inferred.id) :=
    parentActualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
  have allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext :=
    RecursiveExpressionInvariant.ofStatement
      (initialInvariant.allocateStatementId allocationEq)
  have childSubstitutionExtension : finalized.substitution.SemanticallyExtends
      childState.inference.substitution := by
    rw [childSubstitutionEq]
    exact resultSubstitutionExtension
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources interfaces childSubstitutionExtension
      signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant actual (operational.allocateStatementId allocationEq)
      (by simp) (by simp) (SubtreePreserved.ofTypingSourceExtends childParentExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
      childActualCovered
  obtain ⟨facts, active, statementType, agreement⟩ :=
    inferStatementFuel_success_expression_sound statementEq allocationEq
      success initialInvariant.active roots (by
        intro actualInferred actualState actualSuccess
        have pairEq : (actualInferred, actualState) =
            (inferred, childState) := by
          rw [childSuccess] at actualSuccess
          exact (Except.ok.inj actualSuccess).symm
        cases pairEq
        exact typed)
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocationScope := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using childEq.trans allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, facts, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

/-- The value-return branch sends its actual child to the scoped expression
theorem with the function return type as expected type. -/
theorem actualInferStatementFuel_returnValue_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {frames : List InitializedLetBinding}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
    (interfaces : ExecutableCoercionInterfaces.SourceInterfaces wholeContext.signatures
      finalized.solvedRequirements finalized.typedSource)
    (signaturesEq : inferenceContext.signatures = wholeContext.signatures)
    (ownerEq : inferenceContext.scope.genericOwner =
      wholeContext.scope.genericOwner)
    (parametersEq : inferenceContext.typeParameters =
      wholeContext.typeParameters)
    (assumptionsEq : inferenceContext.assumptions = wholeContext.assumptions)
    (signatureFormation : ProgramSignatureFormationValidated
      inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (catalog : SignatureCatalogWellFormed inferenceContext.signatures)
    (signatureParameters : SignatureParametersWellFormed
      inferenceContext.scope.genericOwner inferenceContext.typeParameters)
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (actual : ActualContext wholeContext finalized frames semanticContext)
    (operational : ActualStateInvariant initial (evidenceState.toTypedSource roots))
    (_returnAdmissible : TypeAdmissible semanticContext (finalized.substitution.apply expectedReturn))
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (rawEvidenceExtension : RawSubtreePreserved
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots) (.statement result.id))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (parentActualCovered : ActualContext.Covers finalized frames (.statement result.id))
    (expressionSound : ActualInferExprFuelRootedSoundness fuel) :
    ∃ finalContext facts,
      RecursiveStatementInvariant wholeContext expectedReturn finalized result.state finalContext ∧
      ActualContext wholeContext finalized frames finalContext ∧
      ActualStateInvariant result.state (evidenceState.toTypedSource roots) ∧
      StatementHasType
        ((result.state.toTypedSource roots).applySubstitution
          finalized.substitution)
        { returnType := finalized.substitution.apply expectedReturn
          loopDepth := inferenceContext.loopDepth }
        semanticContext result.id finalContext facts ∧
      StatementResultMatchesFactsAfterSubstitution finalized.substitution
        result facts := by
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance statementEq allocationEq
      success initialInvariant.nodesBelow roots
  obtain ⟨actualInferred, actualState, actualSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq success roots
  rw [childSuccess] at actualSuccess
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj actualSuccess).symm
  have childSubstitutionEq : childState.inference.substitution = result.state.inference.substitution := by
    simp [resultEq, State.recordNode]
  have childParentExtension := provenance.sourceExtension.applySubstitution finalized.substitution
  have childEdge : DirectChild (result.state.toTypedSource roots) (.statement result.id) (.expression inferred.id) :=
    directChild_statement_reference containsRaw (by simp [StatementForm.references])
  have rawChildEvidenceExtension := (rawEvidenceExtension.child childEdge).monoBefore provenance.sourceExtension
  have childPatternsSubset := List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset
  have childLiteralsSubset : childState.integerLiterals ⊆ evidenceState.integerLiterals := by
    simpa [resultEq, State.recordNode] using resultLiteralsSubset
  have childRequirementsSubset := List.Subset.trans provenance.requirementsSubset resultRequirementsSubset
  have containsFinal := (rawEvidenceExtension.finalized resources).containsStatement containsRaw
  have childCovered : TemplateScopeCovered finalized.typedSource semanticContext (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references]
  have childActualCovered : ActualContext.Covers finalized frames (.expression inferred.id) :=
    parentActualCovered.statement_reference containsFinal (by
      simp [StatementNode.applySubstitution, StatementForm.applySubstitution, StatementForm.references])
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have childExpectedBelow : ∀ expectedType ∈ (some expectedReturn : Option Ty),
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    simp only [Option.mem_def] at member
    cases member
    exact allocatedInvariant.returnBelow
  have childSubstitutionExtension : finalized.substitution.SemanticallyExtends
      childState.inference.substitution := by
    rw [childSubstitutionEq]
    exact resultSubstitutionExtension
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources interfaces childSubstitutionExtension
      signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters
      (RecursiveExpressionInvariant.ofStatement allocatedInvariant) actual
      (operational.allocateStatementId allocationEq) childExpectedBelow
      (by intro type member; cases Option.mem_def.mp member; exact _returnAdmissible) (SubtreePreserved.ofTypingSourceExtends childParentExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
      childActualCovered
  have branch := inferStatementFuel_success_returnValue_sound statementEq
    allocationEq success initialInvariant.active resultSubstitutionExtension
    roots (by
      intro actualInferred actualState actualSuccess
      have pairEq : (actualInferred, actualState) =
          (inferred, childState) := by
        rw [childSuccess] at actualSuccess
        exact (Except.ok.inj actualSuccess).symm
      cases pairEq
      exact typed)
  obtain ⟨active, statementType, agreement⟩ := branch
  have bindersEq : result.state.localBinders = initial.localBinders := by
    have childEq := congrArg LexicalScope.binders (Detail.inferExprFuel_success_lexicalScope_eq childSuccess)
    have allocationScope := congrArg LexicalScope.binders (Detail.allocateStatementId_success_lexicalScope allocationEq)
    simpa only [resultEq, State.recordNode, State.lexicalScope] using childEq.trans allocationScope
  have properties := Detail.inferStatementFuel_inferenceProperties initialInvariant.ready
    signatureFormation functionsCanonical initialInvariant.returnBelow success
  have finalInvariant := initialInvariant.of_statement_typing success signatureFormation functionsCanonical
    active (inferStatementFuel_preserves_localBindersBelowNextLocal initialInvariant.bindersBelow success)
    resultSubstitutionExtension (activeSchemeQuantifierIsolation_transport initialInvariant.schemeIsolation bindersEq)
    statementType
  exact ⟨semanticContext, _, finalInvariant, actual,
    operational.ofStatementPreservingBinders success bindersEq properties.1.next_le, statementType, agreement⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
end
