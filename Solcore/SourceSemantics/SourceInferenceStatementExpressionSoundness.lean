import Solcore.SourceSemantics.SourceInferenceStatementAtomicSoundness
import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness

/-!
Actual-child resources for expression statements and value returns.  The
statement dispatcher can feed these facts to a recursive expression theorem
without assuming soundness of an unrelated expression computation.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The expression child's actual inference trace is retained under both the
parent's semantic source and the whole finalization evidence source. -/
theorem inferStatementFuel_expression_child_resources
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool} {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {roots : List NodeId}
    {semanticSource coverageSource : TypedSource}
    {target : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      coverageSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource) :
    ∃ inferred childState,
      Detail.inferExprFuel fuel inferenceContext expression none allocated =
        .ok (inferred, childState) ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((childState.toTypedSource roots).applySubstitution outer)
        semanticSource ∧
      TypingSourceExtends (childState.toTypedSource roots)
        (evidenceState.toTypedSource roots) ∧
      childState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      childState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      childState.requirements ⊆ evidenceState.requirements ∧
      TemplateScopeCovered coverageSource target
        (.expression inferred.id) := by
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_expression_child_provenance statementEq
      allocationEq success initialBelow roots
  obtain ⟨inferred', childState', childSuccess', resultEq, containsRaw⟩ :=
    inferStatementFuel_success_expression_facts statementEq allocationEq
      success roots
  rw [childSuccess] at childSuccess'
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj childSuccess').symm
  have resultCoverageExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    resultSemanticExtension.trans semanticCoverageExtension
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .expression inferred.id trailingSemicolon
      } : StatementNode).applySubstitution outer) :=
    resultCoverageExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have childCovered : TemplateScopeCovered coverageSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  refine ⟨inferred, childState, childSuccess, provenance.initialBelow,
    provenance.sourceExtension.applySubstitution outer |>.trans
      resultSemanticExtension,
    provenance.sourceExtension.trans rawEvidenceExtension,
    List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset,
    ?_,
    List.Subset.trans provenance.requirementsSubset resultRequirementsSubset,
    childCovered⟩
  simpa [resultEq, State.recordNode] using resultLiteralsSubset

/-- The value-return child's actual inference trace supplies the same
semantic/evidence transport and its direct-child coverage. -/
theorem inferStatementFuel_returnValue_child_resources
    {fuel : Nat} {inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {expectedReturn : Ty}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult}
    {outer : Substitution} {roots : List NodeId}
    {semanticSource coverageSource : TypedSource}
    {target : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (initialBelow : initial.NodesBelowNextOccurrence)
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      coverageSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered coverageSource target
      (.statement result.id))
    (closed : OccurrenceGraphClosed coverageSource) :
    ∃ inferred childState,
      Detail.inferExprFuel fuel inferenceContext value (some expectedReturn)
        allocated = .ok (inferred, childState) ∧
      allocated.NodesBelowNextOccurrence ∧
      TypingSourceExtends
        ((childState.toTypedSource roots).applySubstitution outer)
        semanticSource ∧
      TypingSourceExtends (childState.toTypedSource roots)
        (evidenceState.toTypedSource roots) ∧
      childState.integerPatterns ⊆ evidenceState.integerPatterns ∧
      childState.integerLiterals ⊆ evidenceState.integerLiterals ∧
      childState.requirements ⊆ evidenceState.requirements ∧
      TemplateScopeCovered coverageSource target
        (.expression inferred.id) := by
  obtain ⟨inferred, childState, childSuccess, provenance⟩ :=
    inferStatementFuel_success_returnValue_child_provenance statementEq
      allocationEq success initialBelow roots
  obtain ⟨inferred', childState', childSuccess', resultEq, containsRaw⟩ :=
    inferStatementFuel_success_returnValue_facts statementEq allocationEq
      success roots
  rw [childSuccess] at childSuccess'
  obtain ⟨rfl, rfl⟩ := (Except.ok.inj childSuccess').symm
  have resultCoverageExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution outer)
      coverageSource :=
    resultSemanticExtension.trans semanticCoverageExtension
  have containsFinal : ContainsStatement coverageSource result.id
      (({
        id := result.id
        span := statement.span
        type := result.type
        form := .returnStmt (some inferred.id)
      } : StatementNode).applySubstitution outer) :=
    resultCoverageExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution outer
        containsRaw)
  have childCovered : TemplateScopeCovered coverageSource target
      (.expression inferred.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  refine ⟨inferred, childState, childSuccess, provenance.initialBelow,
    provenance.sourceExtension.applySubstitution outer |>.trans
      resultSemanticExtension,
    provenance.sourceExtension.trans rawEvidenceExtension,
    List.Subset.trans provenance.integerPatternsSubset resultPatternsSubset,
    ?_,
    List.Subset.trans provenance.requirementsSubset resultRequirementsSubset,
    childCovered⟩
  simpa [resultEq, State.recordNode] using resultLiteralsSubset

/-- The actual expression child is typed by the scoped expression theorem in
the enclosing statement's local source, then the existing statement
constructor discharges the parent typing. -/
theorem inferStatementFuel_expression_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {expression : Syntax.Expr}
    {trailingSemicolon : Bool}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .expression expression trailingSemicolon)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
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
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      finalized.typedSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∃ finalContext facts,
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
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, _allocatedBelow,
      childParentExtension, rawChildEvidenceExtension,
      childPatternsSubset, childLiteralsSubset, childRequirementsSubset,
      childCovered⟩ :=
    inferStatementFuel_expression_child_resources statementEq allocationEq
      success initialInvariant.nodesBelow (TypingSourceExtends.refl
        parentSource) (resultSemanticExtension.trans
        semanticCoverageExtension) rawEvidenceExtension resultPatternsSubset
      resultLiteralsSubset resultRequirementsSubset parentCovered
      resources.graph_closed
  have allocatedInvariant : RecursiveExpressionInvariant wholeContext finalized
      allocated semanticContext :=
    RecursiveExpressionInvariant.ofStatement
      (initialInvariant.allocateStatementId allocationEq)
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters allocatedInvariant (by simp) childParentExtension
      (resultSemanticExtension.trans semanticCoverageExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
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
  exact ⟨semanticContext, facts, active, statementType, agreement⟩

/-- The value-return branch sends its actual child to the scoped expression
theorem with the function return type as expected type. -/
theorem inferStatementFuel_returnValue_scopedBranch
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {value : Syntax.Expr}
    {initial allocated evidenceState : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticSource : TypedSource}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .returnStmt (some value))
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext statement
      expectedReturn initial = .ok result)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState
      roots finalized)
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
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (resultSemanticExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) semanticSource)
    (semanticCoverageExtension : TypingSourceExtends semanticSource
      finalized.typedSource)
    (rawEvidenceExtension : TypingSourceExtends
      (result.state.toTypedSource roots) (evidenceState.toTypedSource roots))
    (resultPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (resultLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (resultRequirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
    ∃ finalContext facts,
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
  let parentSource :=
    (result.state.toTypedSource roots).applySubstitution
      finalized.substitution
  obtain ⟨inferred, childState, childSuccess, _allocatedBelow,
      childParentExtension, rawChildEvidenceExtension,
      childPatternsSubset, childLiteralsSubset, childRequirementsSubset,
      childCovered⟩ :=
    inferStatementFuel_returnValue_child_resources statementEq allocationEq
      success initialInvariant.nodesBelow (TypingSourceExtends.refl
        parentSource) (resultSemanticExtension.trans
        semanticCoverageExtension) rawEvidenceExtension resultPatternsSubset
      resultLiteralsSubset resultRequirementsSubset parentCovered
      resources.graph_closed
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have childExpectedBelow : ∀ expectedType ∈ (some expectedReturn : Option Ty),
      expectedType.VariablesBelow allocated.inference.next := by
    intro expectedType member
    simp only [Option.mem_def] at member
    cases member
    exact allocatedInvariant.returnBelow
  have typed : ExpressionHasType parentSource semanticContext inferred.id
      (finalized.substitution.apply inferred.type) :=
    expressionSound childSuccess resources signaturesEq ownerEq parametersEq
      assumptionsEq signatureFormation functionsCanonical catalog
      signatureParameters
      (RecursiveExpressionInvariant.ofStatement allocatedInvariant)
      childExpectedBelow childParentExtension
      (resultSemanticExtension.trans semanticCoverageExtension)
      rawChildEvidenceExtension childPatternsSubset childLiteralsSubset
      childRequirementsSubset childCovered
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
  exact ⟨semanticContext, _, branch⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
