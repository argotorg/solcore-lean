import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences
import Solcore.SourceSemantics.SourceInferenceSelectedStatementState

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
