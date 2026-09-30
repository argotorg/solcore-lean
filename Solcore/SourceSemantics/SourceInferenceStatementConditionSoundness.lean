import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness
import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-!
Actual-success condition-expression typing for statement branches.  The
condition is checked in the completed parent statement source; the proof
tracks its precise inference state through the body and the final record.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

/-- The condition of a successful `while` statement is typed by the actual
expression-inference call, with all evidence and template coverage inherited
from its enclosing completed statement. -/
theorem inferStatementFuel_success_whileLoop_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .whileLoop condition body)
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
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
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
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
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

/-- The with-else `if` condition remains typed after both branch traversals.
The else branch starts from the restored condition scope, but the occurrence
and requirement ledgers continue to extend the original condition state. -/
theorem inferStatementFuel_success_ifWithElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody elseBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .ifThen condition thenBody (some elseBody))
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
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
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
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
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

/-- The no-else `if` condition is typed in its enclosing statement source,
using the precise condition-to-then-to-parent execution trace. -/
theorem inferStatementFuel_success_ifWithoutElse_condition_scoped
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {wholeReturn expectedReturn : Ty}
    {statement : Syntax.Statement} {condition : Syntax.Expr}
    {thenBody : Syntax.Block}
    {initial allocated evidenceState : State}
    {id : StatementId} {result : Detail.StatementResult}
    {roots : List NodeId} {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value = .ifThen condition thenBody none)
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
    (functionsCanonical : ∀ candidate ∈ inferenceContext.signatures.functions,
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
    (resultExtension : TypingSourceExtends
      ((result.state.toTypedSource roots).applySubstitution
        finalized.substitution) finalized.typedSource)
    (rawResultExtension : TypingSourceExtends
      (result.state.toTypedSource roots)
      (evidenceState.toTypedSource roots))
    (integerPatternsSubset : result.state.integerPatterns ⊆
      evidenceState.integerPatterns)
    (integerLiteralsSubset : result.state.integerLiterals ⊆
      evidenceState.integerLiterals)
    (requirementsSubset : result.state.requirements ⊆
      evidenceState.requirements)
    (parentCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.statement result.id))
    (expressionSound : InferExprFuelScopedSoundness fuel) :
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
    resultExtension.containsStatement
      (FlexibleSubstitution.ContainsStatement.applySubstitution
        finalized.substitution containsRaw)
  have conditionCovered : TemplateScopeCovered finalized.typedSource
      semanticContext (.expression inferredCondition.id) := by
    apply TemplateScopeCovered.statementExpressionChild_of_noBindings_and_reference
      parentCovered resources.graph_closed containsFinal
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        statementInitializedLetBindings]
    · simp [StatementNode.applySubstitution, StatementForm.applySubstitution,
        StatementForm.references]
  exact expressionSound conditionSuccess resources
    conditionSubstitutionExtension signaturesEq ownerEq parametersEq
    assumptionsEq signatureFormation functionsCanonical catalog
    signatureParameters (RecursiveExpressionInvariant.ofStatement
      allocatedInvariant) (by
        intro expected member
        simp only [Option.mem_def] at member
        injection member with expectedEq
        subst expected
        simp [Ty.bool])
    (conditionToParent.applySubstitution finalized.substitution)
    resultExtension
    (conditionToParent.trans rawResultExtension)
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

end Solcore.SourceSemantics.SourceInferenceSoundness
