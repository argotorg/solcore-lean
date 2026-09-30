import Solcore.SourceSemantics.SourceInferenceStatementAtomicSoundness
import Solcore.SourceSemantics.SourceInferenceStatementExpressionSoundness
import Solcore.SourceSemantics.SourceInferenceAssignmentStatementBridge
import Solcore.SourceSemantics.SourceInferenceStatementConditionSoundness
import Solcore.SourceSemantics.SourceInferenceStatementForLoopScopedSoundness

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
