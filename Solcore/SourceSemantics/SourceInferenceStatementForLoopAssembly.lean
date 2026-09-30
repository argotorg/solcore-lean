import Solcore.SourceSemantics.SourceInferenceRecursiveSoundness

/-!
The `for` statement's non-recursive semantic assembly.  The child-typing
premise is indexed by the actual successful initializer, condition, body,
and post traversals of one successful parent; it does not assert anything
about unrelated child computations.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Assemble a scoped `for` statement once its actual four child traversals
have been typed in the completed parent source.  The loop's lexical binders
are restored before returning to the enclosing semantic context. -/
theorem inferStatementFuel_success_forLoop_of_actual_typed_children
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {expectedReturn : Ty}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result}
    {semanticContext : SourceSemantics.Context}
    (statementEq : statement.value =
      .forLoop headerSpan initializer condition post body)
    (allocationEq : initial.allocateStatementId = (id, allocated))
    (success : Detail.inferStatementFuel (fuel + 1) inferenceContext
      statement expectedReturn initial = .ok result)
    (signatureFormation :
      ProgramSignatureFormationValidated inferenceContext.signatures)
    (functionsCanonical : ∀ candidate ∈
      inferenceContext.signatures.functions,
      candidate.scheme.body = .function
        (Ty.productMany candidate.parameterTypes)
        (Ty.productMany candidate.returnTypes))
    (initialInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized initial semanticContext)
    (resultSubstitutionExtension : finalized.substitution.SemanticallyExtends
      result.state.inference.substitution)
    (typedChildren :
      ∀ {initializerResult : Detail.InferredForItems}
        {inferredCondition : InferredExpression}
        {conditionState : State} {bodyResult : Detail.BlockResult}
        {postResult : Detail.InferredForItems},
        Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
          .ok initializerResult →
        Detail.inferExprFuel fuel inferenceContext condition (some .bool)
          initializerResult.state = .ok (inferredCondition, conditionState) →
        Detail.inferStatementsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 }
          body.value expectedReturn conditionState = .ok bodyResult →
        Detail.inferForItemsFuel fuel
          { inferenceContext with
            loopDepth := inferenceContext.loopDepth + 1 } post
          (bodyResult.state.restoreLexicalScope
            initializerResult.state.lexicalScope) = .ok postResult →
        ∃ loopContext bodyFinal bodyFacts postContext,
          ForItemsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            { returnType := finalized.substitution.apply expectedReturn
              loopDepth := inferenceContext.loopDepth }
            semanticContext
            (initializerResult.items.map
              (ForItemForm.applySubstitution finalized.substitution))
            loopContext ∧
          ExpressionHasType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            loopContext inferredCondition.id .bool ∧
          StatementsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            ({ returnType := finalized.substitution.apply expectedReturn
               loopDepth := inferenceContext.loopDepth } :
              ControlContext).enterLoop
            loopContext bodyResult.statements bodyFinal bodyFacts ∧
          ForItemsHaveType
            ((result.state.toTypedSource roots).applySubstitution
              finalized.substitution)
            ({ returnType := finalized.substitution.apply expectedReturn
               loopDepth := inferenceContext.loopDepth } :
              ControlContext).enterLoop
            loopContext
            (postResult.items.map
              (ForItemForm.applySubstitution finalized.substitution))
            postContext) :
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
        result facts := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, contains⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq success
      roots
  obtain ⟨loopContext, bodyFinal, bodyFacts, postContext,
    initializerTyping, conditionTyping, bodyTyping, postTyping⟩ :=
    typedChildren initializerSuccess conditionSuccess bodySuccess postSuccess
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have resultSchemeIsolation : ActiveSchemeQuantifierIsolation result.state := by
    apply activeSchemeQuantifierIsolation_transport
      allocatedInvariant.schemeIsolation
    simp [resultEq, State.restoreLexicalScope, State.recordNode,
      State.lexicalScope]
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
    subst result
    refine ⟨semanticContext, {
      type := .unit
      hasValue := false
      sawReturn := false
      control := .loop bodyFacts.control
    }, allocatedInvariant.active.restoreLexicalScope_recordNode _, ?_, ?_⟩
    · exact forLoopStatementHasType_afterSubstitution contains
        initializerTyping conditionTyping bodyTyping postTyping
    · exact StatementResultMatchesFactsAfterSubstitution.forLoop
        finalized.substitution bodyFacts id _
  exact RecursiveStatementInvariant.close_statement_branch initialInvariant
    success signatureFormation functionsCanonical
    (inferStatementFuel_preserves_localBindersBelowNextLocal
      initialInvariant.bindersBelow success)
    resultSubstitutionExtension resultSchemeIsolation branch

end Solcore.SourceSemantics.SourceInferenceSoundness
