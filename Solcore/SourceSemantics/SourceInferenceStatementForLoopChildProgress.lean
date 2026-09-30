import Solcore.SourceSemantics.SourceInferenceStatementForLoopResources

/-!
The four successful traversals of a `for` statement are source ordered.  This
module exposes their intermediate substitution and literal-ledger resources
without requiring a semantic proof for any of the children.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- Finalization extends the substitutions at every actual `for` child
boundary.  Every child's integer-literal ledger is also retained in the
completed statement, including the post-header traversal that runs after
restoring the initializer's lexical scope. -/
theorem inferStatementFuel_success_forLoop_child_progress
    {fuel : Nat}
    {wholeContext inferenceContext : Frontend.SourceInference.Context}
    {statement : Syntax.Statement} {headerSpan : Syntax.SourceSpan}
    {initializer post : List Syntax.ForItem} {condition : Syntax.Expr}
    {body : Syntax.Block} {expectedReturn : Ty}
    {initial allocated : State} {id : StatementId}
    {result : Detail.StatementResult}
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
      result.state.inference.substitution) :
    ∃ initializerResult inferredCondition conditionState bodyResult postResult,
      Detail.inferForItemsFuel fuel inferenceContext initializer allocated =
        .ok initializerResult ∧
      Detail.inferExprFuel fuel inferenceContext condition (some .bool)
        initializerResult.state = .ok (inferredCondition, conditionState) ∧
      Detail.inferStatementsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 }
        body.value expectedReturn conditionState = .ok bodyResult ∧
      Detail.inferForItemsFuel fuel
        { inferenceContext with
          loopDepth := inferenceContext.loopDepth + 1 } post
        (bodyResult.state.restoreLexicalScope
          initializerResult.state.lexicalScope) = .ok postResult ∧
      finalized.substitution.SemanticallyExtends
        initializerResult.state.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution ∧
      finalized.substitution.SemanticallyExtends
        postResult.state.inference.substitution ∧
      initializerResult.state.integerLiterals ⊆
        result.state.integerLiterals ∧
      conditionState.integerLiterals ⊆ result.state.integerLiterals ∧
      bodyResult.state.integerLiterals ⊆ result.state.integerLiterals ∧
      postResult.state.integerLiterals ⊆ result.state.integerLiterals := by
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, _⟩ :=
    inferStatementFuel_success_forLoop_facts statementEq allocationEq
      success []
  have allocatedInvariant : RecursiveStatementInvariant wholeContext
      expectedReturn finalized allocated semanticContext :=
    initialInvariant.allocateStatementId allocationEq
  have initializerProperties := Detail.inferForItemsFuel_inferenceProperties
    allocatedInvariant.ready signatureFormation functionsCanonical
    initializerSuccess
  have conditionProperties := Detail.inferExprFuel_inferenceProperties
    initializerProperties.2 signatureFormation functionsCanonical
    (by
      intro expected member
      simp only [Option.mem_def] at member
      injection member with expectedEq
      subst expected
      simp [Ty.bool]) conditionSuccess
  have initializerReturnBelow : expectedReturn.VariablesBelow
      initializerResult.state.inference.next :=
    allocatedInvariant.returnBelow.weaken initializerProperties.1.next_le
  have conditionReturnBelow : expectedReturn.VariablesBelow
      conditionState.inference.next :=
    initializerReturnBelow.weaken conditionProperties.1.next_le
  have bodyProperties := Detail.inferStatementsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    conditionProperties.2.1 signatureFormation functionsCanonical
    conditionReturnBelow bodySuccess
  have postInputProperties := State.restoreLexicalScope_inferenceProperties
    initializerProperties.2
    (conditionProperties.1.trans bodyProperties.1)
  have postProperties := Detail.inferForItemsFuel_inferenceProperties
    (context := { inferenceContext with
      loopDepth := inferenceContext.loopDepth + 1 })
    postInputProperties.2 signatureFormation functionsCanonical postSuccess
  have postSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        postResult.state.inference.substitution := by
    simpa [resultEq, State.restoreLexicalScope, State.recordNode] using
      resultSubstitutionExtension
  have bodySubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        bodyResult.state.inference.substitution := by
    have postInputSubstitutionExtension :=
      Substitution.SemanticallyExtends.trans postSubstitutionExtension
        postProperties.1.substitution_extends
    simpa [State.restoreLexicalScope] using postInputSubstitutionExtension
  have conditionSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        conditionState.inference.substitution :=
    Substitution.SemanticallyExtends.trans bodySubstitutionExtension
      bodyProperties.1.substitution_extends
  have initializerSubstitutionExtension :
      finalized.substitution.SemanticallyExtends
        initializerResult.state.inference.substitution :=
    Substitution.SemanticallyExtends.trans conditionSubstitutionExtension
      conditionProperties.1.substitution_extends
  have postLiteralsSubset : postResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    rw [resultEq]
    intro literal member
    simpa [State.restoreLexicalScope, State.recordNode] using member
  have bodyLiteralsSubset : bodyResult.state.integerLiterals ⊆
      result.state.integerLiterals := by
    apply List.Subset.trans ?_ postLiteralsSubset
    intro literal member
    exact Detail.inferForItemsFuel_integerLiterals_subset postSuccess
      (by simpa [State.restoreLexicalScope] using member)
  have conditionLiteralsSubset : conditionState.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferStatementsFuel_integerLiterals_subset bodySuccess)
      bodyLiteralsSubset
  have initializerLiteralsSubset : initializerResult.state.integerLiterals ⊆
      result.state.integerLiterals :=
    List.Subset.trans
      (Detail.inferExprFuel_integerLiterals_subset conditionSuccess)
      conditionLiteralsSubset
  exact ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, initializerSubstitutionExtension,
    conditionSubstitutionExtension, bodySubstitutionExtension,
    postSubstitutionExtension, initializerLiteralsSubset,
    conditionLiteralsSubset, bodyLiteralsSubset, postLiteralsSubset⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
