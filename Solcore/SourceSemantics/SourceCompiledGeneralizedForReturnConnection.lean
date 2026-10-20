import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedForStatement
import Solcore.SourceSemantics.SourceInferenceHeaderSequenceReturnPrivacy

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceStatementsSoundness

/-- The actual ordered initializer supplies return-type privacy for the loop body. -/
theorem statement_for
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursiveItems : ForItemsRootedSoundness selected childFuel)
    (recursiveExpression : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
    {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
    {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
    {initial : State} {result : Detail.StatementResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : statement.value = .forLoop headerSpan initializer condition post body)
    (boundary : StatementBoundary selected (childFuel + 1) inferenceContext statement
      expectedReturn initial result frames target)
    (returnSafe : ∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn)
    (returnAdmissible : TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn))
    (recursiveBody : ∀ {bodyInitial : State} {bodyResult : Detail.BlockResult}
      {loopContext : SourceSemantics.Context},
      (∀ binder ∈ bodyInitial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified bodyInitial expectedReturn) →
      TypeAdmissible loopContext (selected.body.finalized.substitution.apply expectedReturn) →
      StatementsBoundary selected childFuel {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} body.value expectedReturn
        bodyInitial bodyResult frames loopContext →
      StatementsConclusion selected {inferenceContext with loopDepth := inferenceContext.loopDepth + 1} expectedReturn bodyResult frames loopContext) :
    StatementConclusion selected inferenceContext expectedReturn result frames target := by
  apply statement_for_of_initializer_privacy checked recursiveItems recursiveExpression form boundary
    returnSafe returnAdmissible ?_ recursiveBody
  intro actualInitializer actualRun
  obtain ⟨initializerResult, inferredCondition, conditionState, bodyResult,
    postResult, initializerSuccess, conditionSuccess, bodySuccess,
    postSuccess, resultEq, containsRaw⟩ :=
    inferStatementFuel_success_forLoop_facts form rfl boundary.accepted (bodyRoots selected)
  change Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok initializerResult at initializerSuccess
  rw [actualRun] at initializerSuccess
  have same := (Except.ok.inj initializerSuccess).symm
  subst initializerResult
  obtain ⟨progressInitializer, progressCondition, progressConditionState,
    progressBody, progressPost, progressInitializerSuccess,
    progressConditionSuccess, progressBodySuccess, progressPostSuccess,
    initializerExtension, conditionExtension, bodyExtension, postExtension,
    initializerLiterals, conditionLiterals, bodyLiterals, postLiterals⟩ :=
    inferStatementFuel_success_forLoop_child_progress form rfl boundary.accepted
      (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
      boundary.invariant boundary.extension
  change Detail.inferForItemsFuel childFuel inferenceContext initializer initial.allocateStatementId.2 = .ok progressInitializer at progressInitializerSuccess
  rw [actualRun] at progressInitializerSuccess
  have same := (Except.ok.inj progressInitializerSuccess).symm
  subst progressInitializer
  have retained : actualInitializer.items.flatMap ForItemForm.initializedLetBinders ⊆
      (evidenceSource selected).initializedLetBinders := by
    intro binder member
    apply (boundary.rawSubtree.containsStatement containsRaw).initializedLetBinder_mem
    exact List.mem_append_left _ member
  exact boundary.operational.allocateStatementId.forItems_return_safe selected.body.resources
    boundary.invariant.ready.allocateStatementId (boundary.scope.catalog checked)
    (boundary.scope.formation checked) (boundary.scope.functionsCanonical checked)
    retained initializerExtension boundary.invariant.returnBelow returnSafe actualRun

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
