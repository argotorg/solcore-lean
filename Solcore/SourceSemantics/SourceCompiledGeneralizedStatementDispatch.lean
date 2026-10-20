import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
import Solcore.SourceSemantics.SourceCompiledProvenanceCompatibility
import Solcore.SourceSemantics.SourceCompiledGeneralizedBlockStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedReturnStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedControlStatements
import Solcore.SourceSemantics.SourceCompiledGeneralizedAnnotatedDeclaration
import Solcore.SourceSemantics.SourceCompiledGeneralizedBitNotAssignment
import Solcore.SourceSemantics.SourceCompiledGeneralizedValueAssignment
import Solcore.SourceSemantics.SourceCompiledGeneralizedIfStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedIfElseStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedWhileStatement
import Solcore.SourceSemantics.SourceCompiledGeneralizedDefaultMatchStatement

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {callProvenance : CallIndex → Prop}

theorem statementRooted_zero_for : StatementRootedSoundnessFor callProvenance selected 0 := by
  intro inferenceContext statement expectedReturn initial result frames target here returnSafe returnAdmissible boundary
  have success := boundary.accepted
  simp only [Detail.inferStatementFuel] at success
  cases success

theorem statementRooted_step_of_for_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (barriers : BodyInitializerBarriersFor callProvenance selected)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (recursiveBody : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundnessFor callProvenance selected smaller)
    (placeSound : PlaceRootedSoundnessFor callProvenance selected childFuel)
    (forSound : ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
      {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
      {initial : State} {result : Detail.StatementResult}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
      callProvenance (.statement (childFuel + 1) inferenceContext statement expectedReturn initial result) →
      statement.value = .forLoop headerSpan initializer condition post body →
      StatementBoundary selected (childFuel + 1) inferenceContext statement expectedReturn initial result frames target →
      (∀ binder ∈ initial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementConclusion selected inferenceContext expectedReturn result frames target) :
    StatementRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext statement expectedReturn initial result frames target here returnSafe returnAdmissible boundary
  have expressionSound : ExpressionRootedSoundnessFor callProvenance selected childFuel :=
    expressionRooted_of_retained_for checked (recursiveExpression childFuel (Nat.lt_succ_self childFuel))
  have bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel :=
    recursiveBody childFuel (Nat.lt_succ_self childFuel)
  cases form : statement.value with
  | letDecl name annotation initializer =>
    cases initializer with
    | none =>
      cases annotation with
      | none =>
        have success := boundary.accepted
        simp [Detail.inferStatementFuel, form, bind, Except.bind, throw] at success
      | some sourceType => exact statement_annotatedUninitialized checked form boundary
    | some source =>
      obtain ⟨occurrence, childEq, contextEq, initialEq, resultEq⟩ :=
        boundary.initializerOccurrence checked form
      have actualBoundary : StatementBoundary selected (occurrence.childFuel + 1)
          occurrence.inferenceContext statement expectedReturn occurrence.entry occurrence.result frames target := by
        simpa only [childEq, contextEq, initialEq, resultEq] using boundary
      have actualHere : callProvenance (.statement (occurrence.childFuel + 1)
          occurrence.inferenceContext statement expectedReturn occurrence.entry occurrence.result) := by
        simpa only [childEq, contextEq, initialEq, resultEq] using here
      have childSound : ExpressionRootedSoundnessFor callProvenance selected occurrence.childFuel := by
        rw [childEq]
        exact expressionSound
      simpa only [contextEq, resultEq] using
        statement_initialized_for occurrence checked descend childSound actualHere actualBoundary
          (barriers.statement occurrence actualHere actualBoundary)
  | returnStmt value =>
    cases value with
    | none => exact statement_returnUnit checked form boundary
    | some value => exact statement_returnValue_for checked descend expressionSound here form boundary returnSafe returnAdmissible
  | expression expression trailingSemicolon =>
    exact statement_expression_for checked descend expressionSound here form boundary
  | ifThen condition body elseBody =>
    cases elseBody with
    | none =>
      exact statement_if_without_else_for checked descend expressionSound here form boundary returnSafe returnAdmissible
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
    | some elseBody =>
      exact statement_if_with_else_for checked descend expressionSound here form boundary returnSafe returnAdmissible
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | block body =>
    exact statement_block_for checked descend bodySound here form returnSafe returnAdmissible boundary
  | assignValue target operator value =>
    exact statement_assignValue_for checked descend placeSound expressionSound here form boundary
  | assignBitNot target span => exact statement_assignBitNot_for checked descend placeSound here form boundary
  | matchWith scrutinees arms =>
    exact statement_match_for descend checked recursiveExpression here form boundary returnSafe returnAdmissible
      (fun smaller below {bodySource bodyInitial bodyResult bodyTarget} bodyHere safe admissible bodyBoundary =>
        recursiveBody smaller below bodyHere safe admissible bodyBoundary)
  | forLoop headerSpan initializer condition post body =>
    exact forSound here form boundary returnSafe returnAdmissible
  | whileLoop condition body =>
    exact statement_while_for checked descend expressionSound here form boundary returnSafe returnAdmissible
      (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | assembly block =>
    have success := boundary.accepted
    simp only [Detail.inferStatementFuel, form] at success
    cases success
  | breakStmt => exact statement_break checked form boundary
  | continueStmt => exact statement_continue checked form boundary
  | error =>
    have success := boundary.accepted
    simp only [Detail.inferStatementFuel, form] at success
    cases success

theorem statementRooted_zero : StatementRootedSoundness selected 0 :=
  statementRootedSoundness_of_true (statementRooted_zero_for (selected := selected) (callProvenance := fun _ => True))

theorem statementRooted_step_of_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : BodyInitializerBarriers selected)
    (recursiveExpression : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (recursiveBody : ∀ smaller, smaller < childFuel + 1 → StatementsRootedSoundness selected smaller)
    (placeSound : PlaceRootedSoundness selected childFuel)
    (forSound : ∀ {inferenceContext : SourceInference.Context} {statement : Syntax.Statement}
      {headerSpan : Syntax.SourceSpan} {initializer post : List Syntax.ForItem}
      {condition : Syntax.Expr} {body : Syntax.Block} {expectedReturn : Ty}
      {initial : State} {result : Detail.StatementResult}
      {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
      statement.value = .forLoop headerSpan initializer condition post body →
      StatementBoundary selected (childFuel + 1) inferenceContext statement expectedReturn initial result frames target →
      (∀ binder ∈ initial.localBinders,
        ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
      TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
      StatementConclusion selected inferenceContext expectedReturn result frames target) :
    StatementRootedSoundness selected (childFuel + 1) := by
  apply statementRootedSoundness_of_true
  apply statementRooted_step_of_for_for checked true_childClosed barriers.with_true
    (fun smaller less => expressionRetainedSoundnessFor_true (recursiveExpression smaller less))
    (fun smaller less => statementsRootedSoundnessFor_true (recursiveBody smaller less))
    (placeRootedSoundnessFor_true placeSound)
  intro inferenceContext statement headerSpan initializer post condition body expectedReturn initial result frames target
    _ form boundary returnSafe returnAdmissible
  exact forSound form boundary returnSafe returnAdmissible

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
