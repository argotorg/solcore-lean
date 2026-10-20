import Solcore.SourceSemantics.SourceCompiledGeneralizedAssemblyContracts
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
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}

theorem statementRooted_zero : StatementRootedSoundness selected 0 := by
  intro inferenceContext statement expectedReturn initial result frames target returnSafe returnAdmissible boundary
  have success := boundary.accepted
  simp only [Detail.inferStatementFuel] at success
  cases success

theorem statementRooted_step_of_for
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (barriers : SelectedInitializerBarriers selected)
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
  intro inferenceContext statement expectedReturn initial result frames target returnSafe returnAdmissible boundary
  have expressionSound : ExpressionRootedSoundness selected childFuel :=
    expressionRooted_of_retained checked (recursiveExpression childFuel (Nat.lt_succ_self childFuel))
  have bodySound : StatementsRootedSoundness selected childFuel :=
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
      have childSound : ExpressionRootedSoundness selected occurrence.childFuel := by
        rw [childEq]
        exact expressionSound
      simpa only [contextEq, resultEq] using
        statement_initialized occurrence checked childSound actualBoundary (barriers.statement occurrence actualBoundary)
  | returnStmt value =>
    cases value with
    | none => exact statement_returnUnit checked form boundary
    | some value => exact statement_returnValue checked expressionSound form boundary returnSafe returnAdmissible
  | expression expression trailingSemicolon =>
    exact statement_expression checked expressionSound form boundary
  | ifThen condition body elseBody =>
    cases elseBody with
    | none =>
      exact statement_if_without_else checked expressionSound form boundary returnSafe returnAdmissible
        (fun safe admissible bodyBoundary => bodySound safe admissible bodyBoundary)
    | some elseBody =>
      exact statement_if_with_else checked expressionSound form boundary returnSafe returnAdmissible
        (fun safe admissible bodyBoundary => bodySound safe admissible bodyBoundary)
  | block body =>
    exact statement_block checked form boundary
      (fun bodyBoundary => bodySound (initial := initial.allocateStatementId.2)
        (fun binder member => returnSafe binder member) returnAdmissible bodyBoundary)
  | assignValue target operator value =>
    exact statement_assignValue checked placeSound expressionSound form boundary
  | assignBitNot target span => exact statement_assignBitNot checked placeSound form boundary
  | matchWith scrutinees arms =>
    exact statement_match checked recursiveExpression form boundary returnSafe returnAdmissible
      (fun smaller below {bodySource bodyInitial bodyResult bodyTarget} safe admissible bodyBoundary =>
        recursiveBody smaller below safe admissible bodyBoundary)
  | forLoop headerSpan initializer condition post body =>
    exact forSound form boundary returnSafe returnAdmissible
  | whileLoop condition body =>
    exact statement_while checked expressionSound form boundary returnSafe returnAdmissible
      (fun safe admissible bodyBoundary => bodySound safe admissible bodyBoundary)
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

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
