import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts
import Solcore.SourceSemantics.SourceInferenceActualLocalExpression
import Solcore.SourceSemantics.SourceInferenceSelectedDeclaration

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : Selected compiled row fuel}
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem expressionRetained_literal {literal : Syntax.CoreLiteral}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (expressionEq : expression.value = .literal literal)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression expected
      initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have success := boundary.accepted
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  cases literalForm : literal.value with
  | string _ => simp [Detail.inferExprFuel, expressionEq, literalForm] at success
  | decimal spelling | hexadecimal spelling =>
    cases decoded : numericLiteralValue? literal.value with
    | none =>
      unfold Detail.inferExprFuel at success
      simp only [allocationEq, expressionEq] at success
      rw [literalForm] at decoded
      simp [literalForm, decoded, bind, Except.bind] at success
    | some rawValue =>
      exact inferExprFuel_success_numericLiteral_expressionTypingBase_selected
        selected.body.resources boundary.interfaces expressionEq rfl decoded allocationEq success boundary.extension
        boundary.requirements boundary.integerLiterals boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures
        ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered

theorem expressionRetained_identifier {name : Syntax.Identifier}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (expressionEq : expression.value = .identifier name)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression expected
      initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have success := boundary.accepted
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  cases found : allocated.lookupBinder? name.value with
  | some binder =>
    obtain ⟨pending, ledger⟩ := boundary.operational.ledger
    exact inferExprFuel_success_localIdentifier_expressionTypingBase_actual
      selected.body.resources boundary.interfaces expressionEq allocationEq found success ledger boundary.operational.origins
      boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures
      ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered
  | none =>
    cases boolean : (name.value == "true" || name.value == "false") with
    | true =>
      exact inferExprFuel_success_builtinBooleanIdentifier_expressionTypingBase_selected
        selected.body.resources boundary.interfaces expressionEq allocationEq found boolean success boundary.extension
        boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered
    | false =>
      cases functions : Detail.functionsNamed inferenceContext name.value with
      | error error =>
        simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
          functions, bind, Except.bind] at success
      | ok candidates =>
        cases candidates with
        | nil =>
          cases builtin : builtinFunctionNamed? name.value with
          | none =>
            simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
              functions, builtin, bind, Except.bind] at success
          | some function =>
            exact inferExprFuel_success_builtinFunctionIdentifier_expressionTypingBase_selected
              selected.body.resources boundary.interfaces expressionEq allocationEq found boolean functions builtin success
              boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures
              ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered
        | cons signature rest =>
          cases rest with
          | nil =>
            exact inferExprFuel_success_declarationIdentifier_expressionTypingBase_actual
              selected.body.resources boundary.interfaces expressionEq allocationEq found boolean functions success
              boundary.extension boundary.requirements boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures
              ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered
          | cons next rest =>
            simp [Detail.inferExprFuel, allocationEq, expressionEq, found, boolean,
              functions, bind, Except.bind] at success

theorem expressionRetained_proxy {marker : Syntax.SourceSpan} {sourceType : Syntax.TypeExpr}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (expressionEq : expression.value = .proxy marker sourceType)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression expected
      initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  have success := boundary.accepted
  generalize allocationEq : initial.allocateExpressionId = allocatedPair
  rcases allocatedPair with ⟨id, allocated⟩
  exact inferExprFuel_success_proxy_expressionTypingBase_selected
    selected.body.resources boundary.interfaces expressionEq allocationEq success boundary.extension boundary.requirements
    boundary.expressionRequirements boundary.coercionPrimaries (boundary.scope.catalog checked) boundary.scope.signatures boundary.scope.owner boundary.scope.parameters ((CheckingScope.refl selected).canonical checked) boundary.invariant boundary.covered

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
