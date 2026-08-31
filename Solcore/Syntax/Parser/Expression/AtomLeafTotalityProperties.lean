import Solcore.Syntax.Parser.Expression.AtomProperties
import Solcore.Syntax.Parser.LiteralTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Totality for the non-recursive expression-atom leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem expressionName_ordinary : Parser.Ordinary expressionName := by
  intro input
  unfold expressionName
  split
  · exact booleanIdentifier_ordinary input
  · exact (identifier_ordinary .expression) input

theorem expressionName_invariantFreeOnValid :
    Parser.InvariantFreeOnValid expressionName :=
  expressionName_ordinary.invariantFreeOnValid

theorem expressionName_ne_invariant (input : State)
    (error : ParserInvariantError) :
    expressionName input ≠ .invariant error :=
  expressionName_ordinary.ne_invariant input error

theorem expressionName_elementTotalityContract :
    ElementTotalityContract expressionName := {
  validFor := expressionName_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := expressionName_preservesTokenWindow
  cursorLtOnSuccess := expressionName_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    expressionName_ne_invariant input error
}

theorem literalExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid literalExpression := by
  unfold literalExpression
  apply Parser.bind_invariantFreeOnValid coreLiteral_validFor
    coreLiteral_ordinary.invariantFreeOnValid
  intro literal
  exact Parser.pure_invariantFreeOnValid ({
    span := literal.span
    value := .literal literal
  } : Expr)

theorem literalExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    literalExpression input ≠ .invariant error :=
  literalExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem identifierExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_invariantFreeOnValid expressionName_validFor
    expressionName_invariantFreeOnValid
  intro name
  exact Parser.pure_invariantFreeOnValid ({
    span := name.span
    value := .identifier name
  } : Expr)

theorem identifierExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    identifierExpression input ≠ .invariant error :=
  identifierExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem proxyExpression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .at .expression)
    (symbol_ordinary .at .expression).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid typeExpr_validFor
    typeExpr_invariantFreeOnValid
  intro type
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span type.span
    value := .proxy marker.span type
  } : Expr)

theorem proxyExpression_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    proxyExpression input ≠ .invariant error :=
  proxyExpression_invariantFreeOnValid.ne_invariant
    input inputValid error

theorem optionalLambdaReturnType_invariantFreeOnValid :
    Parser.InvariantFreeOnValid optionalLambdaReturnType := by
  unfold optionalLambdaReturnType
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro state
  split
  · apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .arrow .typeExpr)
      (symbol_ordinary .arrow .typeExpr).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid typeExpr_validFor
      typeExpr_invariantFreeOnValid
    intro type
    exact Parser.pure_invariantFreeOnValid (some type)
  · exact Parser.pure_invariantFreeOnValid none

theorem optionalLambdaReturnType_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    optionalLambdaReturnType input ≠ .invariant error :=
  optionalLambdaReturnType_invariantFreeOnValid.ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ExpressionAtomInternals
