import Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionLeafExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties

/-! Exact values of leading-dot, proxy, and array Core expression atoms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Opening-parenthesis priority fixes the optional constructor arguments. -/
theorem OptionalDotConstructorArgumentsOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Option (DelimitedList Syntax.Expr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary
      input left afterLeft)
    (rightParsed : OptionalDotConstructorArgumentsOrdinaryParses nestedOrdinary
      input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightArguments => exact False.elim (leftAbsent rightArguments.opening_present)
  | present leftArguments =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent leftArguments.opening_present)
      | present rightArguments =>
          exact congrArg some (leftArguments.value_unique outcomes rightArguments)

/-- Leading-dot construction fixes its marker, Boolean-first name, and arguments. -/
theorem DotConstructorOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftDot leftName leftArguments =>
      cases rightParsed with
      | parsed rightSpan rightDot rightName rightArguments =>
          rcases leftDot.result_unique rightDot with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases ExpressionNameOrdinaryParses.result_unique leftName rightName with
            ⟨nameEq, nameOutputEq⟩
          subst nameEq
          subst nameOutputEq
          cases OptionalDotConstructorArgumentsOrdinaryParses.value_unique
            outcomes leftArguments rightArguments
          rfl

/-- Leading-dot construction fixes its complete AST and final remainder. -/
theorem DotConstructorOrdinaryParses.result_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : DotConstructorOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : DotConstructorOrdinaryParses nestedOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Exact type outcomes fix the proxy marker, type, and complete covering span. -/
theorem ProxyExpressionOrdinaryParses.value_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ProxyExpressionOrdinaryParses typeOrdinary input left afterLeft)
    (rightParsed : ProxyExpressionOrdinaryParses typeOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftType =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightType =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases outcomes.successValueUnique leftType rightType
          rfl

/-- Exact no-trailing nested lists fix the complete array AST and span. -/
theorem ArrayLiteralExpressionOrdinaryParses.value_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input left afterLeft)
    (rightParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftValues =>
      cases rightParsed with
      | parsed rightValues =>
          cases leftValues.value_unique outcomes rightValues
          rfl

end Solcore.Syntax.DeclarativeGrammar
