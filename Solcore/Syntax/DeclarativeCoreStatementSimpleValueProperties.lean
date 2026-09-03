import Solcore.Syntax.DeclarativeCoreStatementSimpleCompleteOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties

/-! Exact success values for canonical Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional let annotations fix both their type AST and final remainder. -/
theorem OptionalLetTypeParses.result_unique
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetTypeParses input left afterLeft)
    (rightParsed : OptionalLetTypeParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present span token parsed =>
          exact False.elim (leftAbsent ⟨span, token.1⟩)
  | present leftSpan leftToken leftType =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken rightType =>
          have afterTokenEq := leftToken.output_unique rightToken
          subst afterTokenEq
          rcases typeExprExactOutcomeSpec.successResultUnique leftType
              rightType with ⟨typeEq, outputEq⟩
          exact ⟨congrArg some typeEq, outputEq⟩

/-- Exact expressions fix a maximal optional let initializer and remainder. -/
theorem OptionalLetInitializerOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present span token parsed =>
          exact False.elim (leftAbsent ⟨span, token.1⟩)
  | present leftSpan leftToken leftValue =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken rightValue =>
          have afterTokenEq := leftToken.output_unique rightToken
          subst afterTokenEq
          rcases expressionOutcomes.successResultUnique leftValue rightValue
            with ⟨valueEq, outputEq⟩
          exact ⟨congrArg some valueEq, outputEq⟩

/-- Semicolon priority and exact expressions fix an optional return value. -/
theorem OptionalReturnValueOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftSpan leftToken =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightAbsent rightValue =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken⟩)
  | present leftAbsent leftValue =>
      cases rightParsed with
      | absent rightSpan rightToken =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken⟩)
      | present rightAbsent rightValue =>
          rcases expressionOutcomes.successResultUnique leftValue rightValue
            with ⟨valueEq, outputEq⟩
          exact ⟨congrArg some valueEq, outputEq⟩

/-- Exact expressions make a successful Core let fix its name, annotation,
initializer, source span, and full statement AST. -/
theorem LetStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : LetStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : LetStatementOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftName leftType
        leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightName
            rightType rightInitializer rightSemicolon =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases leftName.result_unique rightName with ⟨nameEq, inputEq⟩
          subst nameEq
          subst inputEq
          rcases leftType.result_unique rightType with ⟨typeEq, inputEq⟩
          subst typeEq
          subst inputEq
          rcases OptionalLetInitializerOrdinaryParses.result_unique
              expressionOutcomes leftInitializer rightInitializer with
            ⟨initializerEq, inputEq⟩
          subst initializerEq
          subst inputEq
          have semicolonEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonEq
          rfl

/-- Core let success fixes its complete AST and final remainder. -/
theorem LetStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : LetStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : LetStatementOrdinaryParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨LetStatementOrdinaryParses.value_unique expressionOutcomes leftParsed
      rightParsed,
    LetStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      typeExprExactOutcomeSpec.toDeterministicOutcomeSpec leftParsed
      rightParsed⟩

/-- Exact expressions make a successful Core return fix its optional value,
covering span, and full statement AST. -/
theorem ReturnStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ReturnStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ReturnStatementOrdinaryParses expressionOrdinary input
      right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftValue
        leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightValue
            rightSemicolon =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases OptionalReturnValueOrdinaryParses.result_unique
              expressionOutcomes leftValue rightValue with ⟨valueEq, inputEq⟩
          subst valueEq
          subst inputEq
          have semicolonEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonEq
          rfl

/-- Core return success fixes its complete AST and final remainder. -/
theorem ReturnStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ReturnStatementOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ReturnStatementOrdinaryParses expressionOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨ReturnStatementOrdinaryParses.value_unique expressionOutcomes leftParsed
      rightParsed,
    ReturnStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
