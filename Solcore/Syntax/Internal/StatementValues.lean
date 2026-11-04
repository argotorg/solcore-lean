import Solcore.Syntax.Internal.StatementOutcomes
import Solcore.Syntax.Internal.TypeExactness
import Solcore.Syntax.Internal.BlockExactness
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Grammar.StatementLayer
import Solcore.Syntax.Grammar.TermLevels
import Solcore.Syntax.Internal.SignatureExactness

/-!
Exactness of the declarative grammar of statement branches, `for` items and `match`
components: outcomes fix the whole result. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementSimpleValueProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemValueProperties
/-! Exact success values for prioritized Core `for` header items. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact expressions fix a for-header let item, including its optional type,
initializer, and source span. -/
theorem ForLetItemOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForLetItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForLetItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftName leftType leftInitializer =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightName rightType rightInitializer =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases leftName.result_unique rightName with ⟨nameEq, inputEq⟩
          subst nameEq
          subst inputEq
          rcases leftType.result_unique rightType with ⟨typeEq, inputEq⟩
          subst typeEq
          subst inputEq
          have initializerEq :=
            (OptionalLetInitializerOrdinaryParses.result_unique
              expressionOutcomes leftInitializer rightInitializer).1
          subst initializerEq
          rfl

/-- Exact expressions fix a for-header assignment/expression item's AST. -/
theorem ForAssignmentOrExpressionOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : ForAssignmentOrExpressionOrdinaryParses expressionOrdinary
      input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftExpression, leftAfterExpression, leftTail,
    leftExpressionParsed, leftTailParsed, leftBuild⟩
  rcases rightParsed with ⟨rightExpression, rightAfterExpression, rightTail,
    rightExpressionParsed, rightTailParsed, rightBuild⟩
  rcases expressionOutcomes.successResultUnique leftExpressionParsed
      rightExpressionParsed with ⟨expressionEq, inputEq⟩
  subst expressionEq
  subst inputEq
  have tailEq := (leftTailParsed.result_unique expressionOutcomes
    rightTailParsed).1
  subst tailEq
  cases leftBuild <;> cases rightBuild <;> rfl

/-- Let-token priority and exact child values fix a complete for-header item. -/
theorem ForItemOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | letItem leftItem =>
      cases rightParsed with
      | letItem rightItem =>
          exact ForLetItemOrdinaryParses.value_unique expressionOutcomes
            leftItem rightItem
      | assignmentOrExpression rightAbsent rightItem =>
          cases leftItem with
          | parsed span marker name type initializer =>
              exact False.elim (rightAbsent ⟨span, marker.1⟩)
  | assignmentOrExpression leftAbsent leftItem =>
      cases rightParsed with
      | letItem rightItem =>
          cases rightItem with
          | parsed span marker name type initializer =>
              exact False.elim (leftAbsent ⟨span, marker.1⟩)
      | assignmentOrExpression rightAbsent rightItem =>
          exact ForAssignmentOrExpressionOrdinaryParses.value_unique
            expressionOutcomes leftItem rightItem

/-- A successful for-header item fixes its full AST and remainder. -/
theorem ForItemOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ForItemOrdinaryParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨ForItemOrdinaryParses.value_unique expressionOutcomes leftParsed rightParsed,
    ForItemOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      typeExprExactOutcomeSpec.toDeterministicOutcomeSpec leftParsed
      rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForItemsValueProperties
/-! Exact forward-list values for Core `for` header item sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Comma priority and exact items fix the forward tail list and remainder. -/
theorem ForItemsTailOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightSpan rightComma rightStop rightItem rightProgress rightTail =>
          exact False.elim (leftAbsent ⟨rightSpan, rightComma.1⟩)
  | next leftSpan leftComma leftStop leftItem leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftComma.1⟩)
      | next rightSpan rightComma rightStop rightItem rightProgress rightTail =>
          have inputEq := leftComma.output_unique rightComma
          subst inputEq
          rcases ForItemOrdinaryParses.result_unique expressionOutcomes
              leftItem rightItem with ⟨itemEq, inputEq⟩
          subst itemEq
          subst inputEq
          rcases ih rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- An ordinary for-item tail has one exact forward list of items. -/
theorem ForItemsTailOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      left afterLeft)
    (rightParsed : ForItemsTailOrdinaryParses expressionOrdinary stop input
      right afterRight) : left = right :=
  (ForItemsTailOrdinaryParses.result_unique expressionOutcomes stop
    leftParsed rightParsed).1

/-- Stop priority and exact items fix a complete forward item list and
remainder without accepting a trailing comma. -/
theorem ForItemsOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | empty leftSpan leftToken =>
      cases rightParsed with
      | empty => exact ⟨rfl, rfl⟩
      | nonempty rightAbsent rightFirst rightProgress rightTail =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken⟩)
  | nonempty leftAbsent leftFirst leftProgress leftTail =>
      cases rightParsed with
      | empty rightSpan rightToken =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken⟩)
      | nonempty rightAbsent rightFirst rightProgress rightTail =>
          rcases ForItemOrdinaryParses.result_unique expressionOutcomes
              leftFirst rightFirst with ⟨firstEq, inputEq⟩
          subst firstEq
          subst inputEq
          rcases ForItemsTailOrdinaryParses.result_unique expressionOutcomes
              stop leftTail rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- An ordinary public for-item list fixes the ASTs in source order. -/
theorem ForItemsOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) (stop : Symbol)
    {input : Remainder} {left right : List Syntax.ForItem}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForItemsOrdinaryParses expressionOrdinary stop input left
      afterLeft)
    (rightParsed : ForItemsOrdinaryParses expressionOrdinary stop input right
      afterRight) : left = right :=
  (ForItemsOrdinaryParses.result_unique expressionOutcomes stop leftParsed
    rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreForStatementValueProperties
/-! Exact success values for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child statements and expressions fix a complete for statement,
including retained header delimiters, forward item order, and body spans. -/
theorem ForStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftFirstSemicolonSpan
        leftSecondSemicolonSpan leftClosingSpan leftMarker leftOpening
        leftInitializer leftFirstSemicolon leftCondition leftSecondSemicolon
        leftPost leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightFirstSemicolonSpan
            rightSecondSemicolonSpan rightClosingSpan rightMarker rightOpening
            rightInitializer rightFirstSemicolon rightCondition
            rightSecondSemicolon rightPost rightClosing rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases ForItemsOrdinaryParses.result_unique expressionOutcomes
              .semicolon leftInitializer rightInitializer with
            ⟨initializerEq, inputEq⟩
          subst initializerEq
          subst inputEq
          have inputEq := leftFirstSemicolon.output_unique rightFirstSemicolon
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftSecondSemicolon.output_unique rightSecondSemicolon
          subst inputEq
          rcases ForItemsOrdinaryParses.result_unique expressionOutcomes
              .rightParen leftPost rightPost with ⟨postEq, inputEq⟩
          subst postEq
          subst inputEq
          rcases leftClosing.result_unique rightClosing with
            ⟨closingEq, inputEq⟩
          subst closingEq
          subst inputEq
          have bodyEq := leftBody.value_unique statementOutcomes rightBody
          subst bodyEq
          rfl

/-- A successful complete Core for statement fixes its AST and remainder. -/
theorem ForStatementOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input left afterLeft)
    (rightParsed : ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨ForStatementOrdinaryParses.value_unique statementOutcomes expressionOutcomes
      leftParsed rightParsed,
    ForStatementOrdinaryParses.output_unique
      statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementBranchValueProperties
/-! Exact success values for Core `if`, optional `else`, and `while`. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive statements fix a prioritized optional else body. -/
theorem OptionalElseBodyOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalElseBodyOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : OptionalElseBodyOrdinaryParses statementOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightToken rightBody =>
          exact False.elim (leftAbsent ⟨rightSpan, rightToken.1⟩)
  | present leftSpan leftToken leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftToken.1⟩)
      | present rightSpan rightToken rightBody =>
          have afterMarkerEq := leftToken.output_unique rightToken
          subst afterMarkerEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          exact ⟨congrArg some bodyEq, outputEq⟩

/-- Exact expression and recursive statement outcomes fix the condition,
branches, covering source span, and full Core if AST. -/
theorem IfStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftThen leftElse =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightThen rightElse =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftClosing.output_unique rightClosing
          subst inputEq
          rcases leftThen.result_unique statementOutcomes rightThen with
            ⟨thenEq, inputEq⟩
          subst thenEq
          subst inputEq
          have elseEq := (OptionalElseBodyOrdinaryParses.result_unique
            statementOutcomes leftElse rightElse).1
          subst elseEq
          rfl

/-- Core if success fixes both its AST and final remainder. -/
theorem IfStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨IfStatementOrdinaryParses.value_unique expressionOutcomes statementOutcomes
      leftParsed rightParsed,
    IfStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

/-- Exact expression and recursive statement outcomes fix the condition,
body, covering source span, and full contextual while AST. -/
theorem WhileStatementOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftOpening leftCondition leftClosing leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightOpening rightCondition rightClosing rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          have inputEq := leftOpening.output_unique rightOpening
          subst inputEq
          rcases expressionOutcomes.successResultUnique leftCondition
              rightCondition with ⟨conditionEq, inputEq⟩
          subst conditionEq
          subst inputEq
          have inputEq := leftClosing.output_unique rightClosing
          subst inputEq
          have bodyEq := leftBody.value_unique statementOutcomes rightBody
          subst bodyEq
          rfl

/-- Contextual Core while success fixes both its AST and final remainder. -/
theorem WhileStatementOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input left afterLeft)
    (rightParsed : WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨WhileStatementOrdinaryParses.value_unique expressionOutcomes
      statementOutcomes leftParsed rightParsed,
    WhileStatementOrdinaryParses.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec leftParsed rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementControlLeafExactnessProperties
/-! Exact Core block statements and keyword-plus-semicolon control leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The fixed control value retains the unique marker/semicolon cover span. -/
theorem TerminatedControlStatementOrdinaryParses.value_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightSemicolon =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have semicolonSpanEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonSpanEq
          rfl

/-- Control leaves fix the complete statement and successful remainder. -/
theorem TerminatedControlStatementOrdinaryParses.result_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A control rejection fixes either the original or post-marker endpoint. -/
theorem TerminatedControlStatementRejects.output_unique
    {keyword : HardKeyword} {input left right : Remainder}
    (leftRejects : TerminatedControlStatementRejects keyword input left)
    (rightRejects : TerminatedControlStatementRejects keyword input right) :
    left = right := by
  cases leftRejects with
  | markerMissing leftAbsent =>
      cases rightRejects with
      | markerMissing => rfl
      | semicolonMissing rightSpan rightMarker rightAbsent =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | semicolonMissing leftSpan leftMarker leftAbsent =>
      cases rightRejects with
      | markerMissing rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | semicolonMissing rightSpan rightMarker rightAbsent =>
          exact leftMarker.output_unique rightMarker

/-- Unconditional exact outcomes for one fixed terminated control keyword. -/
theorem terminatedControlStatementExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    ExactDeterministicOutcomeSpec
      (TerminatedControlStatementOrdinaryParses keyword statementValue)
      (TerminatedControlStatementRejects keyword) where
  toDeterministicOutcomeSpec :=
    terminatedControlStatementDeterministicOutcomeSpec keyword statementValue
  successValueUnique := TerminatedControlStatementOrdinaryParses.value_unique
  rejectOutputUnique := TerminatedControlStatementRejects.output_unique

/-- A block statement retains its child's exact body and source span. -/
theorem BlockStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : BlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : BlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          have bodyEq := (coreBlockExactOutcomeSpec .require
            statementOutcomes).successValueUnique leftBody rightBody
          subst bodyEq
          rfl

/-- Recursive exact statement outcomes lift through a required braced block. -/
theorem blockStatementExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    ExactDeterministicOutcomeSpec
      (BlockStatementOrdinaryParses statementOrdinary)
      (BlockStatementRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec := blockStatementDeterministicOutcomeSpec
    statementOutcomes.toDeterministicOutcomeSpec
  successValueUnique := BlockStatementOrdinaryParses.value_unique statementOutcomes
  rejectOutputUnique := (coreBlockExactOutcomeSpec .require
    statementOutcomes).rejectOutputUnique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchComponentValueProperties
/-! Exact success values for Core match scrutinees, cases, and default bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact expressions fix a required trailing-comma scrutinee list and its
remainder, including the list's retained delimiter span. -/
theorem MatchScrutineeListOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight :=
  (nonemptyTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    expressionOutcomes).successResultUnique leftParsed rightParsed

/-- A match scrutinee list fixes its complete forward AST value. -/
theorem MatchScrutineeListOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : left = right :=
  (MatchScrutineeListOrdinaryParses.result_unique expressionOutcomes
    leftParsed rightParsed).1

/-- Converting the same parsed list fixes the nonempty carrier and remainder. -/
theorem RequireScrutineesOrdinaryParses.result_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed
  cases rightParsed
  exact ⟨rfl, rfl⟩

/-- Nonempty conversion fixes exactly the supplied scrutinee list value. -/
theorem RequireScrutineesOrdinaryParses.value_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : left = right :=
  (RequireScrutineesOrdinaryParses.result_unique leftParsed rightParsed).1

/-- Exact recursive statement and pattern outcomes fix a match case's AST,
covering source span, and final remainder. -/
theorem MatchCaseOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftPattern leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightPattern rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases patternOutcomes.successResultUnique leftPattern rightPattern
            with ⟨patternEq, inputEq⟩
          subst patternEq
          subst inputEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          subst bodyEq
          exact ⟨rfl, outputEq⟩

/-- A successful match case fixes its full pattern-and-body AST. -/
theorem MatchCaseOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right :=
  (MatchCaseOrdinaryParses.result_unique statementOutcomes patternOutcomes
    leftParsed rightParsed).1

/-- Default-token priority and exact recursive statements fix an optional
default body's value and remainder. -/
theorem OptionalDefaultBodyOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightMarker rightBody =>
          exact False.elim (leftAbsent ⟨rightSpan, rightMarker.1⟩)
  | present leftSpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftMarker.1⟩)
      | present rightSpan rightMarker rightBody =>
          have inputEq := leftMarker.output_unique rightMarker
          subst inputEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          exact ⟨congrArg some bodyEq, outputEq⟩

/-- A prioritized optional default body fixes its exact optional AST. -/
theorem OptionalDefaultBodyOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : left = right :=
  (OptionalDefaultBodyOrdinaryParses.result_unique statementOutcomes
    leftParsed rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchCasesValueProperties
/-! Exact forward-order success values for maximal Core match case lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Case-token priority and exact arms fix the maximal forward case list and
its remainder, including ordinary body diagnostics. -/
theorem MatchCasesOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightArm rightProgress rightTail =>
          exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent =>
          exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm rightProgress rightTail =>
          rcases leftArm.result_unique statementOutcomes patternOutcomes
              rightArm with ⟨armEq, inputEq⟩
          subst armEq
          subst inputEq
          rcases ih rightTail with ⟨tailEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, outputEq⟩

/-- A maximal match case list fixes the exact arm ASTs in source order. -/
theorem MatchCasesOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : List Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCasesOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right :=
  (leftParsed.result_unique statementOutcomes patternOutcomes rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreMatchStatementValueProperties
/-! Exact success values for diagnostic-inclusive Core match statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact child outcomes fix all scrutinees, forward case arms, optional
default, retained spans, and the complete ordinary match statement AST. -/
theorem MatchStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftOpeningSpan leftClosingSpan leftMarker
        leftValues leftRequired leftOpening leftCases leftDefault leftClosing =>
      cases rightParsed with
      | parsed rightMarkerSpan rightOpeningSpan rightClosingSpan rightMarker
            rightValues rightRequired rightOpening rightCases rightDefault
            rightClosing =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases MatchScrutineeListOrdinaryParses.result_unique
              expressionOutcomes leftValues rightValues with
            ⟨valuesEq, inputEq⟩
          subst valuesEq
          subst inputEq
          rcases RequireScrutineesOrdinaryParses.result_unique leftRequired
              rightRequired with ⟨requiredEq, inputEq⟩
          subst requiredEq
          subst inputEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingEq, inputEq⟩
          subst openingEq
          subst inputEq
          rcases leftCases.result_unique statementOutcomes patternOutcomes
              rightCases with ⟨casesEq, inputEq⟩
          subst casesEq
          subst inputEq
          rcases leftDefault.result_unique statementOutcomes rightDefault with
            ⟨defaultEq, inputEq⟩
          subst defaultEq
          subst inputEq
          have closingEq := leftClosing.span_unique rightClosing
          subst closingEq
          rfl

/-- A complete ordinary match success fixes its exact AST and remainder;
diagnostic-only arity or missing-arm validation does not weaken the result. -/
theorem MatchStatementOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input left afterLeft)
    (rightParsed : MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique statementOutcomes expressionOutcomes patternOutcomes
      rightParsed,
    leftParsed.output_unique statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
      patternOutcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementLayerExactnessProperties
/-! Exact Core statement layers from exact recursive Core-term children. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recognized primary stage fixes its exact statement value from the
recursive child outcomes. Core types and inline Yul need no extra premises. -/
theorem StatementLayerPrimaryOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    (stage : StatementLayerStage) (notFallback : stage ≠ .fallback)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : StatementLayerPrimaryOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary stage input left afterLeft)
    (rightParsed : StatementLayerPrimaryOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary stage input right afterRight) :
    left = right := by
  cases stage with
  | letGuard =>
      exact LetStatementOrdinaryParses.value_unique expressionOutcomes
        leftParsed rightParsed
  | returnGuard =>
      exact ReturnStatementOrdinaryParses.value_unique expressionOutcomes
        leftParsed rightParsed
  | matchGuard =>
      exact MatchStatementOrdinaryParses.value_unique statementOutcomes
        expressionOutcomes patternOutcomes leftParsed rightParsed
  | forGuard =>
      exact ForStatementOrdinaryParses.value_unique statementOutcomes
        expressionOutcomes leftParsed rightParsed
  | whileGuard =>
      exact WhileStatementOrdinaryParses.value_unique expressionOutcomes
        statementOutcomes leftParsed rightParsed
  | ifGuard =>
      exact IfStatementOrdinaryParses.value_unique expressionOutcomes
        statementOutcomes leftParsed rightParsed
  | assemblyGuard =>
      exact assemblyStatementExactOutcomeSpec.successValueUnique
        leftParsed rightParsed
  | blockGuard =>
      exact BlockStatementOrdinaryParses.value_unique statementOutcomes
        leftParsed rightParsed
  | breakGuard =>
      exact TerminatedControlStatementOrdinaryParses.value_unique
        leftParsed rightParsed
  | continueGuard =>
      exact TerminatedControlStatementOrdinaryParses.value_unique
        leftParsed rightParsed
  | fallback => contradiction

/-- Deterministic primaries, their exact successful values, and the exact
assignment fallback fix a complete prioritized statement layer, including
transactionally rewound rejection endpoints. -/
theorem statementLayerExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects) :
    ExactDeterministicOutcomeSpec
      (StatementLayerOrdinaryParses statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects)
      (StatementLayerRejects statementOrdinary statementRejects
        expressionOrdinary expressionRejects patternOrdinary patternRejects) :=
  statementLayerSelectionExactOutcomeSpecOfSuccess
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)
    (statementLayerPrimaryDeterministicOutcomeSpec
      statementOutcomes.toDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
      patternOutcomes.toDeterministicOutcomeSpec)
    (StatementLayerPrimaryOrdinaryParses.value_unique statementOutcomes
      expressionOutcomes patternOutcomes)
    (assignmentOrExpressionStatementExactOutcomeSpec expressionOutcomes)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreStatementFuelExactnessProperties
/-! Base and successor lifts for exact mutually recursive Core statement fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Fuel zero admits neither an ordinary statement success nor rejection. -/
theorem coreStatementExactOutcomeSpecWithFuel_zero :
    ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel 0)
      (CoreStatementRejectsWithFuel 0) where
  toDeterministicOutcomeSpec := coreStatementOutcomeSpecWithFuel 0
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed
    exact False.elim (CoreStatementOrdinaryParsesWithFuel.zero leftParsed)
  rejectOutputUnique := by
    intro input left right leftRejected
    exact False.elim (CoreStatementRejectsWithFuel.zero leftRejected)

/-- Statement, expression, and pattern exactness at the same preceding fuel
supplies exact successor statements, with no other recursive prerequisites. -/
theorem coreStatementExactOutcomeSpecWithFuel_succ
    (fuel : Nat)
    (statementOutcomes : ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel))
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel))
    (patternOutcomes : ExactDeterministicOutcomeSpec
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec
      (CoreStatementOrdinaryParsesWithFuel (fuel + 1))
      (CoreStatementRejectsWithFuel (fuel + 1)) := by
  change ExactDeterministicOutcomeSpec
    (StatementLayerOrdinaryParses
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel)
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
    (StatementLayerRejects
      (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel)
      (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel)
      (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel))
  exact statementLayerExactOutcomeSpec statementOutcomes expressionOutcomes
    patternOutcomes

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTermExactnessProperties
/-! Unconditional exactness of mutually recursive Core terms at every fuel. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- All three mutually recursive grammars are exact at each fixed fuel.
Successor expressions use preceding expressions/statements, patterns use
preceding patterns/expressions, and statements use all three preceding levels. -/
theorem coreTermExactOutcomeSpecsWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel) ∧
    ExactDeterministicOutcomeSpec (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel) ∧
    ExactDeterministicOutcomeSpec (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact ⟨coreExpressionExactOutcomeSpecWithFuel_zero,
        corePatternExactOutcomeSpecWithFuel_zero,
        coreStatementExactOutcomeSpecWithFuel_zero⟩
  | succ fuel ih =>
      exact ⟨coreExpressionExactOutcomeSpecWithFuel_succ fuel ih.1 ih.2.2,
        corePatternExactOutcomeSpecWithFuel_succ fuel ih.2.1 ih.1,
        coreStatementExactOutcomeSpecWithFuel_succ fuel ih.2.2 ih.1 ih.2.1⟩

/-- Fixed-fuel Core expressions have exact ASTs and complete outcome endpoints. -/
theorem coreExpressionExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreExpressionOrdinaryParsesWithFuel fuel)
      (CoreExpressionRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).1

/-- Fixed-fuel Core patterns have exact ASTs and complete outcome endpoints. -/
theorem corePatternExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CorePatternOrdinaryParsesWithFuel fuel)
      (CorePatternRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).2.1

/-- Fixed-fuel Core statements have exact ASTs and complete outcome endpoints. -/
theorem coreStatementExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec (CoreStatementOrdinaryParsesWithFuel fuel)
      (CoreStatementRejectsWithFuel fuel) :=
  (coreTermExactOutcomeSpecsWithFuel fuel).2.2

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTermPublicExactnessProperties
/-! Unconditional exact public Core terms and isolated block boundaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Input-selected expression fuel preserves complete ordinary exactness. -/
theorem coreExpressionPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreExpressionOrdinaryParses CoreExpressionPublicRejects where
  toDeterministicOutcomeSpec := coreExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreExpressionExactOutcomeSpecWithFuel (coreExpressionPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (coreExpressionExactOutcomeSpecWithFuel (coreExpressionPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Input-selected pattern fuel preserves complete ordinary exactness. -/
theorem corePatternPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CorePatternOrdinaryParses CorePatternPublicRejects where
  toDeterministicOutcomeSpec := corePatternPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (corePatternExactOutcomeSpecWithFuel (corePatternPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (corePatternExactOutcomeSpecWithFuel (corePatternPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Input-selected statement fuel preserves complete ordinary exactness. -/
theorem coreStatementPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec CoreStatementOrdinaryParses CoreStatementPublicRejects where
  toDeterministicOutcomeSpec := coreStatementPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (coreStatementExactOutcomeSpecWithFuel (coreStatementPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (coreStatementExactOutcomeSpecWithFuel (coreStatementPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Both Core block tail policies now have unconditional public exactness. -/
theorem coreBlockPublicExactOutcomeSpec (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec (CoreBlockPublicOrdinaryParses policy)
      (CoreBlockPublicRejects policy) :=
  coreBlockPublicExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel policy

/-- Captured-body isolation preserves unconditional exactness for both policies. -/
theorem isolatedCoreBlockPublicExactOutcomeSpec (policy : CoreBlockTailPolicy) :
    ExactDeterministicOutcomeSpec (IsolatedCoreBlockPublicOrdinaryParses policy)
      (IsolatedCoreBlockPublicRejects policy) :=
  isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel policy

/-- Public Core expressions fix their complete AST and final remainder. -/
theorem CoreExpressionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Expr} {afterLeft afterRight : Remainder}
    (leftParsed : CoreExpressionOrdinaryParses input left afterLeft)
    (rightParsed : CoreExpressionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  coreExpressionPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core patterns fix their complete AST and final remainder. -/
theorem CorePatternOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Pattern} {afterLeft afterRight : Remainder}
    (leftParsed : CorePatternOrdinaryParses input left afterLeft)
    (rightParsed : CorePatternOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  corePatternPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core statements fix their complete AST and final remainder. -/
theorem CoreStatementOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.Statement} {afterLeft afterRight : Remainder}
    (leftParsed : CoreStatementOrdinaryParses input left afterLeft)
    (rightParsed : CoreStatementOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  coreStatementPublicExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public Core expression rejection fixes the complete endpoint. -/
theorem CoreExpressionPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CoreExpressionPublicRejects input left)
    (rightRejected : CoreExpressionPublicRejects input right) : left = right :=
  coreExpressionPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Public Core pattern rejection fixes the complete endpoint. -/
theorem CorePatternPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CorePatternPublicRejects input left)
    (rightRejected : CorePatternPublicRejects input right) : left = right :=
  corePatternPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

/-- Public Core statement rejection fixes the complete endpoint. -/
theorem CoreStatementPublicRejects.output_unique {input left right : Remainder}
    (leftRejected : CoreStatementPublicRejects input left)
    (rightRejected : CoreStatementPublicRejects input right) : left = right :=
  coreStatementPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
end
