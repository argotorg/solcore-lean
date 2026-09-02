import Solcore.Syntax.DeclarativeCoreTypeSuccessExactnessProperties

/-! Public exact values for recursive Core type lists and optional suffixes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recursive type-list tail fixes elements, closing span, and remainder. -/
theorem TypeExprTrailingDelimitedTailParses.result_unique
    {closing : Symbol} {input : Remainder}
    {left right : List Syntax.TypeExpr}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprTrailingDelimitedTailParses closing input left
      leftClosing afterLeft)
    (rightParsed : TypeExprTrailingDelimitedTailParses closing input right
      rightClosing afterRight) :
      left = right ∧ leftClosing = rightClosing ∧ afterLeft = afterRight := by
  cases leftParsed with
  | close commaAbsent closingToken =>
      cases rightParsed with
      | close _ rightClosingToken =>
          cases closingToken.token_unique rightClosingToken
          exact ⟨rfl, rfl, rfl⟩
      | trailing commaToken _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | next commaToken _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
  | trailing commaToken closingToken =>
      cases rightParsed with
      | close commaAbsent _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | trailing _ rightClosingToken =>
          cases closingToken.token_unique rightClosingToken
          exact ⟨rfl, rfl, rfl⟩
      | next _ closingAbsent _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  | next commaToken closingAbsent progress elementsEq elementParsed tail =>
      cases rightParsed with
      | close commaAbsent _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | trailing _ rightClosing =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent rightClosing)
      | next _ _ _ rightElementsEq rightElement rightTail =>
          have elementEq := TypeExprParses.value_unique elementParsed
            rightElement
          have afterElementEq := TypeExprParses.output_unique elementParsed
            rightElement
          subst elementEq
          subst afterElementEq
          rcases TypeExprTrailingDelimitedTailParses.result_unique tail
            rightTail with ⟨tailEq, closingEq, outputEq⟩
          constructor
          · simp_all
          · exact ⟨closingEq, outputEq⟩
termination_by left.length
decreasing_by simp_all

/-- A recursive type-list tail has one exact element sequence. -/
theorem TypeExprTrailingDelimitedTailParses.value_unique
    {closing : Symbol} {input : Remainder} {left right : List Syntax.TypeExpr}
    {leftClosing rightClosing : SourceSpan} {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprTrailingDelimitedTailParses closing input left leftClosing afterLeft)
    (rightParsed : TypeExprTrailingDelimitedTailParses closing input right rightClosing afterRight) :
    left = right := (leftParsed.result_unique rightParsed).1

/-- A recursive type list fixes its complete AST and final remainder. -/
theorem TypeExprTrailingDelimitedListParses.result_unique
    {opening closing : Symbol} {input : Remainder}
    {left right : DelimitedList Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprTrailingDelimitedListParses opening closing input left afterLeft)
    (rightParsed : TypeExprTrailingDelimitedListParses opening closing input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | empty leftOpening leftClosing _ _ leftOpeningToken leftClosingToken =>
      cases rightParsed with
      | empty rightOpening rightClosing _ _ rightOpeningToken rightClosingToken =>
          have openingEq := congrArg (fun t : Token => t.span)
            (leftOpeningToken.token_unique rightOpeningToken)
          have closingEq := congrArg (fun t : Token => t.span)
            (leftClosingToken.token_unique rightClosingToken)
          cases left; cases right; simp_all
      | nonempty _ _ closingAbsent _ _ _ _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent leftClosingToken)
  | nonempty leftOpening leftClosing closingAbsent leftOpeningToken _ _ _ _ _
      leftFirst leftTail =>
      cases rightParsed with
      | empty _ _ _ _ _ rightClosingToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent rightClosingToken)
      | nonempty rightOpening rightClosing _ rightOpeningToken _ _ _ _ _
          rightFirst rightTail =>
          have openingEq := congrArg (fun t : Token => t.span)
            (leftOpeningToken.token_unique rightOpeningToken)
          have firstEq := TypeExprParses.value_unique leftFirst rightFirst
          have firstOutputEq := TypeExprParses.output_unique leftFirst rightFirst
          subst firstEq; subst firstOutputEq
          rcases TypeExprTrailingDelimitedTailParses.result_unique leftTail
            rightTail with ⟨restEq, closingEq, outputEq⟩
          constructor
          · cases left; cases right; simp_all
          · exact outputEq

/-- A recursive type list has one exact delimited-list AST. -/
theorem TypeExprTrailingDelimitedListParses.value_unique
    {opening closing : Symbol} {input : Remainder}
    {left right : DelimitedList Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprTrailingDelimitedListParses opening closing input left afterLeft)
    (rightParsed : TypeExprTrailingDelimitedListParses opening closing input right afterRight) :
    left = right := (leftParsed.result_unique rightParsed).1

/-- Optional named-type arguments fix their value and final remainder. -/
theorem OptionalNamedTypeArgumentsParses.result_unique
    {input : Remainder}
    {left right : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalNamedTypeArgumentsParses input left afterLeft)
    (rightParsed : OptionalNamedTypeArgumentsParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present _ _ rightOpeningToken _ _ _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftAbsent rightOpeningToken)
  | @present leftInput leftAfterFirst leftOutput leftArguments leftFirst leftRest
      leftOpening leftClosing leftOpeningToken leftProgress leftTokensEq
      leftEndIndexEq leftElementsEq leftSpanEq leftFirstParsed leftTail =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightAbsent leftOpeningToken)
      | @present rightInput rightAfterFirst rightOutput rightArguments rightFirst
          rightRest rightOpening rightClosing rightOpeningToken rightProgress
          rightTokensEq rightEndIndexEq rightElementsEq rightSpanEq
          rightFirstParsed rightTail =>
          have openingEq := congrArg (fun t : Token => t.span)
            (leftOpeningToken.token_unique rightOpeningToken)
          change leftOpening = rightOpening at openingEq
          have firstEq := TypeExprParses.value_unique leftFirstParsed rightFirstParsed
          have firstOutputEq := TypeExprParses.output_unique leftFirstParsed rightFirstParsed
          subst firstEq; subst firstOutputEq
          rcases TypeExprTrailingDelimitedTailParses.result_unique leftTail
            rightTail with ⟨restEq, closingEq, outputEq⟩
          subst restEq
          constructor
          · congr 1
            cases leftArguments with | mk _ leftElements =>
              cases leftElements with | mk _ _ =>
                cases rightArguments with | mk _ rightElements =>
                  cases rightElements with | mk _ _ =>
                    simp_all [Syntax.NonemptyList.toList]
          · exact outputEq

/-- Optional named-type arguments have one exact optional AST. -/
theorem OptionalNamedTypeArgumentsParses.value_unique
    {input : Remainder} {left right : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalNamedTypeArgumentsParses input left afterLeft)
    (rightParsed : OptionalNamedTypeArgumentsParses input right afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

/-- Optional function-type returns fix their value and final remainder. -/
theorem OptionalFunctionTypeReturnsParses.result_unique
    {input : Remainder} {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionTypeReturnsParses input left afterLeft)
    (rightParsed : OptionalFunctionTypeReturnsParses input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present _ rightMarker _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token leftAbsent rightMarker.1)
  | present _ leftMarker leftValues =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (typeTokenAbsent_conflicts_token rightAbsent leftMarker.1)
      | present _ rightMarker rightValues =>
          have markerOutputEq := leftMarker.output_unique rightMarker
          subst markerOutputEq
          rcases TypeExprTrailingDelimitedListParses.result_unique leftValues
            rightValues with ⟨valuesEq, outputEq⟩
          exact ⟨congrArg some valuesEq, outputEq⟩

/-- Optional function-type returns have one exact optional AST. -/
theorem OptionalFunctionTypeReturnsParses.value_unique
    {input : Remainder} {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalFunctionTypeReturnsParses input left afterLeft)
    (rightParsed : OptionalFunctionTypeReturnsParses input right afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
