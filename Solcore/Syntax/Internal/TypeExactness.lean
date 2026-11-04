import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Exactness of the declarative grammar of type expressions: outcomes fix the whole result.
Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeSuccessExactnessMotive
/-! Internal motives shared by the recursive Core type value proof. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar.CoreTypeExactnessInternals

theorem nonemptyDelimited_eq_of_toList_eq {alpha : Type}
    {left right : NonemptyDelimitedList alpha}
    (spanEq : left.span = right.span)
    (elementsEq : left.elements.toList = right.elements.toList) :
    left = right := by
  cases left with
  | mk _ leftElements =>
      cases leftElements with
      | mk _ _ =>
          cases right with
          | mk _ rightElements =>
              cases rightElements with
              | mk _ _ => simp_all [Syntax.NonemptyList.toList]

def typeValueMotive (input : Remainder) (value : Syntax.TypeExpr)
    (output : Remainder) (_ : TypeExprParses input value output) : Prop :=
  ∀ {right afterRight}, TypeExprParses input right afterRight → value = right

def tailValueMotive (closing : Symbol) (input : Remainder)
    (values : List Syntax.TypeExpr) (closingSpan : SourceSpan)
    (output : Remainder)
    (_ : TypeExprTrailingDelimitedTailParses closing input values closingSpan
      output) : Prop :=
  ∀ {right rightClosing afterRight},
    TypeExprTrailingDelimitedTailParses closing input right rightClosing
      afterRight →
    values = right ∧ closingSpan = rightClosing ∧ output = afterRight

def listValueMotive (opening closing : Symbol) (input : Remainder)
    (value : DelimitedList Syntax.TypeExpr) (output : Remainder)
    (_ : TypeExprTrailingDelimitedListParses opening closing input value
      output) : Prop :=
  ∀ {right afterRight},
    TypeExprTrailingDelimitedListParses opening closing input right afterRight →
    value = right ∧ output = afterRight

def argumentsValueMotive (input : Remainder)
    (value : Option (NonemptyDelimitedList Syntax.TypeExpr))
    (output : Remainder)
    (_ : OptionalNamedTypeArgumentsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalNamedTypeArgumentsParses input right afterRight →
    value = right ∧ output = afterRight

def returnsValueMotive (input : Remainder)
    (value : Option (DelimitedList Syntax.TypeExpr)) (output : Remainder)
    (_ : OptionalFunctionTypeReturnsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalFunctionTypeReturnsParses input right afterRight →
    value = right ∧ output = afterRight

end Solcore.Syntax.DeclarativeGrammar.CoreTypeExactnessInternals
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeSuccessExactnessProperties
/-! Exact successful values for the mutually recursive Core type grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

open CoreTypeExactnessInternals

/-- Recursive Core type parsing constructs one exact type-expression AST. -/
theorem TypeExprParses.value_unique {input : Remainder}
    {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprParses input left afterLeft) (rightParsed : TypeExprParses input right afterRight) : left = right := by
  refine TypeExprParses.rec
    (motive_1 := typeValueMotive) (motive_2 := tailValueMotive)
    (motive_3 := listValueMotive) (motive_4 := argumentsValueMotive)
    (motive_5 := returnsValueMotive) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ leftParsed rightParsed
  · intro input afterKeyword afterParameters output result parameters returns
      keywordSpan keywordToken resultEq parametersParsed returnsParsed
      parametersIH returnsIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword rightResultEq rightParameters rightReturns =>
        rcases keywordToken.result_unique rightKeyword with ⟨keywordEq, outEq⟩
        subst keywordEq; subst outEq
        rcases parametersIH rightParameters with
          ⟨parametersEq, parametersOutEq⟩
        subst parametersEq; subst parametersOutEq
        rcases returnsIH rightReturns with ⟨returnsEq, returnsOutEq⟩
        subst returnsEq
        exact resultEq.trans rightResultEq.symm
    | comptime _ _ _ rightMarker _ _ _ _ => cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ => cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | proxy _ rightMarker _ _ => cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨_, token⟩
        cases typeTokenAt_kind_eq keywordToken.1 token
    | named _ _ rightName _ _ => cases typeTokenAt_kind_eq keywordToken.1 rightName.2.2.1
  · intro input afterMarker afterOpening afterInner output result inner
      markerSpan openingSpan closingSpan markerToken openingToken closingToken
      resultEq innerParsed innerIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ => cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker rightOpening rightClosing rightResultEq
          rightInner =>
        rcases markerToken.result_unique rightMarker with ⟨markerEq, outEq⟩
        subst markerEq; subst outEq
        rcases openingToken.result_unique rightOpening with ⟨openingEq, outEq⟩
        subst openingEq; subst outEq
        have innerEq := innerIH rightInner
        have innerOutEq := innerParsed.output_unique rightInner
        subst innerEq; subst innerOutEq
        have closingEq := closingToken.span_unique rightClosing
        subst closingEq
        exact resultEq.trans rightResultEq.symm
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        have h := typeTokenAt_kind_eq markerToken.1 rightMarker.1; simp [ContextualKeyword.spelling] at h
    | proxy _ rightMarker _ _ => cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨_, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named comptimeAbsent _ _ _ _ =>
        exact False.elim (comptimeAbsent ⟨markerSpan, openingSpan,
          markerToken.1, by simpa [markerToken.2] using openingToken.1⟩)
  · intro input afterMarker afterOpening afterKey afterArrow afterValue output
      result key value markerSpan openingSpan arrowSpan closingSpan markerToken
      openingToken arrowToken closingToken resultEq keyParsed valueParsed keyIH
      valueIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ => cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ =>
        have h := typeTokenAt_kind_eq markerToken.1 rightMarker.1; simp [ContextualKeyword.spelling] at h
    | mapping _ _ _ _ rightMarker rightOpening rightArrow rightClosing
          rightResultEq rightKey rightValue =>
        rcases markerToken.result_unique rightMarker with ⟨markerEq, outEq⟩
        subst markerEq; subst outEq
        rcases openingToken.result_unique rightOpening with ⟨openingEq, outEq⟩
        subst openingEq; subst outEq
        have keyEq := keyIH rightKey
        have keyOutEq := keyParsed.output_unique rightKey
        subst keyEq; subst keyOutEq
        rcases arrowToken.result_unique rightArrow with ⟨arrowEq, outEq⟩
        subst arrowEq; subst outEq
        have valueEq := valueIH rightValue
        have valueOutEq := valueParsed.output_unique rightValue
        subst valueEq; subst valueOutEq
        have closingEq := closingToken.span_unique rightClosing
        subst closingEq
        exact resultEq.trans rightResultEq.symm
    | proxy _ rightMarker _ _ => cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨_, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named _ mappingAbsent _ _ _ =>
        exact False.elim (mappingAbsent ⟨markerSpan, openingSpan,
          markerToken.1, by simpa [markerToken.2] using openingToken.1⟩)
  · intro input afterMarker output result inner markerSpan markerToken resultEq
      innerParsed innerIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ => cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ => cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ => cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | proxy _ rightMarker rightResultEq rightInner =>
        rcases markerToken.result_unique rightMarker with ⟨markerEq, outEq⟩
        subst markerEq; subst outEq
        have innerEq := innerIH rightInner
        subst innerEq
        exact resultEq.trans rightResultEq.symm
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨_, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named _ _ rightName _ _ => cases typeTokenAt_kind_eq markerToken.1 rightName.2.2.1
  · intro input output result values resultEq valuesParsed valuesIH right
      afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        rcases valuesParsed.opening_token with ⟨_, token⟩; cases typeTokenAt_kind_eq token rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ =>
        rcases valuesParsed.opening_token with ⟨_, token⟩; cases typeTokenAt_kind_eq token rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        rcases valuesParsed.opening_token with ⟨_, token⟩; cases typeTokenAt_kind_eq token rightMarker.1
    | proxy _ rightMarker _ _ =>
        rcases valuesParsed.opening_token with ⟨_, token⟩; cases typeTokenAt_kind_eq token rightMarker.1
    | tuple rightResultEq rightValues =>
        rcases valuesIH rightValues with ⟨valuesEq, valuesOutEq⟩
        subst valuesEq
        exact resultEq.trans rightResultEq.symm
    | named _ _ rightName _ _ =>
        rcases valuesParsed.opening_token with ⟨_, token⟩; cases typeTokenAt_kind_eq token rightName.2.2.1
  · intro input afterName output result name arguments comptimeAbsent
      mappingAbsent nameParsed resultEq argumentsParsed argumentsIH right
      afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        cases typeTokenAt_kind_eq nameParsed.2.2.1 rightKeyword.1
    | comptime markerSpan openingSpan _ rightMarker rightOpening _ _ _ =>
        exact False.elim (comptimeAbsent ⟨markerSpan, openingSpan,
          rightMarker.1, by simpa [rightMarker.2] using rightOpening.1⟩)
    | mapping markerSpan openingSpan _ _ rightMarker rightOpening _ _ _ _ _ =>
        exact False.elim (mappingAbsent ⟨markerSpan, openingSpan,
          rightMarker.1, by simpa [rightMarker.2] using rightOpening.1⟩)
    | proxy _ rightMarker _ _ =>
        cases typeTokenAt_kind_eq nameParsed.2.2.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨_, token⟩
        cases typeTokenAt_kind_eq nameParsed.2.2.1 token
    | named _ _ rightName rightResultEq rightArguments =>
        rcases nameParsed.result_unique rightName with ⟨nameEq, outEq⟩
        subst nameEq; subst outEq
        rcases argumentsIH rightArguments with ⟨argumentsEq, argumentsOutEq⟩
        subst argumentsEq
        exact resultEq.trans rightResultEq.symm
  · intro closing input closingSpan commaAbsent closingToken right
      rightClosing afterRight rightParsed
    cases rightParsed with
    | close _ rightClosingToken =>
        have tokenEq := closingToken.token_unique rightClosingToken
        cases tokenEq
        exact ⟨rfl, rfl, rfl⟩
    | trailing commaToken _ =>
        exact False.elim (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | next commaToken _ _ _ _ _ =>
        exact False.elim (typeTokenAbsent_conflicts_token commaAbsent commaToken)
  · intro closing input commaSpan closingSpan commaToken closingToken right
      rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | trailing _ rightClosingToken =>
        have tokenEq := closingToken.token_unique rightClosingToken
        cases tokenEq
        exact ⟨rfl, rfl, rfl⟩
    | next _ closingAbsent _ _ _ _ =>
        exact False.elim (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  · intro closing input afterElement output commaSpan closingSpan element
      elements values commaToken closingAbsent progress elementsEq elementParsed
      tail elementIH tailIH right rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | trailing _ rightClosing =>
        exact False.elim (typeTokenAbsent_conflicts_token closingAbsent rightClosing)
    | next _ _ _ rightElementsEq rightElement rightTail =>
        have elementEq := elementIH rightElement
        have outEq := elementParsed.output_unique rightElement
        subst elementEq; subst outEq
        rcases tailIH rightTail with ⟨tailEq, closingEq, outputEq⟩
        subst tailEq
        exact ⟨elementsEq.trans rightElementsEq.symm, closingEq, outputEq⟩
  · intro opening closing input values openingSpan closingSpan elementsEq
      spanEq openingToken closingToken right afterRight rightParsed
    cases rightParsed with
    | empty rightOpening rightClosing rightElementsEq rightSpanEq
          rightOpeningToken rightClosingToken =>
        have openingEq := congrArg (fun t : Token => t.span)
          (openingToken.token_unique rightOpeningToken)
        have closingEq := congrArg (fun t : Token => t.span)
          (closingToken.token_unique rightClosingToken)
        cases values; cases right; simp_all
    | nonempty _ _ closingAbsent _ _ _ _ _ _ _ _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  · intro opening closing input afterFirst output values first rest openingSpan
      closingSpan closingAbsent openingToken progress tokensEq endIndexEq
      elementsEq spanEq firstParsed tail firstIH tailIH right afterRight
      rightParsed
    cases rightParsed with
    | empty _ _ _ _ _ rightClosing =>
        exact False.elim
          (typeTokenAbsent_conflicts_token closingAbsent rightClosing)
    | nonempty rightOpening rightClosing _ rightOpeningToken _ _ _
          rightElementsEq rightSpanEq rightFirst rightTail =>
        have openingEq := congrArg (fun t : Token => t.span)
          (openingToken.token_unique rightOpeningToken)
        have firstEq := firstIH rightFirst
        have outEq := firstParsed.output_unique rightFirst
        subst firstEq; subst outEq
        rcases tailIH rightTail with ⟨restEq, closingEq, outputEq⟩
        subst restEq
        constructor
        · cases values; cases right; simp_all
        · exact outputEq
  · intro input openingAbsent right afterRight rightParsed
    cases rightParsed with
    | absent => exact ⟨rfl, rfl⟩
    | present _ _ openingToken _ _ _ _ _ _ _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token openingAbsent openingToken)
  · intro input afterFirst output arguments first rest openingSpan closingSpan
      openingToken progress tokensEq endIndexEq elementsEq spanEq firstParsed
      tail firstIH tailIH right afterRight rightParsed
    cases rightParsed with
    | absent rightAbsent =>
        exact False.elim
          (typeTokenAbsent_conflicts_token rightAbsent openingToken)
    | @present rightInput rightAfterFirst rightOutput rightArguments rightFirst
          rightRest rightOpening rightClosing rightOpeningToken rightProgress
          rightTokensEq rightEndIndexEq rightElementsEq rightSpanEq
          rightFirstParsed rightTail =>
        have openingEq := congrArg (fun t : Token => t.span)
          (openingToken.token_unique rightOpeningToken)
        change openingSpan = rightOpening at openingEq
        have firstEq := firstIH rightFirstParsed
        have outEq := firstParsed.output_unique rightFirstParsed
        subst firstEq; subst outEq
        rcases tailIH rightTail with ⟨restEq, closingEq, outputEq⟩
        subst restEq
        have coverEq : SourceSpan.cover openingSpan closingSpan =
            SourceSpan.cover rightOpening rightClosing := by
          rw [openingEq, closingEq]
        have argumentsEq : arguments = rightArguments :=
          nonemptyDelimited_eq_of_toList_eq
            (spanEq.trans (coverEq.trans rightSpanEq.symm))
            (elementsEq.trans rightElementsEq.symm)
        exact ⟨congrArg some argumentsEq, outputEq⟩
  · intro input markerAbsent right afterRight rightParsed
    cases rightParsed with
    | absent => exact ⟨rfl, rfl⟩
    | present _ markerToken _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token markerAbsent markerToken.1)
  · intro input afterMarker output values markerSpan markerToken valuesParsed
      valuesIH right afterRight rightParsed
    cases rightParsed with
    | absent markerAbsent =>
        exact False.elim
          (typeTokenAbsent_conflicts_token markerAbsent markerToken.1)
    | present _ rightMarker rightValues =>
        have outEq := markerToken.output_unique rightMarker
        subst outEq
        rcases valuesIH rightValues with ⟨valuesEq, valuesOutEq⟩
        subst valuesEq
        exact ⟨rfl, valuesOutEq⟩
end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeCompositeSuccessExactnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeBranchRejectionExactnessProperties
/-! Exact rejection endpoints for each recursive Core type branch. -/
set_option autoImplicit false
namespace Solcore.Syntax.DeclarativeGrammar
/-- A selected function-return suffix has one rejecting endpoint. -/
theorem FunctionTypeReturnsRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : FunctionTypeReturnsRejects nestedRejects input left)
    (rightRejects : FunctionTypeReturnsRejects nestedRejects input right) :
    left = right := by
  cases leftRejects with
  | valuesRejected _ leftMarker leftValues =>
      cases rightRejects with
      | valuesRejected _ rightMarker rightValues =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact leftValues.output_unique outcomes rightValues

/-- A selected function type has one first rejecting endpoint. -/
theorem FunctionTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : FunctionTypeRejects nestedRejects input left)
    (rightRejects : FunctionTypeRejects nestedRejects input right) :
    left = right := by
  cases leftRejects with
  | parametersRejected _ leftKeyword leftParameters =>
      cases rightRejects with
      | parametersRejected _ rightKeyword rightParameters =>
          have afterKeywordEq := leftKeyword.output_unique rightKeyword
          subst afterKeywordEq
          exact leftParameters.output_unique outcomes rightParameters
      | returnsRejected _ rightKeyword rightParameters rightReturns =>
          have afterKeywordEq := leftKeyword.output_unique rightKeyword
          subst afterKeywordEq
          exact False.elim
            (leftParameters.disjointAllowEmptyTrailing
              outcomes.toDeterministicOutcomeSpec (fun parsed => parsed)
              ⟨_, _, rightParameters⟩)
  | returnsRejected _ leftKeyword leftParameters leftReturns =>
      cases rightRejects with
      | parametersRejected _ rightKeyword rightParameters =>
          have afterKeywordEq := leftKeyword.output_unique rightKeyword
          subst afterKeywordEq
          exact False.elim
            (rightParameters.disjointAllowEmptyTrailing
              outcomes.toDeterministicOutcomeSpec (fun parsed => parsed)
              ⟨_, _, leftParameters⟩)
      | returnsRejected _ rightKeyword rightParameters rightReturns =>
          have afterKeywordEq := leftKeyword.output_unique rightKeyword
          subst afterKeywordEq
          have afterParametersEq := TrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := TypeExprParses) outcomes.successOutputUnique
            leftParameters rightParameters
          subst afterParametersEq
          exact leftReturns.output_unique outcomes rightReturns

/-- A selected `comptime` type has one first rejecting endpoint. -/
theorem ComptimeTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : ComptimeTypeRejects nestedRejects input left)
    (rightRejects : ComptimeTypeRejects nestedRejects input right) :
    left = right := by
  cases leftRejects with
  | innerRejected _ _ leftMarker leftOpening leftInner =>
      cases rightRejects with
      | innerRejected _ _ rightMarker rightOpening rightInner =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact outcomes.rejectOutputUnique leftInner rightInner
      | closingMissing _ _ rightMarker rightOpening rightInner _ =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact False.elim
            (outcomes.successRejectDisjoint leftInner ⟨_, _, rightInner⟩)
  | closingMissing _ _ leftMarker leftOpening leftInner _ =>
      cases rightRejects with
      | innerRejected _ _ rightMarker rightOpening rightInner =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact False.elim
            (outcomes.successRejectDisjoint rightInner ⟨_, _, leftInner⟩)
      | closingMissing _ _ rightMarker rightOpening rightInner _ =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          have afterOpeningEq := leftOpening.output_unique rightOpening
          subst afterOpeningEq
          exact outcomes.successOutputUnique leftInner rightInner

private theorem mappingPrefixOutputUnique
    {input leftMarker rightMarker leftOpening rightOpening : Remainder}
    {leftMarkerSpan rightMarkerSpan leftOpeningSpan rightOpeningSpan :
      SourceSpan}
    (leftMarkerParsed : ExactTokenParses
      (.identifier ContextualKeyword.mapping.spelling)
      input leftMarkerSpan leftMarker)
    (leftOpeningParsed : ExactTokenParses (.symbol .leftParen)
      leftMarker leftOpeningSpan leftOpening)
    (rightMarkerParsed : ExactTokenParses
      (.identifier ContextualKeyword.mapping.spelling)
      input rightMarkerSpan rightMarker)
    (rightOpeningParsed : ExactTokenParses (.symbol .leftParen)
      rightMarker rightOpeningSpan rightOpening) :
    leftOpening = rightOpening := by
  have markerEq := leftMarkerParsed.output_unique rightMarkerParsed
  subst markerEq
  exact leftOpeningParsed.output_unique rightOpeningParsed

/-- A selected mapping type has one endpoint across all four stages. -/
theorem MappingTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : MappingTypeRejects nestedRejects input left)
    (rightRejects : MappingTypeRejects nestedRejects input right) :
    left = right := by
  cases leftRejects with
  | keyRejected _ _ leftMarker leftOpening leftRejected =>
      cases rightRejects with
      | keyRejected _ _ rightMarker rightOpening rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftRejected
          exact outcomes.rejectOutputUnique leftRejected rightRejected
      | arrowMissing _ _ rightMarker rightOpening rightKey _
      | valueRejected _ _ _ rightMarker rightOpening rightKey _ _
      | closingMissing _ _ _ rightMarker rightOpening rightKey _ _ _ =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftRejected
          exact False.elim
            (outcomes.successRejectDisjoint leftRejected ⟨_, _, rightKey⟩)
  | arrowMissing _ _ leftMarker leftOpening leftKey leftArrowAbsent =>
      cases rightRejects with
      | keyRejected _ _ rightMarker rightOpening rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          exact False.elim
            (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftKey⟩)
      | arrowMissing _ _ rightMarker rightOpening rightKey _ =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          exact outcomes.successOutputUnique leftKey rightKey
      | valueRejected _ _ _ rightMarker rightOpening rightKey rightArrow _
      | closingMissing _ _ _ rightMarker rightOpening rightKey rightArrow _ _ =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          exact False.elim
            (typeTokenAbsent_conflicts_token leftArrowAbsent rightArrow.1)
  | valueRejected _ _ _ leftMarker leftOpening leftKey leftArrow
        leftRejected =>
      cases rightRejects with
      | keyRejected _ _ rightMarker rightOpening rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          exact False.elim
            (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftKey⟩)
      | arrowMissing _ _ rightMarker rightOpening rightKey rightArrowAbsent =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          exact False.elim
            (typeTokenAbsent_conflicts_token rightArrowAbsent leftArrow.1)
      | valueRejected _ _ _ rightMarker rightOpening rightKey rightArrow
          rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          rw [leftArrow.output_unique rightArrow] at leftRejected
          exact outcomes.rejectOutputUnique leftRejected rightRejected
      | closingMissing _ _ _ rightMarker rightOpening rightKey rightArrow
          rightValue _ =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          rw [leftArrow.output_unique rightArrow] at leftRejected
          exact False.elim
            (outcomes.successRejectDisjoint leftRejected ⟨_, _, rightValue⟩)
  | closingMissing _ _ _ leftMarker leftOpening leftKey leftArrow leftValue
        _ =>
      cases rightRejects with
      | keyRejected _ _ rightMarker rightOpening rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          exact False.elim
            (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftKey⟩)
      | arrowMissing _ _ rightMarker rightOpening rightKey rightArrowAbsent =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          exact False.elim
            (typeTokenAbsent_conflicts_token rightArrowAbsent leftArrow.1)
      | valueRejected _ _ _ rightMarker rightOpening rightKey rightArrow
          rightRejected =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          rw [leftArrow.output_unique rightArrow] at leftValue
          exact False.elim
            (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftValue⟩)
      | closingMissing _ _ _ rightMarker rightOpening rightKey rightArrow
          rightValue _ =>
          rw [mappingPrefixOutputUnique leftMarker leftOpening rightMarker
            rightOpening] at leftKey
          have keyEq := outcomes.successOutputUnique leftKey rightKey
          subst keyEq
          rw [leftArrow.output_unique rightArrow] at leftValue
          exact outcomes.successOutputUnique leftValue rightValue

/-- A selected proxy type has one nested rejecting endpoint. -/
theorem ProxyTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : ProxyTypeRejects nestedRejects input left)
    (rightRejects : ProxyTypeRejects nestedRejects input right) : left = right := by
  cases leftRejects with
  | innerRejected _ leftMarker leftInner =>
      cases rightRejects with
      | innerRejected _ rightMarker rightInner =>
          have afterMarkerEq := leftMarker.output_unique rightMarker
          subst afterMarkerEq
          exact outcomes.rejectOutputUnique leftInner rightInner

/-- A selected tuple type has one delimiter or nested rejecting endpoint. -/
theorem TupleTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : TupleTypeRejects nestedRejects input left)
    (rightRejects : TupleTypeRejects nestedRejects input right) : left = right := by
  cases leftRejects with
  | selected _ _ leftValues =>
      cases rightRejects with
      | selected _ _ rightValues =>
          exact leftValues.output_unique outcomes rightValues

/-- Selected named-type arguments have one rejecting endpoint. -/
theorem NamedTypeArgumentsRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : NamedTypeArgumentsRejects nestedRejects input left)
    (rightRejects : NamedTypeArgumentsRejects nestedRejects input right) :
    left = right := by
  cases leftRejects with
  | selected _ _ leftValues =>
      cases rightRejects with
      | selected _ _ rightValues =>
          exact leftValues.output_unique outcomes rightValues

/-- A selected named type has one name or argument rejecting endpoint. -/
theorem NamedTypeRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : NamedTypeRejects nestedRejects input left)
    (rightRejects : NamedTypeRejects nestedRejects input right) : left = right := by
  cases leftRejects with
  | nameRejected leftName =>
      cases rightRejects with
      | nameRejected rightName => exact leftName.output_unique rightName
      | argumentsRejected rightName rightArguments =>
          exact False.elim
            (leftName.disjointQualified ⟨_, _, rightName⟩)
  | argumentsRejected leftName leftArguments =>
      cases rightRejects with
      | nameRejected rightName =>
          exact False.elim
            (rightName.disjointQualified ⟨_, _, leftName⟩)
      | argumentsRejected rightName rightArguments =>
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          exact leftArguments.output_unique outcomes rightArguments

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeDispatcherRejectionExactnessProperties
/-! Exact rejection endpoints for one prioritized Core type fuel layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem functionSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : FunctionTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .functionKw)) : False := by
  rcases selected.keyword_token with ⟨_, token⟩
  exact typeTokenAbsent_conflicts_token absent token

private theorem comptimeSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : ComptimeTypeRejects nestedRejects input rejected)
    (absent : ContextualSymbolPairAbsentAt input .comptime .less) : False := by
  rcases selected.prefix_tokens with ⟨markerSpan, openingSpan, marker,
    opening⟩
  exact absent ⟨markerSpan, openingSpan, marker, opening⟩

private theorem mappingSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : MappingTypeRejects nestedRejects input rejected)
    (absent : ContextualSymbolPairAbsentAt input .mapping .leftParen) :
    False := by
  rcases selected.prefix_tokens with ⟨markerSpan, openingSpan, marker,
    opening⟩
  exact absent ⟨markerSpan, openingSpan, marker, opening⟩

private theorem proxySelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : ProxyTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .at)) : False := by
  cases selected with
  | innerRejected _ marker _ =>
      exact typeTokenAbsent_conflicts_token absent marker.1

private theorem tupleSelected_conflicts_absent
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (selected : TupleTypeRejects nestedRejects input rejected)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen)) : False := by
  cases selected with
  | selected _ opening _ =>
      exact typeTokenAbsent_conflicts_token absent opening.1

/-- One prioritized Core type dispatcher layer has one first rejecting
endpoint whenever its recursive child outcomes are exact. -/
theorem TypeExprCoreRejects.output_unique
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : TypeExprCoreRejects nestedRejects input left)
    (rightRejects : TypeExprCoreRejects nestedRejects input right) :
    left = right := by
  cases leftRejects <;> cases rightRejects
  all_goals first
    | exact FunctionTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact ComptimeTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact MappingTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact ProxyTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact TupleTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact NamedTypeRejects.output_unique outcomes
        (by assumption) (by assumption)
    | exact False.elim
        (functionSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (comptimeSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (mappingSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (proxySelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        (tupleSelected_conflicts_absent (by assumption) (by assumption))
    | exact False.elim
        ((by assumption : IdentifierAbsentAt input) (by assumption))
    | rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
/-! Full value and rejection-endpoint functionality for recursive Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recursive Core type success fixes its AST and final remainder. -/
theorem TypeExprParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprParses input left afterLeft)
    (rightParsed : TypeExprParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Every executable recursion-fuel layer has exact success values and exact
rejection endpoints. -/
theorem typeExprExactOutcomeSpecWithFuel :
    ∀ fuel, ExactDeterministicOutcomeSpec TypeExprOrdinaryParses
      (TypeExprRejectsWithFuel fuel)
  | 0 => {
      toDeterministicOutcomeSpec := typeExprDeterministicOutcomeSpecWithFuel 0
      successValueUnique := TypeExprParses.value_unique
      rejectOutputUnique := by
        simp [TypeExprRejectsWithFuel]
    }
  | fuel + 1 =>
      let nestedOutcomes := typeExprExactOutcomeSpecWithFuel fuel
      {
        toDeterministicOutcomeSpec :=
          typeExprDeterministicOutcomeSpecWithFuel (fuel + 1)
        successValueUnique := TypeExprParses.value_unique
        rejectOutputUnique :=
          TypeExprCoreRejects.output_unique nestedOutcomes
      }

/-- Public Core type rejection has one exact first failing endpoint. -/
theorem TypeExprRejects.output_unique
    {input left right : Remainder}
    (leftRejects : TypeExprRejects input left)
    (rightRejects : TypeExprRejects input right) : left = right :=
  (typeExprExactOutcomeSpecWithFuel
    (typeExprPublicFuel input)).rejectOutputUnique leftRejects rightRejects

/-- The public recursive Core type grammar has fully exact ordinary outcomes. -/
theorem typeExprExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeExprOrdinaryParses TypeExprRejects where
  toDeterministicOutcomeSpec := typeExprDeterministicOutcomeSpec
  successValueUnique := TypeExprParses.value_unique
  rejectOutputUnique := TypeExprRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
