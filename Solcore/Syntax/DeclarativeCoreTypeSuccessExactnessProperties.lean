import Solcore.Syntax.DeclarativeCoreTypeSuccessExactnessMotive

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
