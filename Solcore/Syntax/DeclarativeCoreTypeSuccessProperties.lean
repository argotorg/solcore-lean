import Solcore.Syntax.DeclarativeCoreTypePrimitiveProperties
/-! Output functionality of the recursive parser-independent Core-type grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private def typeExprOutputMotive (input : Remainder)
    (value : Syntax.TypeExpr) (output : Remainder)
    (_ : TypeExprParses input value output) : Prop :=
  ∀ {right afterRight}, TypeExprParses input right afterRight →
      output = afterRight
private def typeTailOutputMotive (closing : Symbol) (input : Remainder)
    (values : List Syntax.TypeExpr) (closingSpan : SourceSpan)
    (output : Remainder)
    (_ : TypeExprTrailingDelimitedTailParses closing input values closingSpan
      output) : Prop :=
  ∀ {right rightClosing afterRight},
    TypeExprTrailingDelimitedTailParses closing input right rightClosing
      afterRight → output = afterRight
private def typeListOutputMotive (opening closing : Symbol)
    (input : Remainder) (value : DelimitedList Syntax.TypeExpr)
    (output : Remainder)
    (_ : TypeExprTrailingDelimitedListParses opening closing input value output) :
    Prop :=
  ∀ {right afterRight},
    TypeExprTrailingDelimitedListParses opening closing input right afterRight →
      output = afterRight

private def typeArgumentsOutputMotive (input : Remainder)
    (value : Option (NonemptyDelimitedList Syntax.TypeExpr))
    (output : Remainder)
    (_ : OptionalNamedTypeArgumentsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalNamedTypeArgumentsParses input right
    afterRight → output = afterRight

private def typeReturnsOutputMotive (input : Remainder)
    (value : Option (DelimitedList Syntax.TypeExpr)) (output : Remainder)
    (_ : OptionalFunctionTypeReturnsParses input value output) : Prop :=
  ∀ {right afterRight}, OptionalFunctionTypeReturnsParses input right
    afterRight → output = afterRight

/-- Recursive Core type parsing has a unique output remainder. -/
theorem TypeExprParses.output_unique {input : Remainder}
    {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeExprParses input left afterLeft)
    (rightParsed : TypeExprParses input right afterRight) :
    afterLeft = afterRight := by
  refine TypeExprParses.rec
    (motive_1 := typeExprOutputMotive)
    (motive_2 := typeTailOutputMotive)
    (motive_3 := typeListOutputMotive)
    (motive_4 := typeArgumentsOutputMotive)
    (motive_5 := typeReturnsOutputMotive)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ leftParsed rightParsed
  · intro input afterKeyword afterParameters output result parameters returns
      keywordSpan keywordToken resultEq parametersParsed returnsParsed
      parametersIH returnsIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ rightParameters rightReturns =>
        have afterKeywordEq := typeExactToken_output_unique keywordToken
          rightKeyword
        subst afterKeywordEq
        have afterParametersEq := parametersIH rightParameters
        subst afterParametersEq
        exact returnsIH rightReturns
    | comptime _ _ _ rightMarker _ _ _ _ =>
        cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | proxy _ rightMarker _ _ =>
        cases typeTokenAt_kind_eq keywordToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq keywordToken.1 token
    | named _ _ rightName _ _ =>
        cases typeTokenAt_kind_eq keywordToken.1 rightName.2.2.1
  · intro input afterMarker afterOpening afterInner output result inner
      markerSpan openingSpan closingSpan markerToken openingToken closingToken
      resultEq innerParsed innerIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker rightOpening rightClosing _ rightInner =>
        have afterMarkerEq := typeExactToken_output_unique markerToken rightMarker
        subst afterMarkerEq
        have afterOpeningEq := typeExactToken_output_unique openingToken
          rightOpening
        subst afterOpeningEq
        have afterInnerEq := innerIH rightInner
        subst afterInnerEq
        exact typeExactToken_output_unique closingToken rightClosing
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        have impossible := typeTokenAt_kind_eq markerToken.1 rightMarker.1
        simp [ContextualKeyword.spelling] at impossible
    | proxy _ rightMarker _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named comptimeAbsent _ _ _ _ =>
        have openingAtInput : TokenAt input.tokens input.endIndex
            (input.cursor + 1) { span := openingSpan, value := .symbol .less } :=
          by simpa [markerToken.2] using openingToken.1
        exact False.elim (comptimeAbsent
          ⟨markerSpan, openingSpan, markerToken.1, openingAtInput⟩)
  · intro input afterMarker afterOpening afterKey afterArrow afterValue output
      result key value markerSpan openingSpan arrowSpan closingSpan markerToken
      openingToken arrowToken closingToken resultEq keyParsed valueParsed keyIH
      valueIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ =>
        have impossible := typeTokenAt_kind_eq markerToken.1 rightMarker.1
        simp [ContextualKeyword.spelling] at impossible
    | mapping _ _ _ _ rightMarker rightOpening rightArrow rightClosing _
        rightKey rightValue =>
        have afterMarkerEq := typeExactToken_output_unique markerToken rightMarker
        subst afterMarkerEq
        have afterOpeningEq := typeExactToken_output_unique openingToken
          rightOpening
        subst afterOpeningEq
        have afterKeyEq := keyIH rightKey
        subst afterKeyEq
        have afterArrowEq := typeExactToken_output_unique arrowToken rightArrow
        subst afterArrowEq
        have afterValueEq := valueIH rightValue
        subst afterValueEq
        exact typeExactToken_output_unique closingToken rightClosing
    | proxy _ rightMarker _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named _ mappingAbsent _ _ _ =>
        have openingAtInput : TokenAt input.tokens input.endIndex
            (input.cursor + 1) {
              span := openingSpan
              value := .symbol .leftParen
            } := by simpa [markerToken.2] using openingToken.1
        exact False.elim (mappingAbsent
          ⟨markerSpan, openingSpan, markerToken.1, openingAtInput⟩)
  · intro input afterMarker output result inner markerSpan markerToken resultEq
      innerParsed innerIH right afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightMarker.1
    | proxy _ rightMarker _ rightInner =>
        have afterMarkerEq := typeExactToken_output_unique markerToken rightMarker
        subst afterMarkerEq
        exact innerIH rightInner
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq markerToken.1 token
    | named _ _ rightName _ _ =>
        cases typeTokenAt_kind_eq markerToken.1 rightName.2.2.1
  · intro input output result values resultEq valuesParsed valuesIH right
      afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        rcases valuesParsed.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq token rightKeyword.1
    | comptime _ _ _ rightMarker _ _ _ _ =>
        rcases valuesParsed.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq token rightMarker.1
    | mapping _ _ _ _ rightMarker _ _ _ _ _ _ =>
        rcases valuesParsed.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq token rightMarker.1
    | proxy _ rightMarker _ _ =>
        rcases valuesParsed.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq token rightMarker.1
    | tuple _ rightValues => exact valuesIH rightValues
    | named _ _ rightName _ _ =>
        rcases valuesParsed.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq token rightName.2.2.1
  · intro input afterName output result name arguments comptimeAbsent
      mappingAbsent nameParsed resultEq argumentsParsed argumentsIH right
      afterRight rightParsed
    cases rightParsed with
    | function _ rightKeyword _ _ _ =>
        cases typeTokenAt_kind_eq nameParsed.2.2.1 rightKeyword.1
    | comptime markerSpan openingSpan _ rightMarker rightOpening _ _ _ =>
        have openingAtInput : TokenAt input.tokens input.endIndex
            (input.cursor + 1) { span := openingSpan, value := .symbol .less } :=
          by simpa [rightMarker.2] using rightOpening.1
        exact False.elim (comptimeAbsent
          ⟨markerSpan, openingSpan, rightMarker.1, openingAtInput⟩)
    | mapping markerSpan openingSpan _ _ rightMarker rightOpening _ _ _ _ _ =>
        have openingAtInput : TokenAt input.tokens input.endIndex
            (input.cursor + 1) {
              span := openingSpan
              value := .symbol .leftParen
            } := by simpa [rightMarker.2] using rightOpening.1
        exact False.elim (mappingAbsent
          ⟨markerSpan, openingSpan, rightMarker.1, openingAtInput⟩)
    | proxy _ rightMarker _ _ =>
        cases typeTokenAt_kind_eq nameParsed.2.2.1 rightMarker.1
    | tuple _ rightValues =>
        rcases rightValues.opening_token with ⟨span, token⟩
        cases typeTokenAt_kind_eq nameParsed.2.2.1 token
    | named _ _ rightName _ rightArguments =>
        have afterNameEq := nameParsed.output_unique rightName
        subst afterNameEq
        exact argumentsIH rightArguments
  · intro closing input closingSpan commaAbsent closingToken right rightClosing
      afterRight rightParsed
    cases rightParsed with
    | close => rfl
    | trailing commaToken _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | next commaToken _ _ _ _ _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token commaAbsent commaToken)
  · intro closing input commaSpan closingSpan commaToken closingToken right
      rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | trailing => rfl
    | next _ closingAbsent _ _ _ _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  · intro closing input afterElement output commaSpan closingSpan element
      elements values commaToken closingAbsent progress elementsEq elementParsed
      tail elementIH tailIH right rightClosing afterRight rightParsed
    cases rightParsed with
    | close commaAbsent _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token commaAbsent commaToken)
    | trailing _ rightClosing =>
        exact False.elim
          (typeTokenAbsent_conflicts_token closingAbsent rightClosing)
    | next _ _ _ _ rightElement rightTail =>
        have afterElementEq := elementIH rightElement
        subst afterElementEq
        exact tailIH rightTail
  · intro opening closing input values openingSpan closingSpan elementsEq spanEq
      openingToken closingToken right afterRight rightParsed
    cases rightParsed with
    | empty => rfl
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
    | nonempty _ _ _ _ _ _ _ _ _ rightFirst rightTail =>
        have afterFirstEq := firstIH rightFirst
        subst afterFirstEq
        exact tailIH rightTail
  · intro input openingAbsent right afterRight rightParsed
    cases rightParsed with
    | absent => rfl
    | present _ _ openingToken _ _ _ _ _ _ _ =>
        exact False.elim
          (typeTokenAbsent_conflicts_token openingAbsent openingToken)
  · intro input afterFirst output arguments first rest openingSpan closingSpan
      openingToken progress tokensEq endIndexEq elementsEq spanEq firstParsed
      tail firstIH tailIH right afterRight rightParsed
    cases rightParsed with
    | absent openingAbsent =>
        exact False.elim
          (typeTokenAbsent_conflicts_token openingAbsent openingToken)
    | present _ _ _ _ _ _ _ _ rightFirst rightTail =>
        have afterFirstEq := firstIH rightFirst
        subst afterFirstEq
        exact tailIH rightTail
  · intro input markerAbsent right afterRight rightParsed
    cases rightParsed with
    | absent => rfl
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
        have afterMarkerEq := typeExactToken_output_unique markerToken
          rightMarker
        subst afterMarkerEq
        exact valuesIH rightValues

end Solcore.Syntax.DeclarativeGrammar
