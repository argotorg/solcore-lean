import Solcore.Syntax.Grammar.Types
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Internal.DelimitedOutcomes

/-!
Properties of the declarative grammar of core types and qualified names: outcomes are
deterministic, and successful values and rejection points are unique. Nothing here
mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeTypeDispatchSelectionProperties
/-! The explicit prioritized selectors determine at most one branch. This is
selection uniqueness, not existence of a successful or rejected type outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TypeDispatchPairPresent.exact_prefix {input : Remainder}
    {keyword : ContextualKeyword} {symbol : Symbol}
    (present : TypeDispatchPairPresent input keyword symbol) :
    ∃ markerSpan openingSpan afterMarker afterOpening,
      ExactTokenParses (.identifier keyword.spelling) input markerSpan afterMarker ∧
      ExactTokenParses (.symbol symbol) afterMarker openingSpan afterOpening := by
  rcases present with ⟨markerSpan, openingSpan, marker, opening⟩
  exact ⟨markerSpan, openingSpan, _, _, ⟨marker, rfl⟩, ⟨opening, rfl⟩⟩

theorem TypeDispatchSelects.branch_unique {input : Remainder} {left right : TypeDispatchBranch}
    (leftSelected : TypeDispatchSelects input left) (rightSelected : TypeDispatchSelects input right) :
    left = right := by
  cases leftSelected <;> cases rightSelected <;>
    grind only [TokenKindAbsentAt, ContextualSymbolPairAbsentAt, TypeDispatchPairPresent, IdentifierAbsentAt]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypePrimitiveProperties
/-! Primitive functionality facts used by declarative Core-type outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem typeTokenAbsent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

theorem typeTokenAt_kind_eq {tokens : Array Token} {endIndex index : Nat}
    {leftKind rightKind : TokenKind} {leftSpan rightSpan : SourceSpan}
    (left : TokenAt tokens endIndex index {
      span := leftSpan
      value := leftKind
    })
    (right : TokenAt tokens endIndex index {
      span := rightSpan
      value := rightKind
    }) : leftKind = rightKind := by
  have tokenEq : ({ span := leftSpan, value := leftKind } : Token) =
      { span := rightSpan, value := rightKind } := by
    apply Option.some.inj
    rw [← left.2, ← right.2]
  exact congrArg (fun token : Token => token.value) tokenEq

theorem typeExactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (left : ExactTokenParses kind input leftSpan leftOutput)
    (right : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [left.2, right.2]

/-- Two consecutive exact tokens witness a contextual dispatch guard. -/
theorem contextualPair_present_of_exact
    {keyword : ContextualKeyword} {symbol : Symbol}
    {input afterMarker afterOpening : Remainder}
    {markerSpan openingSpan : SourceSpan}
    (markerParsed : ExactTokenParses (.identifier keyword.spelling) input
      markerSpan afterMarker)
    (openingParsed : ExactTokenParses (.symbol symbol) afterMarker
      openingSpan afterOpening) :
    ∃ markerSpan openingSpan,
      TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .identifier keyword.spelling
      } ∧ TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := openingSpan
        value := .symbol symbol
      } := by
  refine ⟨markerSpan, openingSpan, markerParsed.1, ?_⟩
  simpa [markerParsed.2] using openingParsed.1

private theorem DottedIdentifierTailParses.output_unique
    {tokens : Array Token} {endIndex cursor : Nat}
    {left right : List Syntax.Identifier} {afterLeft afterRight : Nat}
    (leftParsed : DottedIdentifierTailParses tokens endIndex cursor left
      afterLeft)
    (rightParsed : DottedIdentifierTailParses tokens endIndex cursor right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done cursor stopped =>
      cases rightParsed with
      | done => rfl
      | next dotSpan dotToken componentToken tail =>
          exact False.elim
            (typeTokenAbsent_conflicts_token stopped dotToken)
  | next dotSpan dotToken componentToken tail inductionHypothesis =>
      cases rightParsed with
      | done cursor stopped =>
          exact False.elim
            (typeTokenAbsent_conflicts_token stopped dotToken)
      | next => exact inductionHypothesis (by assumption)

/-- Qualified-name recognition has one output remainder. -/
theorem QualifiedNameParses.output_unique {input : Remainder}
    {left right : Syntax.QualifiedName} {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftTokens, leftEndIndex, leftFirst, leftTail, leftSpan⟩
  rcases rightParsed with
    ⟨rightTokens, rightEndIndex, rightFirst, rightTail, rightSpan⟩
  have cursorEq := DottedIdentifierTailParses.output_unique leftTail rightTail
  cases input
  cases afterLeft
  cases afterRight
  simp_all

/-- Every recursive type list exposes its exact opening token. -/
theorem TypeExprTrailingDelimitedListParses.opening_token
    {opening closing : Symbol} {input output : Remainder}
    {values : DelimitedList Syntax.TypeExpr}
    (parsed : TypeExprTrailingDelimitedListParses opening closing input values
      output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .symbol opening
    } := by
  cases parsed with
  | empty openingSpan => exact ⟨openingSpan, by assumption⟩
  | nonempty openingSpan => exact ⟨openingSpan, by assumption⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeSuccessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeListOutcomeProperties
/-! Disjointness of generic list rejection from recursive Core-type lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Generic and recursive successful type tails end at the same cursor. -/
theorem TrailingDelimitedTailParses.output_uniqueTypeTail
    {closing : Symbol} {input : Remainder}
    {left right : List Syntax.TypeExpr}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedTailParses closing TypeExprParses input
      left leftClosing afterLeft)
    (rightParsed : TypeExprTrailingDelimitedTailParses closing input right
      rightClosing afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right rightClosing afterRight with
  | close commaAbsent closingToken =>
      cases rightParsed with
      | close => rfl
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
      | trailing => rfl
      | next _ closingAbsent _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  | next commaToken closingAbsent elementParsed progress tail
        inductionHypothesis =>
      cases rightParsed with
      | close commaAbsent _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token commaAbsent commaToken)
      | trailing _ closingToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
      | next _ _ _ _ successfulElement successfulTail =>
          have outputEq := TypeExprParses.output_unique elementParsed
            successfulElement
          subst outputEq
          exact inductionHypothesis successfulTail

/-- Generic and recursive successful type lists end at the same cursor. -/
theorem TrailingDelimitedListParses.output_uniqueTypeList
    {opening closing : Symbol} {input : Remainder}
    {left right : DelimitedList Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TrailingDelimitedListParses opening closing TypeExprParses
      input left afterLeft)
    (rightParsed : TypeExprTrailingDelimitedListParses opening closing input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | empty _ _ _ closingToken =>
      cases rightParsed with
      | empty => rfl
      | nonempty _ _ closingAbsent _ _ _ _ _ _ _ _ =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      cases rightParsed with
      | empty _ _ _ _ _ closingToken =>
          exact False.elim
            (typeTokenAbsent_conflicts_token closingAbsent closingToken)
      | nonempty _ _ _ _ _ _ _ _ _ successfulFirst successfulTail =>
          have outputEq := TypeExprParses.output_unique firstParsed
            successfulFirst
          subst outputEq
          exact tail.output_uniqueTypeTail successfulTail

/-- A generic trailing-tail rejection excludes the recursive type-tail
success judgment used by `TypeExprParses`. -/
theorem DelimitedTailRejects.disjointTypeTail
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {closing : Symbol} {input rejected : Remainder}
    (rejection : DelimitedTailRejects closing true TypeExprParses
      nestedRejects input rejected) :
    ¬ ∃ values closingSpan output,
      TypeExprTrailingDelimitedTailParses closing input values closingSpan
        output := by
  induction rejection with
  | delimiterMissing commaAbsent closingAbsent =>
      rintro ⟨values, closingSpan, output, parsed⟩
      cases parsed with
      | close _ closingToken =>
          exact typeTokenAbsent_conflicts_token closingAbsent closingToken
      | trailing commaToken _ =>
          exact typeTokenAbsent_conflicts_token commaAbsent commaToken
      | next commaToken _ _ _ _ _ =>
          exact typeTokenAbsent_conflicts_token commaAbsent commaToken
  | elementRejected commaSpan commaToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨values, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact typeTokenAbsent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | next _ _ _ _ elementParsed _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, elementParsed⟩
  | laterRejected commaSpan commaToken continues elementParsed progress
        tailRejected inductionHypothesis =>
      cases continues with
      | absent closingAbsent =>
          rintro ⟨values, closingSpan, output, parsed⟩
          cases parsed with
          | close commaAbsent _ =>
              exact typeTokenAbsent_conflicts_token commaAbsent commaToken
          | trailing _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | next _ _ _ _ successfulElement successfulTail =>
              have outputEq := outcomes.successOutputUnique elementParsed
                successfulElement
              subst outputEq
              exact inductionHypothesis ⟨_, _, _, successfulTail⟩

/-- A generic allow-empty/trailing list rejection excludes the recursive
type-list success judgment. -/
theorem DelimitedListRejects.disjointTypeList
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {opening closing : Symbol} {input rejected : Remainder}
    (rejection : DelimitedListRejects opening closing true true
      TypeExprParses nestedRejects input rejected) :
    ¬ ∃ values output,
      TypeExprTrailingDelimitedListParses opening closing input values
        output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | openingMissing openingAbsent =>
      rcases successful.opening_token with ⟨span, openingToken⟩
      exact typeTokenAbsent_conflicts_token openingAbsent openingToken
  | firstRejected openingSpan openingToken continues nestedRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ _ _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | nonempty _ _ _ _ _ _ _ _ _ firstParsed _ =>
              exact outcomes.successRejectDisjoint nestedRejected
                ⟨_, _, firstParsed⟩
  | tailRejected openingSpan openingToken continues firstParsed progress
        tailRejected =>
      cases continues with
      | absent closingAbsent =>
          cases successful with
          | empty _ _ _ _ _ closingToken =>
              exact typeTokenAbsent_conflicts_token closingAbsent closingToken
          | nonempty _ _ _ _ _ _ _ _ _ successfulFirst successfulTail =>
              have outputEq := outcomes.successOutputUnique firstParsed
                successfulFirst
              subst outputEq
              exact tailRejected.disjointTypeTail outcomes
                ⟨_, _, _, successfulTail⟩

/-- A selected nonempty named-type argument rejection excludes the optional
argument success branch. -/
theorem DelimitedListRejects.disjointNamedTypeArguments
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected : Remainder}
    (rejection : DelimitedListRejects .less .greater false true
      TypeExprParses nestedRejects input rejected) :
    ¬ ∃ arguments output,
      OptionalNamedTypeArgumentsParses input (some arguments) output := by
  rintro ⟨arguments, output, successful⟩
  cases successful with
  | present openingSpan closingSpan successfulOpening progress tokensEq
        endIndexEq elementsEq spanEq successfulFirst successfulTail =>
      cases rejection with
      | openingMissing openingAbsent =>
          exact typeTokenAbsent_conflicts_token openingAbsent
            successfulOpening
      | firstRejected _ _ continues nestedRejected =>
          cases continues
          exact outcomes.successRejectDisjoint nestedRejected
            ⟨_, _, successfulFirst⟩
      | tailRejected _ _ continues firstParsed _ tailRejected =>
          cases continues
          have outputEq := outcomes.successOutputUnique firstParsed
            successfulFirst
          subst outputEq
          exact tailRejected.disjointTypeTail outcomes
            ⟨_, _, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties
/-! Disjointness facts for recursive Core-type qualified names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact qualified-name-tail rejection excludes a dotted-tail success. -/
theorem TypeQualifiedNameTailRejects.disjointDotted
    {input rejected : Remainder}
    (rejection : TypeQualifiedNameTailRejects input rejected) :
    ¬ ∃ components finish,
      DottedIdentifierTailParses input.tokens input.endIndex input.cursor
        components finish := by
  induction rejection with
  | componentRejected dotSpan dotParsed componentRejected =>
      rintro ⟨components, finish, successful⟩
      cases successful with
      | done cursor dotAbsent =>
          exact typeTokenAbsent_conflicts_token dotAbsent dotParsed.1
      | next _ successfulDot componentToken tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          cases componentRejected with
          | absent identifierAbsent =>
              exact identifierAbsent ⟨_, _, componentToken⟩
  | @laterRejected rejectionInput afterDot afterComponent rejected component
        dotSpan dotParsed componentParsed laterRejected inductionHypothesis =>
      rintro ⟨components, finish, successful⟩
      cases successful with
      | done cursor dotAbsent =>
          exact typeTokenAbsent_conflicts_token dotAbsent dotParsed.1
      | @next _ _ component components _ successfulDot componentToken tail =>
          have afterDotEq := dotParsed.2
          subst afterDotEq
          have successfulComponent : IdentifierParses
              { rejectionInput with
                cursor := rejectionInput.cursor + 1 } component
              { rejectionInput with
                cursor := rejectionInput.cursor + 2 } := by
            refine ⟨componentToken, rfl, rfl, ?_⟩
            simp
          have outputEq := IdentifierParses.output_unique componentParsed
            successfulComponent
          subst outputEq
          exact inductionHypothesis ⟨_, _, tail⟩

/-- Exact qualified-name rejection excludes qualified-name success. -/
theorem TypeQualifiedNameRejects.disjointQualified
    {input rejected : Remainder}
    (rejection : TypeQualifiedNameRejects input rejected) :
    ¬ ∃ name output, QualifiedNameParses input name output := by
  rintro ⟨name, output, successful⟩
  rcases successful with
    ⟨tokensEq, endIndexEq, firstToken, successfulTail, spanEq⟩
  cases rejection with
  | firstRejected firstRejected =>
      cases firstRejected with
      | absent identifierAbsent =>
          exact identifierAbsent ⟨_, _, firstToken⟩
  | tailRejected firstParsed tailRejected =>
      have successfulFirst : IdentifierParses input
          name.value.components.head { input with cursor := input.cursor + 1 } :=
        ⟨firstToken, rfl, rfl, rfl⟩
      have outputEq := IdentifierParses.output_unique firstParsed
        successfulFirst
      subst outputEq
      exact tailRejected.disjointDotted ⟨_, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeBranchOutcomeProperties
/-! Local disjointness of selected Core-type rejection branches. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every selected function rejection retains its dispatch token. -/
theorem FunctionTypeRejects.keyword_token
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : FunctionTypeRejects nestedRejects input rejected) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .keyword .functionKw
    } := by
  cases rejection with
  | parametersRejected span parsed _ => exact ⟨span, parsed.1⟩
  | returnsRejected span parsed _ _ => exact ⟨span, parsed.1⟩

/-- Every selected comptime rejection retains its two-token guard. -/
theorem ComptimeTypeRejects.prefix_tokens
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ComptimeTypeRejects nestedRejects input rejected) :
    ∃ markerSpan openingSpan,
      TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .identifier ContextualKeyword.comptime.spelling
      } ∧ TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := openingSpan
        value := .symbol .less
      } := by
  cases rejection <;> exact contextualPair_present_of_exact
    (by assumption) (by assumption)

/-- Every selected mapping rejection retains its two-token guard. -/
theorem MappingTypeRejects.prefix_tokens
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : MappingTypeRejects nestedRejects input rejected) :
    ∃ markerSpan openingSpan,
      TokenAt input.tokens input.endIndex input.cursor {
        span := markerSpan
        value := .identifier ContextualKeyword.mapping.spelling
      } ∧ TokenAt input.tokens input.endIndex (input.cursor + 1) {
        span := openingSpan
        value := .symbol .leftParen
      } := by
  cases rejection <;> exact contextualPair_present_of_exact
    (by assumption) (by assumption)

/-- A selected `returns` rejection excludes its optional suffix success. -/
theorem FunctionTypeReturnsRejects.disjointOptional
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected output : Remainder}
    {returns : Option (DelimitedList Syntax.TypeExpr)}
    (rejection : FunctionTypeReturnsRejects nestedRejects input rejected)
    (successful : OptionalFunctionTypeReturnsParses input returns output) :
    False := by
  cases rejection with
  | valuesRejected markerSpan markerParsed valuesRejected =>
      cases successful with
      | absent markerAbsent =>
          exact typeTokenAbsent_conflicts_token markerAbsent markerParsed.1
      | present _ successfulMarker successfulValues =>
          have afterMarkerEq := typeExactToken_output_unique markerParsed
            successfulMarker
          subst afterMarkerEq
          exact valuesRejected.disjointTypeList outcomes
            ⟨_, _, successfulValues⟩

/-- A selected function-type rejection excludes a function-type success. -/
theorem FunctionTypeRejects.disjointFunction
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected afterKeyword afterParameters output : Remainder}
    {parameters : DelimitedList Syntax.TypeExpr}
    {returns : Option (DelimitedList Syntax.TypeExpr)}
    {keywordSpan : SourceSpan}
    (rejection : FunctionTypeRejects nestedRejects input rejected)
    (keywordParsed : ExactTokenParses (.keyword .functionKw) input
      keywordSpan afterKeyword)
    (parametersParsed : TypeExprTrailingDelimitedListParses .leftParen
      .rightParen afterKeyword parameters afterParameters)
    (returnsParsed : OptionalFunctionTypeReturnsParses afterParameters
      returns output) : False := by
  cases rejection with
  | parametersRejected _ rejectedKeyword parametersRejected =>
      have afterKeywordEq := typeExactToken_output_unique rejectedKeyword
        keywordParsed
      subst afterKeywordEq
      exact parametersRejected.disjointTypeList outcomes
        ⟨_, _, parametersParsed⟩
  | returnsRejected _ rejectedKeyword rejectedParameters returnsRejected =>
      have afterKeywordEq := typeExactToken_output_unique rejectedKeyword
        keywordParsed
      subst afterKeywordEq
      have afterParametersEq := rejectedParameters.output_uniqueTypeList
        parametersParsed
      subst afterParametersEq
      exact returnsRejected.disjointOptional outcomes returnsParsed

/-- A selected comptime-type rejection excludes comptime-type success. -/
theorem ComptimeTypeRejects.disjointComptime
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected afterMarker afterOpening afterInner output : Remainder}
    {inner : Syntax.TypeExpr} {markerSpan openingSpan closingSpan : SourceSpan}
    (rejection : ComptimeTypeRejects nestedRejects input rejected)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.comptime.spelling) input markerSpan
      afterMarker)
    (openingParsed : ExactTokenParses (.symbol .less) afterMarker openingSpan
      afterOpening)
    (innerParsed : TypeExprParses afterOpening inner afterInner)
    (closingParsed : ExactTokenParses (.symbol .greater) afterInner
      closingSpan output) : False := by
  cases rejection with
  | innerRejected _ _ rejectedMarker rejectedOpening innerRejected =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      exact outcomes.successRejectDisjoint innerRejected ⟨_, _, innerParsed⟩
  | closingMissing _ _ rejectedMarker rejectedOpening rejectedInner
        closingAbsent =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      have afterInnerEq := TypeExprParses.output_unique rejectedInner
        innerParsed
      subst afterInnerEq
      exact typeTokenAbsent_conflicts_token closingAbsent closingParsed.1

/-- A selected mapping-type rejection excludes mapping-type success. -/
theorem MappingTypeRejects.disjointMapping
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected afterMarker afterOpening afterKey afterArrow afterValue
      output : Remainder} {key value : Syntax.TypeExpr}
    {markerSpan openingSpan arrowSpan closingSpan : SourceSpan}
    (rejection : MappingTypeRejects nestedRejects input rejected)
    (markerParsed : ExactTokenParses
      (.identifier ContextualKeyword.mapping.spelling) input markerSpan
      afterMarker)
    (openingParsed : ExactTokenParses (.symbol .leftParen) afterMarker
      openingSpan afterOpening)
    (keyParsed : TypeExprParses afterOpening key afterKey)
    (arrowParsed : ExactTokenParses (.symbol .fatArrow) afterKey arrowSpan
      afterArrow)
    (valueParsed : TypeExprParses afterArrow value afterValue)
    (closingParsed : ExactTokenParses (.symbol .rightParen) afterValue
      closingSpan output) : False := by
  cases rejection with
  | keyRejected _ _ rejectedMarker rejectedOpening keyRejected =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      exact outcomes.successRejectDisjoint keyRejected ⟨_, _, keyParsed⟩
  | arrowMissing _ _ rejectedMarker rejectedOpening rejectedKey arrowAbsent =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      have afterKeyEq := TypeExprParses.output_unique rejectedKey keyParsed
      subst afterKeyEq
      exact typeTokenAbsent_conflicts_token arrowAbsent arrowParsed.1
  | valueRejected _ _ _ rejectedMarker rejectedOpening rejectedKey
        rejectedArrow valueRejected =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      have afterKeyEq := TypeExprParses.output_unique rejectedKey keyParsed
      subst afterKeyEq
      have afterArrowEq := typeExactToken_output_unique rejectedArrow
        arrowParsed
      subst afterArrowEq
      exact outcomes.successRejectDisjoint valueRejected ⟨_, _, valueParsed⟩
  | closingMissing _ _ _ rejectedMarker rejectedOpening rejectedKey
        rejectedArrow rejectedValue closingAbsent =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      have afterOpeningEq := typeExactToken_output_unique rejectedOpening
        openingParsed
      subst afterOpeningEq
      have afterKeyEq := TypeExprParses.output_unique rejectedKey keyParsed
      subst afterKeyEq
      have afterArrowEq := typeExactToken_output_unique rejectedArrow
        arrowParsed
      subst afterArrowEq
      have afterValueEq := TypeExprParses.output_unique rejectedValue
        valueParsed
      subst afterValueEq
      exact typeTokenAbsent_conflicts_token closingAbsent closingParsed.1

/-- A selected proxy-type rejection excludes proxy-type success. -/
theorem ProxyTypeRejects.disjointProxy
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected afterMarker output : Remainder} {inner : Syntax.TypeExpr}
    {markerSpan : SourceSpan}
    (rejection : ProxyTypeRejects nestedRejects input rejected)
    (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
      afterMarker)
    (innerParsed : TypeExprParses afterMarker inner output) : False := by
  cases rejection with
  | innerRejected _ rejectedMarker innerRejected =>
      have afterMarkerEq := typeExactToken_output_unique rejectedMarker
        markerParsed
      subst afterMarkerEq
      exact outcomes.successRejectDisjoint innerRejected ⟨_, _, innerParsed⟩

/-- A selected tuple-type rejection excludes tuple-type success. -/
theorem TupleTypeRejects.disjointTuple
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected output : Remainder}
    {values : DelimitedList Syntax.TypeExpr}
    (rejection : TupleTypeRejects nestedRejects input rejected)
    (successful : TypeExprTrailingDelimitedListParses .leftParen .rightParen
      input values output) : False := by
  cases rejection with
  | selected _ _ valuesRejected =>
      exact valuesRejected.disjointTypeList outcomes ⟨_, _, successful⟩

/-- A selected named-argument rejection excludes either optional outcome. -/
theorem NamedTypeArgumentsRejects.disjointOptional
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected output : Remainder}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    (rejection : NamedTypeArgumentsRejects nestedRejects input rejected)
    (successful : OptionalNamedTypeArgumentsParses input arguments output) :
    False := by
  cases rejection with
  | selected _ openingParsed valuesRejected =>
      cases successful with
      | absent openingAbsent =>
          exact typeTokenAbsent_conflicts_token openingAbsent openingParsed.1
      | present openingSpan closingSpan openingToken progress tokensEq
            endIndexEq elementsEq spanEq firstParsed tail =>
          exact valuesRejected.disjointNamedTypeArguments outcomes
            ⟨_, _, .present openingSpan closingSpan openingToken progress
              tokensEq endIndexEq elementsEq spanEq firstParsed tail⟩

/-- A selected named-type rejection excludes named-type success. -/
theorem NamedTypeRejects.disjointNamed
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected afterName output : Remainder}
    {name : Syntax.QualifiedName}
    {arguments : Option (NonemptyDelimitedList Syntax.TypeExpr)}
    (rejection : NamedTypeRejects nestedRejects input rejected)
    (nameParsed : QualifiedNameParses input name afterName)
    (argumentsParsed : OptionalNamedTypeArgumentsParses afterName arguments
      output) : False := by
  cases rejection with
  | nameRejected nameRejected =>
      exact nameRejected.disjointQualified ⟨_, _, nameParsed⟩
  | argumentsRejected rejectedName argumentsRejected =>
      have afterNameEq := rejectedName.output_unique nameParsed
      subst afterNameEq
      exact argumentsRejected.disjointOptional outcomes argumentsParsed

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
/-! Deterministic parser-independent ordinary outcomes for Core types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One prioritized successor-fuel rejection layer excludes ordinary success. -/
theorem TypeExprCoreRejects.disjointOrdinary
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec TypeExprParses nestedRejects)
    {input rejected : Remainder}
    (rejection : TypeExprCoreRejects nestedRejects input rejected) :
    ¬ ∃ value output, TypeExprParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | function branchRejected =>
      rcases branchRejected.keyword_token with ⟨span, rejectedKeyword⟩
      cases successful with
      | function _ successfulKeyword _ successfulParameters
            successfulReturns =>
          exact branchRejected.disjointFunction outcomes successfulKeyword
            successfulParameters successfulReturns
      | comptime _ _ _ successfulMarker _ _ _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | mapping _ _ _ _ successfulMarker _ _ _ _ _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedKeyword openingToken
      | named _ _ successfulName _ _ =>
          cases typeTokenAt_kind_eq rejectedKeyword successfulName.2.2.1
  | comptime functionAbsent branchRejected =>
      rcases branchRejected.prefix_tokens with
        ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening
            successfulClosing _ successfulInner =>
          exact branchRejected.disjointComptime outcomes successfulMarker
            successfulOpening successfulInner successfulClosing
      | mapping _ _ _ _ successfulMarker _ _ _ _ _ _ =>
          have impossible := typeTokenAt_kind_eq rejectedMarker
            successfulMarker.1
          simp [ContextualKeyword.spelling] at impossible
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedMarker successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedMarker openingToken
      | named comptimeAbsent _ _ _ _ =>
          exact comptimeAbsent
            ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
  | mapping functionAbsent comptimeAbsent branchRejected =>
      rcases branchRejected.prefix_tokens with
        ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening successfulArrow
            successfulClosing _ successfulKey successfulValue =>
          exact branchRejected.disjointMapping outcomes successfulMarker
            successfulOpening successfulKey successfulArrow successfulValue
            successfulClosing
      | proxy _ successfulMarker _ _ =>
          cases typeTokenAt_kind_eq rejectedMarker successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          cases typeTokenAt_kind_eq rejectedMarker openingToken
      | named _ mappingAbsent _ _ _ =>
          exact mappingAbsent
            ⟨markerSpan, openingSpan, rejectedMarker, rejectedOpening⟩
  | proxy functionAbsent comptimeAbsent mappingAbsent branchRejected =>
      cases branchRejected with
      | innerRejected markerSpan rejectedMarker innerRejected =>
          cases successful with
          | function _ successfulKeyword _ _ _ =>
              exact typeTokenAbsent_conflicts_token functionAbsent
                successfulKeyword.1
          | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
              exact comptimeAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
              exact mappingAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | proxy _ successfulMarker _ successfulInner =>
              have afterMarkerEq := typeExactToken_output_unique
                rejectedMarker successfulMarker
              subst afterMarkerEq
              exact outcomes.successRejectDisjoint innerRejected
                ⟨_, _, successfulInner⟩
          | tuple _ successfulValues =>
              rcases successfulValues.opening_token with
                ⟨_, openingToken⟩
              cases typeTokenAt_kind_eq rejectedMarker.1 openingToken
          | named _ _ successfulName _ _ =>
              cases typeTokenAt_kind_eq rejectedMarker.1
                successfulName.2.2.1
  | tuple functionAbsent comptimeAbsent mappingAbsent atAbsent
        branchRejected =>
      cases branchRejected with
      | selected openingSpan openingParsed valuesRejected =>
          cases successful with
          | function _ successfulKeyword _ _ _ =>
              exact typeTokenAbsent_conflicts_token functionAbsent
                successfulKeyword.1
          | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
              exact comptimeAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
              exact mappingAbsent (contextualPair_present_of_exact
                successfulMarker successfulOpening)
          | proxy _ successfulMarker _ _ =>
              exact typeTokenAbsent_conflicts_token atAbsent
                successfulMarker.1
          | tuple _ successfulValues =>
              exact valuesRejected.disjointTypeList outcomes
                ⟨_, _, successfulValues⟩
          | named _ _ successfulName _ _ =>
              cases typeTokenAt_kind_eq openingParsed.1
                successfulName.2.2.1
  | named functionAbsent comptimeAbsent mappingAbsent atAbsent
        leftParenAbsent identifierPresent branchRejected =>
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
          exact mappingAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | proxy _ successfulMarker _ _ =>
          exact typeTokenAbsent_conflicts_token atAbsent successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          exact typeTokenAbsent_conflicts_token leftParenAbsent openingToken
      | named _ _ successfulName _ successfulArguments =>
          exact branchRejected.disjointNamed outcomes successfulName
            successfulArguments
  | final functionAbsent comptimeAbsent mappingAbsent atAbsent
        leftParenAbsent identifierAbsent =>
      cases successful with
      | function _ successfulKeyword _ _ _ =>
          exact typeTokenAbsent_conflicts_token functionAbsent
            successfulKeyword.1
      | comptime _ _ _ successfulMarker successfulOpening _ _ _ =>
          exact comptimeAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | mapping _ _ _ _ successfulMarker successfulOpening _ _ _ _ _ =>
          exact mappingAbsent (contextualPair_present_of_exact
            successfulMarker successfulOpening)
      | proxy _ successfulMarker _ _ =>
          exact typeTokenAbsent_conflicts_token atAbsent successfulMarker.1
      | tuple _ successfulValues =>
          rcases successfulValues.opening_token with ⟨_, openingToken⟩
          exact typeTokenAbsent_conflicts_token leftParenAbsent openingToken
      | named _ _ successfulName _ _ =>
          exact identifierAbsent ⟨_, _, successfulName.2.2.1⟩

/-- Every executable fuel layer has deterministic, exclusive outcomes. -/
theorem typeExprDeterministicOutcomeSpecWithFuel :
    ∀ fuel, DeterministicOutcomeSpec TypeExprOrdinaryParses
      (TypeExprRejectsWithFuel fuel)
  | 0 => {
      successOutputUnique := TypeExprParses.output_unique
      successRejectDisjoint := by simp [TypeExprRejectsWithFuel]
    }
  | fuel + 1 => {
      successOutputUnique := TypeExprParses.output_unique
      successRejectDisjoint := by
        intro input rejected rejection
        exact rejection.disjointOrdinary
          (typeExprDeterministicOutcomeSpecWithFuel fuel)
    }

/-- The public Core type grammar has deterministic ordinary success and exact
rejection outcomes. -/
theorem typeExprDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeExprOrdinaryParses TypeExprRejects where
  successOutputUnique := TypeExprParses.output_unique
  successRejectDisjoint := by
    intro input rejected rejection
    exact (typeExprDeterministicOutcomeSpecWithFuel
      (typeExprPublicFuel input)).successRejectDisjoint rejection

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties
/-! Exact qualified-name outcomes used by recursive Core named types. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One maximal dotted identifier tail has one exact component list. -/
theorem DottedIdentifierTailParses.value_unique :
    ∀ {tokens : Array Token} {endIndex cursor : Nat}
      {left right : List Syntax.Identifier} {leftFinish rightFinish : Nat},
      DottedIdentifierTailParses tokens endIndex cursor left leftFinish →
      DottedIdentifierTailParses tokens endIndex cursor right rightFinish →
      left = right := by
  intro tokens endIndex cursor left right leftFinish rightFinish leftParsed
  induction leftParsed generalizing right rightFinish with
  | done cursor leftDotAbsent =>
      intro rightParsed
      cases rightParsed with
      | done => rfl
      | next rightDotSpan rightDot rightComponent rightTail =>
          exact False.elim (leftDotAbsent ⟨rightDotSpan, rightDot⟩)
  | @next cursor leftFinish leftComponent leftComponents leftDotSpan leftDot
      leftComponentToken leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | done cursor rightDotAbsent =>
          exact False.elim (rightDotAbsent ⟨leftDotSpan, leftDot⟩)
      | @next _ rightFinish rightComponent rightComponents rightDotSpan
          rightDot rightComponentToken rightTail =>
          have componentTokenEq :=
            leftComponentToken.token_unique rightComponentToken
          have componentEq : leftComponent = rightComponent := by
            cases leftComponent
            cases rightComponent
            simp_all
          have tailEq := inductionHypothesis rightTail
          subst componentEq
          subst tailEq
          rfl

/-- One qualified-name success has one exact located component sequence. -/
theorem QualifiedNameParses.value_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    left = right := by
  rcases leftParsed with
    ⟨leftTokensEq, leftEndIndexEq, leftFirst, leftTail, leftSpanEq⟩
  rcases rightParsed with
    ⟨rightTokensEq, rightEndIndexEq, rightFirst, rightTail, rightSpanEq⟩
  have firstTokenEq := leftFirst.token_unique rightFirst
  have tailEq := leftTail.value_unique rightTail
  cases left with
  | mk leftSpan leftValue =>
      cases leftValue with
      | mk leftComponents =>
          cases leftComponents with
          | mk leftHead leftRest =>
              cases right with
              | mk rightSpan rightValue =>
                  cases rightValue with
                  | mk rightComponents =>
                      cases rightComponents with
                      | mk rightHead rightRest =>
                          cases leftHead
                          cases rightHead
                          simp_all

/-- One qualified-name success fixes its value and final remainder. -/
theorem QualifiedNameParses.result_unique
    {input : Remainder} {left right : Syntax.QualifiedName}
    {afterLeft afterRight : Remainder}
    (leftParsed : QualifiedNameParses input left afterLeft)
    (rightParsed : QualifiedNameParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A dotted qualified-name tail rejection has one failing endpoint. -/
theorem TypeQualifiedNameTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeQualifiedNameTailRejects input left)
    (rightRejected : TypeQualifiedNameTailRejects input right) :
    left = right := by
  induction leftRejected generalizing right with
  | componentRejected leftDotSpan leftDot leftComponent =>
      cases rightRejected with
      | componentRejected rightDotSpan rightDot rightComponent =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact leftComponent.output_unique rightComponent
      | laterRejected rightDotSpan rightDot rightComponent rightTail =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint leftComponent
              ⟨_, _, rightComponent⟩)
  | laterRejected leftDotSpan leftDot leftComponent leftTail
        inductionHypothesis =>
      cases rightRejected with
      | componentRejected rightDotSpan rightDot rightComponent =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint rightComponent
              ⟨_, _, leftComponent⟩)
      | laterRejected rightDotSpan rightDot rightComponent rightTail =>
          have afterDotEq := leftDot.output_unique rightDot
          subst afterDotEq
          rcases leftComponent.result_unique rightComponent with
            ⟨componentEq, afterComponentEq⟩
          subst componentEq
          subst afterComponentEq
          exact inductionHypothesis rightTail

/-- A complete qualified-name rejection has one failing endpoint. -/
theorem TypeQualifiedNameRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeQualifiedNameRejects input left)
    (rightRejected : TypeQualifiedNameRejects input right) :
    left = right := by
  cases leftRejected with
  | firstRejected leftFirst =>
      cases rightRejected with
      | firstRejected rightFirst => exact leftFirst.output_unique rightFirst
      | tailRejected rightFirst rightTail =>
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint leftFirst
              ⟨_, _, rightFirst⟩)
  | tailRejected leftFirst leftTail =>
      cases rightRejected with
      | firstRejected rightFirst =>
          exact False.elim
            (identifierExactOutcomeSpec.successRejectDisjoint rightFirst
              ⟨_, _, leftFirst⟩)
      | tailRejected rightFirst rightTail =>
          rcases leftFirst.result_unique rightFirst with
            ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Qualified names have fully functional success and rejection outcomes. -/
theorem typeQualifiedNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec QualifiedNameParses
      TypeQualifiedNameRejects where
  toDeterministicOutcomeSpec := {
    successOutputUnique := QualifiedNameParses.output_unique
    successRejectDisjoint := TypeQualifiedNameRejects.disjointQualified
  }
  successValueUnique := QualifiedNameParses.value_unique
  rejectOutputUnique := TypeQualifiedNameRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end
