import Solcore.Syntax.DeclarativeCoreTypeNameOutcomeProperties

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
