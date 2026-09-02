import Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeDelimitedRejectionExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties

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
