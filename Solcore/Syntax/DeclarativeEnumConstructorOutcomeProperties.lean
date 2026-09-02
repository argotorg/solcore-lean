import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar

/-! Deterministic exact ordinary outcomes for enum constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem noTrailing_opening_present {alpha : Type}
    {opening closing : Symbol}
    {elementParses : Remainder → alpha → Remainder → Prop}
    {input output : Remainder} {values : DelimitedList alpha}
    (parsed : NoTrailingDelimitedListParses opening closing elementParses input
      values output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol opening } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- The allow-empty, no-trailing constructor-field list inherits the public
Core type outcome. -/
theorem enumConstructorFieldListDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects) :=
  noTrailingDelimitedListDeterministicOutcomeSpec .leftParen .rightParen
    typeExprDeterministicOutcomeSpec

/-- Optional constructor fields have one final remainder. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.output_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightFields =>
          rcases noTrailing_opening_present rightFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token leftAbsent openingPresent)
  | present leftFields =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases noTrailing_opening_present leftFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (absent_conflicts_token rightAbsent openingPresent)
      | present rightFields =>
          exact enumConstructorFieldListDeterministicOutcomeSpec
            |>.successOutputUnique leftFields rightFields

/-- A committed constructor-field rejection excludes absent and present
ordinary success. -/
theorem OptionalEnumConstructorFieldsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : OptionalEnumConstructorFieldsRejects input rejected) :
    ¬ ∃ fields output,
      OptionalEnumConstructorFieldsOrdinaryParses input fields output := by
  rintro ⟨fields, output, successful⟩
  cases rejection with
  | present openingPresent fieldsRejected =>
      cases successful with
      | absent openingAbsent =>
          rcases openingPresent with ⟨span, openingToken⟩
          exact absent_conflicts_token openingAbsent openingToken
      | present fieldsParsed =>
          exact enumConstructorFieldListDeterministicOutcomeSpec
            |>.successRejectDisjoint fieldsRejected ⟨_, _, fieldsParsed⟩

/-- Optional enum-constructor fields have deterministic and exclusive ordinary
outcomes. -/
theorem optionalEnumConstructorFieldsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec OptionalEnumConstructorFieldsOrdinaryParses
      OptionalEnumConstructorFieldsRejects where
  successOutputUnique :=
    OptionalEnumConstructorFieldsOrdinaryParses.output_unique
  successRejectDisjoint :=
    OptionalEnumConstructorFieldsRejects.disjointOrdinary

/-- Ordinary enum-constructor success has one final remainder. -/
theorem EnumConstructorOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftName leftFields =>
      cases rightParsed with
      | parsed rightName rightFields =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          exact OptionalEnumConstructorFieldsOrdinaryParses.output_unique
            leftFields rightFields

/-- Exact enum-constructor rejection excludes every ordinary success. -/
theorem EnumConstructorRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : EnumConstructorRejects input rejected) :
    ¬ ∃ constructor output,
      EnumConstructorOrdinaryParses input constructor output := by
  rintro ⟨constructor, output, successful⟩
  cases rejection with
  | nameRejected nameRejected =>
      cases successful with
      | parsed nameParsed fieldsParsed =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, nameParsed⟩
  | fieldsRejected rejectedName fieldsRejected =>
      cases successful with
      | parsed successfulName successfulFields =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact optionalEnumConstructorFieldsDeterministicOutcomeSpec
            |>.successRejectDisjoint fieldsRejected
              ⟨_, _, successfulFields⟩

/-- Enum constructors have deterministic and exclusive ordinary outcomes. -/
theorem enumConstructorDeterministicOutcomeSpec :
    DeterministicOutcomeSpec EnumConstructorOrdinaryParses
      EnumConstructorRejects where
  successOutputUnique := EnumConstructorOrdinaryParses.output_unique
  successRejectDisjoint := EnumConstructorRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
