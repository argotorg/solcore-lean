import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingExactnessProperties
import Solcore.Syntax.DeclarativeEnumConstructorOutcomeProperties

/-! Exact values and rejection endpoints for enum constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem enumConstructor_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem enumConstructorFields_opening_present
    {input output : Remainder} {fields : DelimitedList Syntax.TypeExpr}
    (parsed : NoTrailingDelimitedListParses .leftParen .rightParen
      TypeExprParses input fields output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor {
      span, value := .symbol .leftParen } := by
  cases parsed with
  | empty openingSpan closingSpan openingToken closingToken =>
      exact ⟨openingSpan, openingToken⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
        elementsEq, spanEq⟩
      exact ⟨openingSpan, openingToken⟩

/-- Constructor payload lists have exact Core type values and rejection
endpoints. -/
theorem enumConstructorFieldListExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (NoTrailingDelimitedListParses .leftParen .rightParen
        TypeExprOrdinaryParses)
      (DelimitedListRejects .leftParen .rightParen true false
        TypeExprOrdinaryParses TypeExprRejects) :=
  noTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    typeExprExactOutcomeSpec

/-- Optional constructor payloads fix their absent or present AST value. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.value_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightFields =>
          rcases enumConstructorFields_opening_present rightFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (enumConstructor_absent_conflicts_token leftAbsent openingPresent)
  | present leftFields =>
      cases rightParsed with
      | absent rightAbsent =>
          rcases enumConstructorFields_opening_present leftFields with
            ⟨span, openingPresent⟩
          exact False.elim
            (enumConstructor_absent_conflicts_token rightAbsent openingPresent)
      | present rightFields =>
          rw [enumConstructorFieldListExactOutcomeSpec.successValueUnique
            leftFields rightFields]

/-- Optional constructor payloads fix both their value and remainder. -/
theorem OptionalEnumConstructorFieldsOrdinaryParses.result_unique
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.TypeExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalEnumConstructorFieldsOrdinaryParses input left
      afterLeft)
    (rightParsed : OptionalEnumConstructorFieldsOrdinaryParses input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A committed optional constructor-payload rejection has one endpoint. -/
theorem OptionalEnumConstructorFieldsRejects.output_unique
    {input left right : Remainder}
    (leftRejected : OptionalEnumConstructorFieldsRejects input left)
    (rightRejected : OptionalEnumConstructorFieldsRejects input right) :
    left = right := by
  cases leftRejected with
  | present _ leftFields =>
      cases rightRejected with
      | present _ rightFields =>
          exact enumConstructorFieldListExactOutcomeSpec.rejectOutputUnique
            leftFields rightFields

/-- Optional enum-constructor payloads have fully exact outcomes. -/
theorem optionalEnumConstructorFieldsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      OptionalEnumConstructorFieldsOrdinaryParses
      OptionalEnumConstructorFieldsRejects where
  toDeterministicOutcomeSpec :=
    optionalEnumConstructorFieldsDeterministicOutcomeSpec
  successValueUnique :=
    OptionalEnumConstructorFieldsOrdinaryParses.value_unique
  rejectOutputUnique := OptionalEnumConstructorFieldsRejects.output_unique

/-- A successful enum constructor fixes its complete AST. -/
theorem EnumConstructorOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftName leftFields =>
      cases rightParsed with
      | parsed rightName rightFields =>
          rcases identifierExactOutcomeSpec.successResultUnique leftName
              rightName with ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases optionalEnumConstructorFieldsExactOutcomeSpec
              |>.successResultUnique leftFields rightFields with
            ⟨fieldsEq, afterFieldsEq⟩
          subst fieldsEq
          rfl

/-- A successful enum constructor fixes its AST and final remainder. -/
theorem EnumConstructorOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.EnumConstructor}
    {afterLeft afterRight : Remainder}
    (leftParsed : EnumConstructorOrdinaryParses input left afterLeft)
    (rightParsed : EnumConstructorOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Enum-constructor rejection fixes its first failing endpoint. -/
theorem EnumConstructorRejects.output_unique
    {input left right : Remainder}
    (leftRejected : EnumConstructorRejects input left)
    (rightRejected : EnumConstructorRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      optionalEnumConstructorFieldsExactOutcomeSpec.rejectOutputUnique]

/-- Enum constructors have fully exact ordinary outcomes. -/
theorem enumConstructorExactOutcomeSpec :
    ExactDeterministicOutcomeSpec EnumConstructorOrdinaryParses
      EnumConstructorRejects where
  toDeterministicOutcomeSpec := enumConstructorDeterministicOutcomeSpec
  successValueUnique := EnumConstructorOrdinaryParses.value_unique
  rejectOutputUnique := EnumConstructorRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
