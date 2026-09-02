import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Full functionality of recovered derive-attribute outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- For one fixed last retained span, the priority-ordered recovery tail has
one exact recovered AST value. -/
theorem DeriveAttributeRecoveryTailParses.value_unique :
    ∀ {hash last : SourceSpan} {input : Remainder}
      {left right : Syntax.DeriveAttribute}
      {afterLeft afterRight : Remainder},
      DeriveAttributeRecoveryTailParses hash last input left afterLeft →
      DeriveAttributeRecoveryTailParses hash last input right afterRight →
      left = right := by
  intro hash last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | malformed leftClosingSpan leftClosing =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          have closingSpanEq := leftClosing.span_unique rightClosing
          cases closingSpanEq
          rfl
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim
            (absent_conflicts_token rightClosingAbsent leftClosing.1)
  | unclosed leftClosingAbsent leftStops =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed => rfl
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftClosingAbsent leftContinues leftCurrent leftTail
      inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          exact False.elim
            (absent_conflicts_token leftClosingAbsent rightClosing.1)
      | unclosed rightClosingAbsent rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightClosingAbsent rightContinues rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery tail with one fixed retained span fixes its AST and final
remainder. -/
theorem DeriveAttributeRecoveryTailParses.result_unique
    {hash last : SourceSpan} {input : Remainder}
    {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveryTailParses hash last input left
      afterLeft)
    (rightParsed : DeriveAttributeRecoveryTailParses hash last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The complete recovered path has one exact AST value. -/
theorem DeriveAttributeRecoveredParses.value_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftHashSpan leftOpeningSpan leftHash leftOpening leftTail =>
      cases rightParsed with
      | recovered rightHashSpan rightOpeningSpan rightHash rightOpening
          rightTail =>
          rcases leftHash.result_unique rightHash with
            ⟨hashSpanEq, afterHashEq⟩
          cases hashSpanEq
          cases afterHashEq
          rcases leftOpening.result_unique rightOpening with
            ⟨openingSpanEq, afterOpeningEq⟩
          cases openingSpanEq
          cases afterOpeningEq
          exact leftTail.value_unique rightTail

/-- The complete recovered path fixes its AST and final remainder. -/
theorem DeriveAttributeRecoveredParses.result_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- A recovered-prefix rejection has one exact failing endpoint. -/
theorem DeriveAttributeRecoveredRejects.output_unique
    {input left right : Remainder}
    (leftRejects : DeriveAttributeRecoveredRejects input left)
    (rightRejects : DeriveAttributeRecoveredRejects input right) :
    left = right := by
  cases leftRejects with
  | hashMissing leftHashAbsent =>
      cases rightRejects with
      | hashMissing => rfl
      | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHash.1)
  | openingMissing leftHashSpan leftHash leftOpeningAbsent =>
      cases rightRejects with
      | hashMissing rightHashAbsent =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHash.1)
      | openingMissing rightHashSpan rightHash rightOpeningAbsent =>
          exact leftHash.output_unique rightHash

/-- Recovered derive attributes have fully functional ordinary and rejection
outcomes. -/
theorem deriveAttributeRecoveredExactOutcomeSpec :
    ExactDeterministicOutcomeSpec DeriveAttributeRecoveredParses
      DeriveAttributeRecoveredRejects where
  toDeterministicOutcomeSpec :=
    deriveAttributeRecoveredDeterministicOutcomeSpec
  successValueUnique := DeriveAttributeRecoveredParses.value_unique
  rejectOutputUnique := DeriveAttributeRecoveredRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
