import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Deterministic ordinary outcomes for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- The priority-ordered recovery tail has one final remainder. -/
theorem DeriveAttributeRecoveryTailParses.output_unique :
    ∀ {hash leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.DeriveAttribute}
      {afterLeft afterRight : Remainder},
      DeriveAttributeRecoveryTailParses hash leftLast input left afterLeft →
      DeriveAttributeRecoveryTailParses hash rightLast input right afterRight →
      afterLeft = afterRight := by
  intro hash leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | malformed leftClosingSpan leftClosing =>
      intro rightParsed
      cases rightParsed with
      | malformed rightClosingSpan rightClosing =>
          rw [leftClosing.2, rightClosing.2]
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
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- The complete recovered path has one final remainder. -/
theorem DeriveAttributeRecoveredParses.output_unique
    {input : Remainder} {left right : Syntax.DeriveAttribute}
    {afterLeft afterRight : Remainder}
    (leftParsed : DeriveAttributeRecoveredParses input left afterLeft)
    (rightParsed : DeriveAttributeRecoveredParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftHashSpan leftOpeningSpan leftHash leftOpening leftTail =>
      cases rightParsed with
      | recovered rightHashSpan rightOpeningSpan rightHash rightOpening
          rightTail =>
          have hashTokenEq := tokenAt_unique leftHash.1 rightHash.1
          have hashSpanEq : leftHashSpan = rightHashSpan :=
            congrArg (fun token : Token => token.span) hashTokenEq
          have afterHashEq := leftHash.2.trans rightHash.2.symm
          subst rightHashSpan
          subst afterHashEq
          have openingTokenEq := tokenAt_unique leftOpening.1 rightOpening.1
          have openingSpanEq : leftOpeningSpan = rightOpeningSpan :=
            congrArg (fun token : Token => token.span) openingTokenEq
          have afterOpeningEq := leftOpening.2.trans rightOpening.2.symm
          subst rightOpeningSpan
          subst afterOpeningEq
          exact leftTail.output_unique rightTail

/-- A recovered-prefix rejection excludes every recovered success. -/
theorem DeriveAttributeRecoveredRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : DeriveAttributeRecoveredRejects input rejected) :
    ¬ ∃ value output, DeriveAttributeRecoveredParses input value output := by
  rintro ⟨value, output, successful⟩
  cases successful with
  | recovered successfulHashSpan successfulOpeningSpan successfulHash
      successfulOpening successfulTail =>
      cases rejection with
      | hashMissing hashAbsent =>
          exact absent_conflicts_token hashAbsent successfulHash.1
      | openingMissing rejectedHashSpan rejectedHash openingAbsent =>
          have afterHashEq := rejectedHash.2.trans successfulHash.2.symm
          subst afterHashEq
          exact absent_conflicts_token openingAbsent successfulOpening.1

/-- Recovered derive attributes form a deterministic ordinary outcome. -/
theorem deriveAttributeRecoveredDeterministicOutcomeSpec :
    DeterministicOutcomeSpec DeriveAttributeRecoveredParses
      DeriveAttributeRecoveredRejects where
  successOutputUnique := DeriveAttributeRecoveredParses.output_unique
  successRejectDisjoint := DeriveAttributeRecoveredRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
