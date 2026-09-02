import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeTypeAliasOutcomeGrammar

/-! Deterministic ordinary outcomes for recovery-aware type-alias values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- Every pre-recovery boundary is also a stop of the recovery scan. -/
theorem TypeAliasValueBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : TypeAliasValueBoundaryStops input) :
    TypeAliasValueRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token

/-- The recursive malformed-value scan has one final remainder. -/
theorem TypeAliasValueRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder},
      TypeAliasValueRecoveryScanParses first leftLast input left afterLeft →
      TypeAliasValueRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing rightLast right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- Complete malformed-value recovery has one final remainder. -/
theorem TypeAliasValueRecoveryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | recovered leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every recovery rejection retains its complete input remainder. -/
theorem TypeAliasValueRecoveryRejects.output_eq
    {input rejected : Remainder}
    (rejection : TypeAliasValueRecoveryRejects input rejected) :
    rejected = input := by
  cases rejection <;> rfl

/-- An unavailable recovery first token excludes every recovery success. -/
theorem TypeAliasValueRecoveryRejects.disjointParses
    {input rejected : Remainder}
    (rejection : TypeAliasValueRecoveryRejects input rejected) :
    ¬ ∃ value output, TypeAliasValueRecoveryParses input value output := by
  rintro ⟨value, output, parsed⟩
  cases parsed with
  | recovered continues current scan =>
      cases rejection with
      | boundary stops => exact continues stops
      | missingToken inside missing =>
          rw [current.2] at missing
          contradiction

/-- Standalone malformed-value recovery has deterministic ordinary outcomes. -/
theorem typeAliasValueRecoveryDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasValueRecoveryParses
      TypeAliasValueRecoveryRejects where
  successOutputUnique := TypeAliasValueRecoveryParses.output_unique
  successRejectDisjoint := TypeAliasValueRecoveryRejects.disjointParses

/-- Preserved carrier and window evidence makes cursor-only rewind exact. -/
theorem TypeAliasValueCoreRejectsWithPreservedWindow.exists_rewind_eq
    {input : Remainder}
    (rejected : TypeAliasValueCoreRejectsWithPreservedWindow input) :
    ∃ failed, TypeExprRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- A preserved Core rejection excludes strict Core type success. -/
theorem TypeAliasValueCoreRejectsWithPreservedWindow.disjointOrdinary
    {input : Remainder}
    (rejected : TypeAliasValueCoreRejectsWithPreservedWindow input) :
    ¬ ∃ value output, TypeExprOrdinaryParses input value output := by
  rintro ⟨value, output, parsed⟩
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  exact typeExprDeterministicOutcomeSpec.successRejectDisjoint rejection
    ⟨_, _, parsed⟩

/-- Recovery-aware alias-value success has one final remainder. -/
theorem TypeAliasValueOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact typeExprDeterministicOutcomeSpec.successOutputUnique leftCore
            rightCore
      | recovered rightRejected rightRecovery =>
          exact False.elim
            (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightRejected rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact alias-value rejection excludes strict and recovered success. -/
theorem TypeAliasValueRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TypeAliasValueRejects input rejected) :
    ¬ ∃ value output, TypeAliasValueOrdinaryParses input value output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          exact coreRejected.disjointOrdinary ⟨_, _, coreParsed⟩
      | recovered otherRejected recovered =>
          cases recovered with
          | recovered continues current scan => exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          exact coreRejected.disjointOrdinary ⟨_, _, coreParsed⟩
      | recovered otherRejected recovered =>
          exact typeAliasValueRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every alias-value rejection returns the rewound input remainder. -/
theorem TypeAliasValueRejects.output_eq
    {input rejected : Remainder}
    (rejection : TypeAliasValueRejects input rejected) : rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Recovery-aware alias values have deterministic and exclusive outcomes. -/
theorem typeAliasValueDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects where
  successOutputUnique := TypeAliasValueOrdinaryParses.output_unique
  successRejectDisjoint := TypeAliasValueRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
