import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativeTypeAliasValueOutcomeProperties

/-!
Exact malformed type-alias value recovery and its conditional lift through
the remaining Core type-expression frontier.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exact_tokenAt_unique {tokens : Array Token}
    {endIndex index : Nat} {left right : Token}
    (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- With the same retained first and last spans, a recovery scan constructs
one exact error type value. -/
theorem TypeAliasValueRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder},
      TypeAliasValueRecoveryScanParses first last input left afterLeft →
      TypeAliasValueRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues rightCurrent rightTail =>
          exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops =>
          exact False.elim (leftContinues rightStops)
      | next rightContinues rightCurrent rightTail =>
          have currentEq := exact_tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan fixes both its error type value and final remainder. -/
theorem TypeAliasValueRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.TypeExpr} {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryScanParses first last input left
      afterLeft)
    (rightParsed : TypeAliasValueRecoveryScanParses first last input right
      afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Complete malformed-value recovery constructs one exact error type. -/
theorem TypeAliasValueRecoveryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | recovered leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | recovered rightContinues rightCurrent rightScan =>
          have currentEq := exact_tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- Complete malformed-value recovery fixes its value and remainder. -/
theorem TypeAliasValueRecoveryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueRecoveryParses input left afterLeft)
    (rightParsed : TypeAliasValueRecoveryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Every unavailable-first-token recovery rejection has one endpoint. -/
theorem TypeAliasValueRecoveryRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TypeAliasValueRecoveryRejects input left)
    (rightRejected : TypeAliasValueRecoveryRejects input right) :
    left = right :=
  leftRejected.output_eq.trans rightRejected.output_eq.symm

/-- Standalone malformed-value recovery has fully exact outcomes. -/
theorem typeAliasValueRecoveryExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasValueRecoveryParses
      TypeAliasValueRecoveryRejects where
  toDeterministicOutcomeSpec :=
    typeAliasValueRecoveryDeterministicOutcomeSpec
  successValueUnique := TypeAliasValueRecoveryParses.value_unique
  rejectOutputUnique := TypeAliasValueRecoveryRejects.output_unique

/-- Exact Core type outcomes make recovery-aware alias values exact. -/
theorem TypeAliasValueOrdinaryParses.value_unique_of_typeExpr
    (typeOutcomes : ExactDeterministicOutcomeSpec
      TypeExprOrdinaryParses TypeExprRejects)
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact typeOutcomes.successValueUnique leftCore rightCore
      | recovered rightCoreRejected rightRecovery =>
          exact False.elim
            (rightCoreRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftCoreRejected leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim
            (leftCoreRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered rightCoreRejected rightRecovery =>
          exact typeAliasValueRecoveryExactOutcomeSpec.successValueUnique
            leftRecovery rightRecovery

/-- Exact Core type outcomes lift through alias-value recovery without any
further prerequisite. -/
theorem typeAliasValueExactOutcomeSpecOfTypeExpr
    (typeOutcomes : ExactDeterministicOutcomeSpec
      TypeExprOrdinaryParses TypeExprRejects) :
    ExactDeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects where
  toDeterministicOutcomeSpec := typeAliasValueDeterministicOutcomeSpec
  successValueUnique :=
    TypeAliasValueOrdinaryParses.value_unique_of_typeExpr typeOutcomes
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact leftRejected.output_eq.trans rightRejected.output_eq.symm

end Solcore.Syntax.DeclarativeGrammar
