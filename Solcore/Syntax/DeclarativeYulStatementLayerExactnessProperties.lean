import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeYulStatementTerminatedBoundaryProperties

/-! Exact optional termination and recovery outcomes for one Yul statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional semicolon consumption preserves the complete core statement AST. -/
theorem YulStatementTerminatedOrdinaryParses.value_unique
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input left afterLeft)
    (rightParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftCore, leftCoreParsed, leftSemicolon⟩
  rcases rightParsed with ⟨rightCore, rightCoreParsed, rightSemicolon⟩
  exact outcomes.successValueUnique leftCoreParsed rightCoreParsed

/-- Exact core outcomes remain exact after maximal optional termination. -/
theorem yulStatementTerminatedExactOutcomeSpec
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec coreOrdinary coreRejects) :
    ExactDeterministicOutcomeSpec (YulStatementTerminatedOrdinaryParses coreOrdinary)
      (YulStatementTerminatedRejects coreRejects) where
  toDeterministicOutcomeSpec :=
    yulStatementTerminatedDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulStatementTerminatedOrdinaryParses.value_unique outcomes
  rejectOutputUnique := outcomes.rejectOutputUnique

/-- Recovery fixes its error span and AST when the accumulated spans are fixed. -/
theorem YulStatementRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.YulStmt} {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementRecoveryScanParses first last input left afterLeft)
    (rightParsed : YulStatementRecoveryScanParses first last input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightCurrent rightTail =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact ih rightTail

/-- Ordinary recovery preserves exact successful statement ASTs. -/
theorem YulStatementLayerOrdinaryParses.value_unique
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec terminatedOrdinary terminatedRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input left afterLeft)
    (rightParsed : YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | terminated leftTerminated =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact outcomes.successValueUnique leftTerminated rightTerminated
      | recovered rightRejected _ _ _ =>
          exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftTerminated⟩)
  | recovered leftRejected _ leftCurrent leftScan =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, rightTerminated⟩)
      | recovered _ _ rightCurrent rightScan =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact leftScan.value_unique rightScan

/-- Statement boundary rejection has a unique complete non-consuming endpoint. -/
theorem YulStatementRejects.output_unique {input left right : Remainder}
    (leftRejected : YulStatementRejects input left)
    (rightRejected : YulStatementRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact terminated outcomes lift through statement recovery unchanged. -/
theorem yulStatementLayerExactOutcomeSpec
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec terminatedOrdinary terminatedRejects)
    (boundaryDisjoint : ∀ {input rejected}, YulStatementRejects input rejected →
      ¬ ∃ statement output, terminatedOrdinary input statement output) :
    ExactDeterministicOutcomeSpec
      (YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects)
      YulStatementRejects where
  toDeterministicOutcomeSpec :=
    yulStatementLayerDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec boundaryDisjoint
  successValueUnique := YulStatementLayerOrdinaryParses.value_unique outcomes
  rejectOutputUnique := YulStatementRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
