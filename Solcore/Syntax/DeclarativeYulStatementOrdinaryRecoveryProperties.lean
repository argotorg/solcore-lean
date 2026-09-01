import Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryGrammar

/-!
Functionality, boundary exclusion, and clean embedding for the outer
recovering Yul-statement outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem tokenAt_unique {tokens : Array Token} {endIndex index : Nat}
    {left right : Token} (leftAt : TokenAt tokens endIndex index left)
    (rightAt : TokenAt tokens endIndex index right) : left = right := by
  exact Option.some.inj (leftAt.2.symm.trans rightAt.2)

/-- A statement recovery scan has functional output from one remainder. -/
theorem YulStatementRecoveryScanParses.output_unique :
    ∀ {first leftLast rightLast : SourceSpan} {input : Remainder}
      {left right : Syntax.YulStmt} {afterLeft afterRight : Remainder},
      YulStatementRecoveryScanParses first leftLast input left afterLeft →
      YulStatementRecoveryScanParses first rightLast input right afterRight →
      afterLeft = afterRight := by
  intro first leftLast rightLast input left right afterLeft afterRight
    leftParsed
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

/-- One ordinary recovering statement layer has functional output. -/
theorem YulStatementLayerOrdinaryParses.output_unique
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec terminatedOrdinary
      terminatedRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input left afterLeft)
    (rightParsed : YulStatementLayerOrdinaryParses terminatedOrdinary
      terminatedRejects input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | terminated leftTerminated =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact outcomes.successOutputUnique leftTerminated rightTerminated
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          exact False.elim (outcomes.successRejectDisjoint rightRejected
            ⟨_, _, leftTerminated⟩)
  | recovered leftRejected leftContinues leftCurrent leftScan =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact False.elim (outcomes.successRejectDisjoint leftRejected
            ⟨_, _, rightTerminated⟩)
      | recovered rightRejected rightContinues rightCurrent rightScan =>
          have currentEq := tokenAt_unique leftCurrent rightCurrent
          cases currentEq
          exact leftScan.output_unique rightScan

/-- Every outer statement rejection is non-consuming. -/
theorem YulStatementRejects.output_eq {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) : rejected = input := by
  cases rejection <;> rfl

/-- Boundary exclusion for terminated successes lifts through recovery. -/
theorem YulStatementRejects.disjointLayerOrdinary
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (terminatedBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output,
          terminatedOrdinary input statement output)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output := by
  rintro ⟨statement, output, parsed⟩
  cases parsed with
  | terminated parsed =>
      exact terminatedBoundaryDisjoint rejection ⟨_, _, parsed⟩
  | recovered terminatedRejected continues current scan =>
      have rejectedEq := rejection.output_eq
      subst rejected
      exact continues rejection

/-- Construct the deterministic outcome contract for one recovering layer. -/
theorem yulStatementLayerDeterministicOutcomeSpec
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec terminatedOrdinary
      terminatedRejects)
    (terminatedBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output,
          terminatedOrdinary input statement output) :
    DeterministicOutcomeSpec
      (YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects)
      YulStatementRejects where
  successOutputUnique :=
    YulStatementLayerOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulStatementRejects.disjointLayerOrdinary terminatedBoundaryDisjoint

/-- A clean terminated success is an ordinary recovering-layer success. -/
theorem YulStatementLayerOrdinaryParses.ofClean
    {cleanTerminated terminatedOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      cleanTerminated input statement output →
        terminatedOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : cleanTerminated input statement output) :
    YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input statement output :=
  .terminated (cleanToOrdinary parsed)

end Solcore.Syntax.DeclarativeGrammar
