import Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryProperties

/-! Deterministic outcomes at the public Core atom recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A pre-recovery boundary is also a stop of the recovery scan itself. -/
theorem ExpressionAtomBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : ExpressionAtomBoundaryStops input) :
    ExpressionAtomRecoveryStops input input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token
  | rightBracket token => exact .rightBracket token
  | rightBrace token => exact .rightBrace token
  | question token => exact .question token
  | colon token => exact .colon token
  | fatArrow token => exact .fatArrow token
  | pipe token => exact .pipe token
  | elseKeyword token => exact .elseKeyword token

/-- Preserved carrier and active-window evidence makes cursor-only rewind
exactly the original declarative input. -/
theorem CoreAtomRejectsWithPreservedWindow.exists_rewind_eq
    {coreRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : CoreAtomRejectsWithPreservedWindow coreRejects input) :
    ∃ failed, coreRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary atom success has a functional output whenever the Core
outcome does. -/
theorem ExpressionAtomOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input
      left afterLeft)
    (rightParsed : ExpressionAtomOrdinaryParses coreOrdinary coreRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact coreOutcomes.successOutputUnique leftCore rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim (coreOutcomes.successRejectDisjoint coreRejected
            ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes both direct Core and recovered success. -/
theorem ExpressionAtomRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : ExpressionAtomRejects coreRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact coreOutcomes.successRejectDisjoint rejected
            ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact expressionAtomRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public atom rejection leaves the rewound declarative input
unchanged. -/
theorem ExpressionAtomRejects.output_eq
    {coreRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : ExpressionAtomRejects coreRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift a deterministic Core outcome through rewind and atom recovery. -/
theorem expressionAtomDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (coreOutcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (ExpressionAtomOrdinaryParses coreOrdinary coreRejects)
      (ExpressionAtomRejects coreRejects) where
  successOutputUnique := ExpressionAtomOrdinaryParses.output_unique
    coreOutcomes
  successRejectDisjoint := ExpressionAtomRejects.disjointOrdinary
    coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
