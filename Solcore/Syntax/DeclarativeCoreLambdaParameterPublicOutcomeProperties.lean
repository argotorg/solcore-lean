import Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeProperties
import Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeProperties

/-! Deterministic ordinary outcomes of the public lambda parameter. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every pre-recovery boundary is also a recovery-scan stop. -/
theorem LambdaParameterBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : LambdaParameterBoundaryStops input) :
    FunctionParameterRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token

/-- Preserved carrier and window make the cursor-only rewind exact. -/
theorem LambdaParameterCoreRejectsWithPreservedWindow.exists_rewind_eq
    {typeRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : LambdaParameterCoreRejectsWithPreservedWindow typeRejects
      input) :
    ∃ failed, LambdaParameterCoreRejects typeRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public ordinary success has one deterministic remainder. -/
theorem LambdaParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.LambdaParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects input
      left afterLeft)
    (rightParsed : LambdaParameterOrdinaryParses typeOrdinary typeRejects input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.output_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes direct and recovered ordinary success. -/
theorem LambdaParameterRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : LambdaParameterRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output := by
  rintro ⟨parameter, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact lambdaParameterRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public rejection retains the original rewound remainder. -/
theorem LambdaParameterRejects.output_eq
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : LambdaParameterRejects typeRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift deterministic type outcomes through Core choice and recovery. -/
theorem lambdaParameterDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (LambdaParameterOrdinaryParses typeOrdinary typeRejects)
      (LambdaParameterRejects typeRejects) where
  successOutputUnique := LambdaParameterOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := LambdaParameterRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
