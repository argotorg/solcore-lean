import Solcore.Syntax.DeclarativeCoreLambdaParameterRecoveryOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParameterCoreOutcomeProperties

/-! Deterministic ordinary outcomes of the public named parameter. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every public pre-recovery boundary is also a recovery-scan stop. -/
theorem FunctionParameterBoundaryStops.toRecoveryStop
    {input : Remainder} (stops : FunctionParameterBoundaryStops input) :
    FunctionParameterRecoveryStops input := by
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | comma token => exact .comma token
  | rightParen token => exact .rightParen token

/-- Preserved carrier and window make the cursor-only rewind exact. -/
theorem FunctionParameterCoreRejectsWithPreservedWindow.exists_rewind_eq
    {typeRejects : Remainder → Remainder → Prop} {input : Remainder}
    (rejected : FunctionParameterCoreRejectsWithPreservedWindow typeRejects
      input) :
    ∃ failed, FunctionParameterCoreRejects typeRejects input failed ∧
      { failed with cursor := input.cursor } = input := by
  rcases rejected with ⟨failed, rejection, tokensEq, endIndexEq⟩
  refine ⟨failed, rejection, ?_⟩
  cases input
  cases failed
  simp_all

/-- Public named-parameter success has one deterministic final remainder. -/
theorem FunctionParameterOrdinaryParses.output_unique
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input : Remainder} {left right : Syntax.FunctionParameter}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input left afterLeft)
    (rightParsed : FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore =>
          exact leftCore.output_unique typeOutcomes rightCore
      | recovered rightRejected rightContinues rightRecovery =>
          rcases rightRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, leftCore⟩)
  | recovered leftRejected leftContinues leftRecovery =>
      cases rightParsed with
      | core rightCore =>
          rcases leftRejected with
            ⟨failed, coreRejected, tokensEq, endIndexEq⟩
          exact False.elim
            (functionParameterCoreDeterministicOutcomeSpec typeOutcomes
              |>.successRejectDisjoint coreRejected ⟨_, _, rightCore⟩)
      | recovered rightRejected rightContinues rightRecovery =>
          exact leftRecovery.output_unique rightRecovery

/-- Exact public rejection excludes direct and recovered ordinary success. -/
theorem FunctionParameterRejects.disjointOrdinary
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    {input rejected : Remainder}
    (rejection : FunctionParameterRejects typeRejects input rejected) :
    ¬ ∃ parameter output,
      FunctionParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output := by
  rintro ⟨parameter, output, successful⟩
  cases rejection with
  | boundary coreRejected stops =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact functionParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected continues recovered =>
          exact continues stops
  | recovery coreRejected continues recoveryRejected =>
      cases successful with
      | core coreParsed =>
          rcases coreRejected with
            ⟨failed, rejected, tokensEq, endIndexEq⟩
          exact functionParameterCoreDeterministicOutcomeSpec typeOutcomes
            |>.successRejectDisjoint rejected ⟨_, _, coreParsed⟩
      | recovered otherRejected otherContinues recovered =>
          exact functionParameterRecoveryDeterministicOutcomeSpec
            |>.successRejectDisjoint recoveryRejected ⟨_, _, recovered⟩

/-- Every public named-parameter rejection retains the rewound remainder. -/
theorem FunctionParameterRejects.output_eq
    {typeRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (rejection : FunctionParameterRejects typeRejects input rejected) :
    rejected = input := by
  cases rejection with
  | boundary => rfl
  | recovery coreRejected continues recoveryRejected =>
      exact recoveryRejected.output_eq

/-- Lift deterministic type outcomes through Core choice and recovery. -/
theorem functionParameterDeterministicOutcomeSpec
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects) :
    DeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses typeOrdinary typeRejects)
      (FunctionParameterRejects typeRejects) where
  successOutputUnique := FunctionParameterOrdinaryParses.output_unique
    typeOutcomes
  successRejectDisjoint := FunctionParameterRejects.disjointOrdinary
    typeOutcomes

end Solcore.Syntax.DeclarativeGrammar
