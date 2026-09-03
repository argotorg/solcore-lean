import Solcore.Syntax.DeclarativeCoreLambdaParameterExactnessProperties
import Solcore.Syntax.Parser.CoreLambdaParameterBoundaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaParameterCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ParameterProperties

/-!
Complete executable ordinary outcomes at the public lambda-parameter rewind,
boundary, diagnostic emission, and recovery layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rewound_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

private theorem emitted_rewound_declarativeRemainder_eq
    (input failed : State) (diagnostic : ParseDiagnostic)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    State.declarativeRemainder
        (({ failed with cursor := input.cursor } : State).emit diagnostic) =
      input.declarativeRemainder := by
  unfold State.emit State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

private theorem coreRejectsWithPreservedWindow_of_result
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input failed : State} {failure : Failure}
    (result : LambdaParameterInternals.lambdaParameterCore input =
      .reject failure failed) :
    DeclarativeGrammar.LambdaParameterCoreRejectsWithPreservedWindow
      typeRejects input.declarativeRemainder := by
  have resultShape :=
    LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    LambdaParameterInternals.lambdaParameterCore_reject_ordinary_sound
      typeRejects typeRejectSound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Every public success is direct Core success or exact rewound recovery. -/
theorem lambdaParameter_success_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input output : State} {parameter : LambdaParameter}
    (result : lambdaParameter input = .ok parameter output) :
    DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary typeRejects
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold lambdaParameter at result
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok coreParameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core
        (LambdaParameterInternals.lambdaParameterCore_success_ordinary_sound
          typeOrdinary typeSuccessSound coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit failure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            failure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok parameter output at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp [boundary] at result
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_lambdaParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recovered :=
          LambdaParameterInternals.recoverLambdaParameter_success_ordinary_sound
            result
        rw [emittedEq] at recovered
        exact .recovered coreRejected continues recovered

/-- Every public rejection is the exact rewound boundary or recovery reject. -/
theorem lambdaParameter_reject_ordinaryOutcome_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : lambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold lambdaParameter at result
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit coreFailure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            coreFailure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result
        typeRejects typeRejectSound coreResult
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject coreFailure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := lambdaParameterBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.LambdaParameterRejects.boundary coreRejected stops
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_lambdaParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          LambdaParameterInternals.recoverLambdaParameter_reject_ordinary_sound
            result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both public executable ordinary outcomes. -/
theorem lambdaParameter_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {parameter : LambdaParameter},
      lambdaParameter input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary
          typeRejects input.declarativeRemainder parameter
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      lambdaParameter input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaParameter_success_ordinaryOutcome_sound typeOrdinary typeRejects
      typeSuccessSound typeRejectSound,
    lambdaParameter_reject_ordinaryOutcome_sound typeRejects typeRejectSound⟩

/-- Lift deterministic supplied type outcomes through the executable API. -/
theorem lambdaParameter_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterOrdinaryParses typeOrdinary
        typeRejects)
      (DeclarativeGrammar.LambdaParameterRejects typeRejects) :=
  DeclarativeGrammar.lambdaParameterDeterministicOutcomeSpec typeOutcomes

/-- Concrete public Core types discharge every lambda-parameter exactness premise. -/
theorem lambdaParameter_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterOrdinaryParses
        DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects)
      (DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects) :=
  DeclarativeGrammar.lambdaParameterPublicExactOutcomeSpec

/-- Public executable parameter successes agree on their complete AST and remainder. -/
theorem lambdaParameter_success_result_unique
    {input leftOutput rightOutput : State} {left right : LambdaParameter}
    (leftResult : lambdaParameter input = .ok left leftOutput)
    (rightResult : lambdaParameter input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_exactOutcomeSpec.successResultUnique
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound leftResult)
    (lambdaParameter_success_ordinaryOutcome_sound
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects
      typeExpr_success_sound typeExpr_reject_sound rightResult)

/-- Public executable parameter rejections agree on the complete rewound endpoint. -/
theorem lambdaParameter_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : lambdaParameter input = .reject leftFailure leftOutput)
    (rightResult : lambdaParameter input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_exactOutcomeSpec.rejectOutputUnique
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound leftResult)
    (lambdaParameter_reject_ordinaryOutcome_sound DeclarativeGrammar.TypeExprRejects
      typeExpr_reject_sound rightResult)

end Solcore.Syntax.Parser
