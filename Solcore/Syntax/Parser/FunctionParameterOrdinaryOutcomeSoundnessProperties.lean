import Solcore.Syntax.DeclarativeFunctionParameterPublicOutcomeProperties
import Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterBoundaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterCoreOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ParameterProperties

/-!
Complete executable ordinary outcomes at the public named-parameter rewind,
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
    (result : FunctionParameterInternals.namedParameterCore input =
      .reject failure failed) :
    DeclarativeGrammar.FunctionParameterCoreRejectsWithPreservedWindow
      typeRejects input.declarativeRemainder := by
  have resultShape :=
    FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    FunctionParameterInternals.namedParameterCore_reject_ordinary_sound
      typeRejects typeRejectSound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Every public success is direct Core success or exact rewound recovery. -/
theorem namedParameter_success_ordinaryOutcome_sound
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
    {input output : State} {parameter : FunctionParameter}
    (result : namedParameter input = .ok parameter output) :
    DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary typeRejects
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok coreParameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core
        (FunctionParameterInternals.namedParameterCore_success_ordinary_sound
          typeOrdinary typeSuccessSound coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
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
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) = .ok parameter output at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp [boundary] at result
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_functionParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recovered :=
          FunctionParameterInternals.recoverParameter_success_ordinary_sound
            result
        rw [emittedEq] at recovered
        exact .recovered coreRejected continues recovered

/-- Every public rejection is the exact rewound boundary or recovery reject. -/
theorem namedParameter_reject_ordinaryOutcome_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
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
        else FunctionParameterInternals.recoverParameter
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary : (rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := functionParameterBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.FunctionParameterRejects.boundary coreRejected stops
      · have boundaryFalse : (rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_functionParameterBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          FunctionParameterInternals.recoverParameter_reject_ordinary_sound
            result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both public executable ordinary outcomes. -/
theorem namedParameter_ordinaryOutcome_sound
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
    (∀ {input output : State} {parameter : FunctionParameter},
      namedParameter input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary
          typeRejects input.declarativeRemainder parameter
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      namedParameter input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namedParameter_success_ordinaryOutcome_sound typeOrdinary typeRejects
      typeSuccessSound typeRejectSound,
    namedParameter_reject_ordinaryOutcome_sound typeRejects typeRejectSound⟩

/-- Lift deterministic supplied type outcomes through the executable API. -/
theorem namedParameter_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FunctionParameterOrdinaryParses typeOrdinary
        typeRejects)
      (DeclarativeGrammar.FunctionParameterRejects typeRejects) :=
  DeclarativeGrammar.functionParameterDeterministicOutcomeSpec typeOutcomes

end Solcore.Syntax.Parser
