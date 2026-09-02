import Solcore.Syntax.DeclarativeTypeAliasValueExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasProperties
import Solcore.Syntax.Parser.TypeAliasValueRecoveryOrdinaryOutcomeSoundnessProperties

/-! Complete executable ordinary outcomes for recovery-aware alias values. -/

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

namespace TypeAliasInternals

private theorem typeAliasValueCoreRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : typeExpr input = .reject failure failed) :
    DeclarativeGrammar.TypeAliasValueCoreRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape := typeExpr_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    typeExpr_ordinaryOutcome_sound.2 result, shape.1,
    congrArg TokenWindow.endIndex shape.2⟩

/-- Every executable alias-value success is direct Core success or exact
recovery after cursor rewind and diagnostic emission. -/
theorem parseAliasValue_success_ordinaryOutcome_sound
    {input output : State} {value : TypeExpr}
    (result : parseAliasValue input = .ok value output) :
    DeclarativeGrammar.TypeAliasValueOrdinaryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core (typeExpr_ordinaryOutcome_sound.1 coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape := typeExpr_preservesTokenWindow input
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
      have coreRejected :=
        typeAliasValueCoreRejectsWithPreservedWindow_of_result coreResult
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value output at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .semicolon) = true
      · simp [boundary] at result
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have recovered := recoverTypeAliasValue_success_ordinary_sound result
        rw [emittedEq] at recovered
        exact .recovered coreRejected recovered

/-- Every executable alias-value rejection is the exact rewound boundary or
the exact non-consuming recovery rejection. -/
theorem parseAliasValue_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : parseAliasValue input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasValueRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok value output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape := typeExpr_preservesTokenWindow input
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
      have coreRejected :=
        typeAliasValueCoreRejectsWithPreservedWindow_of_result coreResult
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject coreFailure rewound
        else recoverTypeAliasValue
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .semicolon) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := typeAliasValueBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.TypeAliasValueRejects.boundary coreRejected stops
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_typeAliasValueBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          recoverTypeAliasValue_reject_ordinary_sound result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both executable ordinary alias-value outcomes. -/
theorem parseAliasValue_ordinaryOutcome_sound :
    (∀ {input output : State} {value : TypeExpr},
      parseAliasValue input = .ok value output →
        DeclarativeGrammar.TypeAliasValueOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseAliasValue input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasValueRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨parseAliasValue_success_ordinaryOutcome_sound,
    parseAliasValue_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic recovery-aware alias-value outcomes. -/
theorem parseAliasValue_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueDeterministicOutcomeSpec

/-- Exact Core type outcomes lift to exact recovery-aware executable alias
values. -/
theorem parseAliasValue_exactOutcomeSpec_of_typeExpr
    (typeOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueExactOutcomeSpecOfTypeExpr typeOutcomes

/-- Re-export unconditional exact recovery-aware alias-value outcomes. -/
theorem parseAliasValue_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueExactOutcomeSpec

/-- Under exact Core type outcomes, two successful executable reflections
have the same alias value and final declarative remainder. -/
theorem parseAliasValue_success_result_unique_of_typeExpr
    (typeOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : parseAliasValue input = .ok left leftOutput)
    (rightResult : parseAliasValue input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
    typeOutcomes
    (parseAliasValue_success_ordinaryOutcome_sound leftResult)
    (parseAliasValue_success_ordinaryOutcome_sound rightResult)

/-- Two successful executable reflections have the same alias value and final
declarative remainder. -/
theorem parseAliasValue_success_result_unique
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : parseAliasValue input = .ok left leftOutput)
    (rightResult : parseAliasValue input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique
    (parseAliasValue_success_ordinaryOutcome_sound leftResult)
    (parseAliasValue_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable alias-value reflections always have the same
rewound declarative endpoint. -/
theorem parseAliasValue_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : parseAliasValue input = .reject leftFailure leftOutput)
    (rightResult : parseAliasValue input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueRejects.output_unique
    (parseAliasValue_reject_ordinaryOutcome_sound leftResult)
    (parseAliasValue_reject_ordinaryOutcome_sound rightResult)

end TypeAliasInternals
end Solcore.Syntax.Parser
