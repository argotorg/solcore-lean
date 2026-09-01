import Solcore.Syntax.Parser.CoreExpressionAtomBoundaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionAtomRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Expression.Atom

/-!
Generic executable ordinary outcomes at the public Core atom rewind and
recovery boundary.
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
    (nested : Parser Expr) (block : Parser Block)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (ExpressionAtomInternals.expressionAtomCore nested block))
    {input failed : State} {failure : Failure}
    (result : ExpressionAtomInternals.expressionAtomCore nested block input =
      .reject failure failed) :
    DeclarativeGrammar.CoreAtomRejectsWithPreservedWindow coreRejects
      input.declarativeRemainder := by
  have resultShape := coreWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder, coreRejectSound result, shape.1,
    congrArg TokenWindow.endIndex shape.2⟩

/-- Every public atom success is a direct ordinary Core success or the exact
recovery after a window-preserving Core rejection and cursor rewind. -/
theorem expressionAtom_success_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (coreOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {expression : Expr},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .ok expression output →
        coreOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (ExpressionAtomInternals.expressionAtomCore nested block))
    {input output : State} {expression : Expr}
    (result : expressionAtom nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionAtomOrdinaryParses coreOrdinary coreRejects
      input.declarativeRemainder expression output.declarativeRemainder := by
  unfold expressionAtom at result
  cases coreResult : ExpressionAtomInternals.expressionAtomCore nested block
      input with
  | ok coreExpression afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core (coreSuccessSound coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape := coreWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq : (rewound.emit failure.toDiagnostic).declarativeRemainder
          = input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            failure.toDiagnostic shape
      have coreRejected := coreRejectsWithPreservedWindow_of_result nested
        block coreRejects coreRejectSound coreWindow coreResult
      change (if ExpressionAtomInternals.isAtomBoundary rewound then
          .reject failure rewound
        else ExpressionAtomInternals.recoverAtom
          (rewound.emit failure.toDiagnostic)) = .ok expression output
        at result
      by_cases boundary : ExpressionAtomInternals.isAtomBoundary rewound = true
      · simp [boundary] at result
      · have boundaryFalse : ExpressionAtomInternals.isAtomBoundary rewound =
            false := Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues :=
          ExpressionAtomInternals.no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false
            rewound boundaryFalse
        rw [rewoundEq] at continues
        have recovered :=
          ExpressionAtomInternals.recoverAtom_success_ordinary_sound result
        rw [emittedEq] at recovered
        exact .recovered coreRejected continues recovered

/-- Every public atom rejection is the exact rewound boundary or standalone
recovery rejection after a window-preserving Core rejection. -/
theorem expressionAtom_reject_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (ExpressionAtomInternals.expressionAtomCore nested block))
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionAtomRejects coreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold expressionAtom at result
  cases coreResult : ExpressionAtomInternals.expressionAtomCore nested block
      input with
  | ok expression output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape := coreWindow input
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
      have coreRejected := coreRejectsWithPreservedWindow_of_result nested
        block coreRejects coreRejectSound coreWindow coreResult
      change (if ExpressionAtomInternals.isAtomBoundary rewound then
          .reject coreFailure rewound
        else ExpressionAtomInternals.recoverAtom
          (rewound.emit coreFailure.toDiagnostic)) = .reject failure rejected
        at result
      by_cases boundary : ExpressionAtomInternals.isAtomBoundary rewound = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by
          injection result
        subst rejected
        have stops :=
          ExpressionAtomInternals.expressionAtomBoundaryStops_of_isAtomBoundary
            rewound boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.ExpressionAtomRejects.boundary coreRejected stops
      · have boundaryFalse : ExpressionAtomInternals.isAtomBoundary rewound =
            false := Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues :=
          ExpressionAtomInternals.no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false
            rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          ExpressionAtomInternals.recoverAtom_reject_ordinary_sound result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both public atom outcomes over one supplied Core bridge. -/
theorem expressionAtom_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (coreOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {expression : Expr},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .ok expression output →
        coreOrdinary input.declarativeRemainder expression
          output.declarativeRemainder)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      ExpressionAtomInternals.expressionAtomCore nested block input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (ExpressionAtomInternals.expressionAtomCore nested block)) :
    (∀ {input output : State} {expression : Expr},
      expressionAtom nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionAtomOrdinaryParses coreOrdinary
          coreRejects input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionAtom nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionAtomRejects coreRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨expressionAtom_success_ordinaryOutcome_sound nested block coreOrdinary
      coreRejects coreSuccessSound coreRejectSound coreWindow,
    expressionAtom_reject_ordinaryOutcome_sound nested block coreRejects
      coreRejectSound coreWindow⟩

/-- Lift a deterministic Core contract through the public executable atom
relations. -/
theorem expressionAtom_ordinaryOutcomeSpec
    {coreOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (coreOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec coreOrdinary
      coreRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionAtomOrdinaryParses coreOrdinary
        coreRejects)
      (DeclarativeGrammar.ExpressionAtomRejects coreRejects) :=
  DeclarativeGrammar.expressionAtomDeterministicOutcomeSpec coreOutcomes

end Solcore.Syntax.Parser
