import Solcore.Syntax.Parser.CorePatternPublicOutcomePrimitiveProperties

/-! Ordinary-success soundness at the public Core pattern boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public pattern success is a direct ordinary Core success or the
exact recovery after a window-preserving Core rejection and cursor rewind. -/
theorem patternLayer_success_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (coreOrdinary : DeclarativeGrammar.Remainder → Pattern →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {pattern : Pattern},
      PatternInternals.patternCore nested expression input =
          .ok pattern output →
        coreOrdinary input.declarativeRemainder pattern
          output.declarativeRemainder)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      PatternInternals.patternCore nested expression input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (PatternInternals.patternCore nested expression))
    {input output : State} {pattern : Pattern}
    (result : patternLayer nested expression input = .ok pattern output) :
    DeclarativeGrammar.PatternLayerOrdinaryParses coreOrdinary coreRejects
      input.declarativeRemainder pattern output.declarativeRemainder := by
  unfold patternLayer at result
  cases coreResult : PatternInternals.patternCore nested expression input with
  | ok corePattern afterCore =>
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
          PatternInternals.rewoundPattern_declarativeRemainder_eq input failed
            shape
      have coreRejected :=
        PatternInternals.patternCoreRejectsWithPreservedWindow_of_result
          nested expression coreRejects coreRejectSound coreWindow coreResult
      change (if PatternInternals.isPatternBoundary rewound then
          .reject failure rewound
        else
          match rewound.advance? with
          | some (token, next) =>
              PatternInternals.recoverPatternAux token.span token.span
                (next.remainingCount + 1)
                (next.emit failure.toDiagnostic)
          | none => .reject failure rewound) = .ok pattern output at result
      by_cases boundary : PatternInternals.isPatternBoundary rewound = true
      · simp [boundary] at result
      · have boundaryFalse : PatternInternals.isPatternBoundary rewound =
            false := Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues :=
          PatternInternals.no_patternBoundaryStops_of_isPatternBoundary_eq_false
            rewound boundaryFalse
        rw [rewoundEq] at continues
        cases advanced : rewound.advance? with
        | none => simp [advanced] at result
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            have recovered :=
              PatternInternals.patternRecoveryParses_of_aux_success advanced
                result
            rw [rewoundEq] at recovered
            exact .recovered coreRejected continues recovered

end Solcore.Syntax.Parser
