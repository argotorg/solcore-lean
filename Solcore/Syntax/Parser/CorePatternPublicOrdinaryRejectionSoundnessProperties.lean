import Solcore.Syntax.Parser.CorePatternPublicOutcomePrimitiveProperties

/-! Exact ordinary rejection at the public Core pattern boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every public pattern rejection is the exact rewound boundary or an
unavailable first recovery token after a window-preserving Core rejection. -/
theorem patternLayer_reject_ordinaryOutcome_sound
    (nested : Parser Pattern) (expression : Parser Expr)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      PatternInternals.patternCore nested expression input =
          .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    (coreWindow : Parser.PreservesTokenWindow
      (PatternInternals.patternCore nested expression))
    {input rejected : State} {failure : Failure}
    (result : patternLayer nested expression input =
      .reject failure rejected) :
    DeclarativeGrammar.PatternLayerRejects coreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold patternLayer at result
  cases coreResult : PatternInternals.patternCore nested expression input with
  | ok pattern output => simp [coreResult] at result
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
          PatternInternals.rewoundPattern_declarativeRemainder_eq input failed
            shape
      have coreRejected :=
        PatternInternals.patternCoreRejectsWithPreservedWindow_of_result
          nested expression coreRejects coreRejectSound coreWindow coreResult
      change (if PatternInternals.isPatternBoundary rewound then
          .reject coreFailure rewound
        else
          match rewound.advance? with
          | some (token, next) =>
              PatternInternals.recoverPatternAux token.span token.span
                (next.remainingCount + 1)
                (next.emit coreFailure.toDiagnostic)
          | none => .reject coreFailure rewound) =
            .reject failure rejected at result
      by_cases boundary : PatternInternals.isPatternBoundary rewound = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops :=
          PatternInternals.patternBoundaryStops_of_isPatternBoundary rewound
            boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.PatternLayerRejects.boundary coreRejected stops
      · have boundaryFalse : PatternInternals.isPatternBoundary rewound =
            false := Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues :=
          PatternInternals.no_patternBoundaryStops_of_isPatternBoundary_eq_false
            rewound boundaryFalse
        rw [rewoundEq] at continues
        cases advanced : rewound.advance? with
        | none =>
            simp only [advanced] at result
            have rejectedEq : rewound = rejected := by injection result
            subst rejected
            have recoveryRejected :=
              PatternInternals.patternRecoveryRejects_of_advance?_eq_none
                rewound advanced
            rw [rewoundEq] at recoveryRejected
            simpa only [rewoundEq] using
              DeclarativeGrammar.PatternLayerRejects.recovery coreRejected
                continues recoveryRejected
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases PatternInternals.recoverPatternAux_production_exists_ok
                token.span token.span (next.emit coreFailure.toDiagnostic) with
              ⟨pattern, output, success⟩
            change PatternInternals.recoverPatternAux token.span token.span
                (next.remainingCount + 1)
                (next.emit coreFailure.toDiagnostic) = .ok pattern output
              at success
            rw [success] at result
            contradiction

end Solcore.Syntax.Parser
