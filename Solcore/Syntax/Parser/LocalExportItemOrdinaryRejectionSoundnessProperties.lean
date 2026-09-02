import Solcore.Syntax.DeclarativeLocalExportItemOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ExportNameOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ExportPathOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection reflection for local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem localExportItemQualifiedStartAt_of_dispatcher_eq_true
    {input : State}
    (present : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = true) :
    DeclarativeGrammar.LocalExportItemQualifiedStartAt
      input.declarativeRemainder := by
  rcases Bool.and_eq_true_iff.mp present with
    ⟨identifierPresent, dotPresent⟩
  rcases identifierPresentAt_of_isIdentifier_eq_true identifierPresent with
    ⟨identifierSpan, text, identifierToken⟩
  rcases symbol_eq_ok_of_isSymbol_eq_true .dot .exportDecl dotPresent with
    ⟨dot, dotResult⟩
  refine ⟨identifierSpan, dot.span, text, identifierToken, ?_⟩
  exact (symbol_success_exactTokenParses .dot .exportDecl dotResult).1

private theorem identifierDotAbsentAt_of_dispatcher_eq_false {input : State}
    (stopped : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = false) :
    DeclarativeGrammar.IdentifierDotAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨identifierSpan, dotSpan, text, identifierAt, dotAt⟩
  have identifierPresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [identifierAt.1, ↓reduceIte, identifierAt.2,
      Option.map_some]
  have dotPresent : isSymbol
      { input with cursor := input.cursor + 1 } .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  rw [identifierPresent, dotPresent] at stopped
  contradiction

private theorem exportPathRejects_identifierAbsentAt
    {input rejected : DeclarativeGrammar.Remainder}
    (rejection : DeclarativeGrammar.ExportPathRejects input rejected) :
    DeclarativeGrammar.IdentifierAbsentAt input := by
  cases rejection with
  | firstRejected identifierRejected =>
      cases identifierRejected with
      | absent identifierAbsent => exact identifierAbsent

private theorem exportPath_ne_reject_of_isIdentifier_eq_true
    {input rejected : State} {failure : Failure}
    (present : isIdentifier input = true)
    (result : ExportInternals.exportPath input = .reject failure rejected) :
    False := by
  have identifierAbsent := exportPathRejects_identifierAbsentAt
    (exportPath_reject_ordinaryOutcome_sound result)
  rcases identifierPresentAt_of_isIdentifier_eq_true present with
    ⟨span, text, token⟩
  exact identifierAbsent ⟨span, text, token⟩

/-- Every executable local-export-item rejection records the exact qualified
dot/star failure or the prioritized unqualified export-name failure. -/
theorem localExportItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.localExportItem input =
      .reject failure rejected) :
    DeclarativeGrammar.LocalExportItemRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.localExportItem at result
  by_cases qualified : (isIdentifier input && isSymbol
      { input with cursor := input.cursor + 1 } .dot) = true
  · simp only [qualified, if_true] at result
    have qualifiedStart :=
      localExportItemQualifiedStartAt_of_dispatcher_eq_true qualified
    have identifierPresent := (Bool.and_eq_true_iff.mp qualified).1
    cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at result
    | reject pathFailure pathRejected =>
        exact False.elim
          (exportPath_ne_reject_of_isIdentifier_eq_true identifierPresent
            pathResult)
    | ok path afterPath =>
        have pathParsed := exportPath_success_ordinaryOutcome_sound pathResult
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject dotFailure dotRejected =>
            have dotRejectedEq := symbol_reject_state_eq .dot .exportDecl
              dotResult
            subst dotRejected
            simp only [dotResult] at result
            cases result
            exact .moduleDotMissing qualifiedStart pathParsed
              (symbol_reject_tokenKindAbsentAt .dot .exportDecl dotResult)
        | ok dot afterDot =>
            have dotParsed := symbol_success_exactTokenParses .dot .exportDecl
              dotResult
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | ok marker afterMarker => simp [markerResult] at result
            | reject markerFailure markerRejected =>
                have markerRejectedEq := symbol_reject_state_eq .star
                  .exportDecl markerResult
                subst markerRejected
                simp only [markerResult] at result
                cases result
                exact .moduleStarMissing qualifiedStart pathParsed dot.span
                  dotParsed
                  (symbol_reject_tokenKindAbsentAt .star .exportDecl
                    markerResult)
  · have qualifiedAbsent : (isIdentifier input && isSymbol
        { input with cursor := input.cursor + 1 } .dot) = false :=
      Bool.eq_false_iff.mpr qualified
    simp only [qualifiedAbsent, Bool.false_eq_true, if_false] at result
    have qualifiedMissing :=
      identifierDotAbsentAt_of_dispatcher_eq_false qualifiedAbsent
    cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at result
    | ok name afterName => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .nameRejected qualifiedMissing
          (exportName_reject_ordinaryOutcome_sound nameResult)

end Solcore.Syntax.Parser
