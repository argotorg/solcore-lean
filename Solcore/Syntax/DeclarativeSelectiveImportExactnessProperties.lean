import Solcore.Syntax.DeclarativeSelectiveImportOutcomeProperties
import Solcore.Syntax.DeclarativeSelectedImportsExactnessProperties
import Solcore.Syntax.DeclarativeModulePathExactnessProperties
import Solcore.Syntax.DeclarativeHidingClauseExactnessProperties
import Solcore.Syntax.DeclarativeImportTerminatorExactnessProperties

/-! Exact selective imports, including source-order selectors and optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Exact selectors, path, and hiding fix the entire selective-import AST. -/
theorem SelectiveImportOrdinaryParses.value_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right afterRight) : left = right := by
  cases leftParsed with
  | parsed _ leftSelection leftFrom leftPath leftHiding leftTerminator =>
      cases rightParsed with
      | parsed _ rightSelection rightFrom rightPath rightHiding rightTerminator =>
          rcases selectedImportsExactOutcomeSpec.successResultUnique
              leftSelection rightSelection with ⟨selectionEq, afterSelectionEq⟩
          subst selectionEq
          subst afterSelectionEq
          have afterFromEq := leftFrom.output_unique rightFrom
          subst afterFromEq
          rcases modulePathExactOutcomeSpec.successResultUnique leftPath rightPath with
            ⟨pathEq, afterPathEq⟩
          subst pathEq
          subst afterPathEq
          rcases optionalHidingExactOutcomeSpec.successResultUnique leftHiding rightHiding with
            ⟨hidingEq, afterHidingEq⟩
          subst hidingEq
          subst afterHidingEq
          have endEq := (importTerminatorExactOutcomeSpec _).successValueUnique
            leftTerminator rightTerminator
          cases endEq
          rfl

/-- Selective-import success fixes the full located AST and remainder. -/
theorem SelectiveImportOrdinaryParses.result_unique (start : SourceSpan)
    {input afterLeft afterRight : Remainder} {left right : Syntax.ImportDecl}
    (leftParsed : SelectiveImportOrdinaryParses start input left afterLeft)
    (rightParsed : SelectiveImportOrdinaryParses start input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique start rightParsed, leftParsed.output_unique start rightParsed⟩

/-- A selective payload fixes the first failing stage's exact remainder. -/
theorem SelectiveImportRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectiveImportRejects input left)
    (rightRejected : SelectiveImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 12) [absent_conflicts_exact, ExactTokenParses.output_unique,
      selectedImportsExactOutcomeSpec.successOutputUnique,
      selectedImportsExactOutcomeSpec.rejectOutputUnique,
      selectedImportsExactOutcomeSpec.successRejectDisjoint,
      modulePathExactOutcomeSpec.successOutputUnique,
      modulePathExactOutcomeSpec.rejectOutputUnique,
      modulePathExactOutcomeSpec.successRejectDisjoint,
      optionalHidingExactOutcomeSpec.successOutputUnique,
      optionalHidingExactOutcomeSpec.rejectOutputUnique,
      optionalHidingExactOutcomeSpec.successRejectDisjoint,
      ImportTerminatorRejects.output_unique]

/-- Selective-import payload outcomes are fully exact at a fixed outer start. -/
theorem selectiveImportExactOutcomeSpec (start : SourceSpan) :
    ExactDeterministicOutcomeSpec (SelectiveImportOrdinaryParses start)
      SelectiveImportRejects where
  toDeterministicOutcomeSpec := selectiveImportDeterministicOutcomeSpec start
  successValueUnique := SelectiveImportOrdinaryParses.value_unique start
  rejectOutputUnique := SelectiveImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
