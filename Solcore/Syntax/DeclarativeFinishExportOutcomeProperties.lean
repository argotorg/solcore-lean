import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeFinishExportOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for finishing an export. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact export finishing has one final remainder. -/
theorem FinishExportParses.output_unique
    {start : SourceSpan} {value : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportParses start value input left afterLeft)
    (rightParsed : FinishExportParses start value input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftSemicolonSpan, leftSemicolon, leftOutputEq, leftDeclarationEq⟩
  rcases rightParsed with
    ⟨rightSemicolonSpan, rightSemicolon, rightOutputEq,
      rightDeclarationEq⟩
  rw [leftOutputEq, rightOutputEq]

/-- Missing-semicolon rejection excludes every ordinary export finish. -/
theorem FinishExportRejects.disjointOrdinary
    (start : SourceSpan) (value : Syntax.ExportDeclValue)
    {input rejected : Remainder}
    (rejection : FinishExportRejects input rejected) :
    ¬ ∃ declaration output,
      FinishExportOrdinaryParses start value input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases rejection with
  | semicolonMissing semicolonAbsent =>
      rcases successful with
        ⟨semicolonSpan, semicolon, outputEq, declarationEq⟩
      exact semicolonAbsent ⟨semicolonSpan, semicolon⟩

/-- Export finishing has a deterministic and exclusive broad outcome. -/
theorem finishExportDeterministicOutcomeSpec (start : SourceSpan)
    (value : Syntax.ExportDeclValue) :
    DeterministicOutcomeSpec (FinishExportOrdinaryParses start value)
      FinishExportRejects where
  successOutputUnique := FinishExportParses.output_unique
  successRejectDisjoint := FinishExportRejects.disjointOrdinary start value

end Solcore.Syntax.DeclarativeGrammar
