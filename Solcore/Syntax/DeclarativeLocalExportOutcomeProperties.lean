import Solcore.Syntax.DeclarativeDelimitedTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeFinishExportOutcomeProperties
import Solcore.Syntax.DeclarativeLocalExportItemOutcomeProperties
import Solcore.Syntax.DeclarativeLocalExportOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for local export payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem localExportItemsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses .leftBrace .rightBrace
        LocalExportItemOrdinaryParses)
      (DelimitedListRejects .leftBrace .rightBrace true true
        LocalExportItemOrdinaryParses LocalExportItemRejects) :=
  trailingDelimitedListDeterministicOutcomeSpec .leftBrace .rightBrace
    localExportItemDeterministicOutcomeSpec

private theorem finishExport_output_unique_anyValue
    {start : SourceSpan} {leftValue rightValue : Syntax.ExportDeclValue}
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FinishExportOrdinaryParses start leftValue input left
      afterLeft)
    (rightParsed : FinishExportOrdinaryParses start rightValue input right
      afterRight) : afterLeft = afterRight := by
  rcases leftParsed with
    ⟨leftSemicolonSpan, leftSemicolon, leftOutputEq, leftDeclarationEq⟩
  rcases rightParsed with
    ⟨rightSemicolonSpan, rightSemicolon, rightOutputEq,
      rightDeclarationEq⟩
  rw [leftOutputEq, rightOutputEq]

/-- Ordinary local-export payload success has one final remainder. -/
theorem LocalExportOrdinaryParses.output_unique (start : SourceSpan)
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : LocalExportOrdinaryParses start input left afterLeft)
    (rightParsed : LocalExportOrdinaryParses start input right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftItems, leftAfterItems, leftItemsParsed,
    leftFinish⟩
  rcases rightParsed with ⟨rightItems, rightAfterItems, rightItemsParsed,
    rightFinish⟩
  have afterItemsEq := localExportItemsDeterministicOutcomeSpec
    |>.successOutputUnique leftItemsParsed rightItemsParsed
  subst afterItemsEq
  exact finishExport_output_unique_anyValue leftFinish rightFinish

/-- Exact local-export rejection excludes every ordinary success. -/
theorem LocalExportRejects.disjointOrdinary (start : SourceSpan)
    {input rejected : Remainder}
    (rejection : LocalExportRejects input rejected) :
    ¬ ∃ declaration output,
      LocalExportOrdinaryParses start input declaration output := by
  rintro ⟨declaration, output, successful⟩
  rcases successful with ⟨successfulItems, successfulAfterItems,
    successfulItemsParsed, successfulFinish⟩
  cases rejection with
  | itemsRejected itemsRejected =>
      exact localExportItemsDeterministicOutcomeSpec.successRejectDisjoint
        itemsRejected ⟨_, _, successfulItemsParsed⟩
  | finishRejected rejectedItems finishRejected =>
      have afterItemsEq := localExportItemsDeterministicOutcomeSpec
        |>.successOutputUnique rejectedItems successfulItemsParsed
      subst afterItemsEq
      exact (finishExportDeterministicOutcomeSpec start
        (.local successfulItems)).successRejectDisjoint finishRejected
          ⟨_, _, successfulFinish⟩

/-- Local export payloads have deterministic and exclusive broad outcomes for
each fixed outer start span. -/
theorem localExportDeterministicOutcomeSpec (start : SourceSpan) :
    DeterministicOutcomeSpec (LocalExportOrdinaryParses start)
      LocalExportRejects where
  successOutputUnique := LocalExportOrdinaryParses.output_unique start
  successRejectDisjoint := LocalExportRejects.disjointOrdinary start

end Solcore.Syntax.DeclarativeGrammar
