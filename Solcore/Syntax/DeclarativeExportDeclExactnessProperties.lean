import Solcore.Syntax.DeclarativeExportDeclOutcomeProperties
import Solcore.Syntax.DeclarativeLocalExportExactnessProperties
import Solcore.Syntax.DeclarativePathExportExactnessProperties

/-! Exact complete export declarations across all four canonical forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportDecl_local_opening {start : SourceSpan}
    {input output : Remainder} {declaration : Syntax.ExportDecl}
    (parsed : LocalExportOrdinaryParses start input declaration output) :
    ExportDeclLeftBracePresentAt input := by
  rcases parsed with ⟨items, afterItems, itemsParsed, finishParsed⟩
  cases itemsParsed with
  | empty openingSpan closingSpan opening closing => exact ⟨openingSpan, opening⟩
  | nonempty closingAbsent parsed =>
      rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
        tokensEq, endIndexEq, opening, firstParsed, progress, tail, elementsEq,
        spanEq⟩
      exact ⟨openingSpan, opening⟩

private theorem exportDecl_exact_dispatch
    {input output : Remainder} {declaration : Syntax.ExportDecl}
    (parsed : ExportDeclOrdinaryParses input declaration output) :
    ∃ start afterKeyword,
      ExactTokenParses (.keyword .exportKw) input start afterKeyword ∧
      ((ExportDeclLeftBracePresentAt afterKeyword ∧
          LocalExportOrdinaryParses start afterKeyword declaration output) ∨
        (TokenKindAbsentAt afterKeyword.tokens afterKeyword.endIndex
            afterKeyword.cursor (.symbol .leftBrace) ∧
          PathExportOrdinaryParses start afterKeyword declaration output)) := by
  cases parsed with
  | ofLocal localParsed =>
      rcases localParsed with ⟨start, keyword, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inl ⟨exportDecl_local_opening payload, payload⟩⟩
  | ofModule moduleParsed =>
      rcases moduleParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .module payload⟩⟩
  | ofModuleAs aliasParsed =>
      rcases aliasParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .moduleAs payload⟩⟩
  | ofItemsFrom selectedParsed =>
      rcases selectedParsed with ⟨start, keyword, absent, payload⟩
      exact ⟨start, _, ⟨keyword, rfl⟩,
        Or.inr ⟨absent, .itemsFrom payload⟩⟩

/-- Complete exports fix their keyword span, entire payload, and closing span. -/
theorem ExportDeclOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    left = right := by
  rcases exportDecl_exact_dispatch leftParsed with
    ⟨leftSpan, leftAfterKeyword, leftKeyword, leftBranch⟩
  rcases exportDecl_exact_dispatch rightParsed with
    ⟨rightSpan, rightAfterKeyword, rightKeyword, rightBranch⟩
  rcases leftKeyword.result_unique rightKeyword with ⟨spanEq, afterEq⟩
  cases spanEq
  cases afterEq
  rcases leftBranch with ⟨leftPresent, leftLocal⟩ | ⟨leftAbsent, leftPath⟩
  · rcases rightBranch with ⟨rightPresent, rightLocal⟩ | ⟨rightAbsent, rightPath⟩
    · exact (localExportExactOutcomeSpec leftSpan).successValueUnique
        leftLocal rightLocal
    · exact False.elim (rightAbsent leftPresent)
  · rcases rightBranch with ⟨rightPresent, rightLocal⟩ | ⟨rightAbsent, rightPath⟩
    · exact False.elim (leftAbsent rightPresent)
    · exact (pathExportExactOutcomeSpec leftSpan).successValueUnique
        leftPath rightPath

/-- Complete export success fixes its entire AST and final remainder. -/
theorem ExportDeclOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportDeclOrdinaryParses input left afterLeft)
    (rightParsed : ExportDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

private theorem exportDecl_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exportDecl_present_conflicts_absent {input : Remainder}
    (present : ExportDeclLeftBracePresentAt input)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBrace)) : False :=
  absent present

/-- Complete export rejection fixes the selected local or path endpoint. -/
theorem ExportDeclRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportDeclRejects input left)
    (rightRejected : ExportDeclRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [exportDecl_absent_conflicts_exact, exportDecl_present_conflicts_absent,
      ExactTokenParses.output_unique, LocalExportRejects.output_unique,
      PathExportRejects.output_unique]

/-- Complete export declarations have unconditional exact AST, remainder,
and rejecting-endpoint outcomes, without diagnostic payload equality. -/
theorem exportDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportDeclOrdinaryParses ExportDeclRejects where
  toDeterministicOutcomeSpec := exportDeclDeterministicOutcomeSpec
  successValueUnique := ExportDeclOrdinaryParses.value_unique
  rejectOutputUnique := ExportDeclRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
