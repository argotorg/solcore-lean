import Solcore.Syntax.DeclarativeConstructorSelectionExactnessProperties
import Solcore.Syntax.DeclarativeExportNameOutcomeProperties
import Solcore.Syntax.DeclarativeSelectorNameExactnessProperties

/-! Exact wildcard, operator, and constructor-qualified export names. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exportName_token_conflicts_absent {input : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (present : TokenAt input.tokens input.endIndex input.cursor
      { span, value := kind })
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent ⟨span, present⟩

private theorem exportName_operator_opening
    {input output : Remainder} {selector : Syntax.SelectorName}
    (parsed : OperatorSelectorParses input selector output) :
    ExportNameTokenPresentAt input (.symbol .leftParen) := by
  rcases parsed with ⟨openingSpan, closingSpan, parts, closingIndex, tokensEq,
    endIndexEq, opening, partsParsed, nonempty, closing, cursorEq, selectorEq⟩
  exact ⟨openingSpan, opening⟩

private theorem exportName_present_conflicts_absent {input : Remainder}
    {kind : TokenKind} (present : ExportNameTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Prioritized export names fix every located name and constructor selection. -/
theorem ExportNameOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [TokenAt.token_unique, exportName_token_conflicts_absent,
      exportName_present_conflicts_absent, → exportName_operator_opening,
      OperatorSelectorParses.value_unique, IdentifierParses.result_unique,
      OptionalConstructorSelectionParses.result_unique]

/-- Export-name success fixes its complete AST and final remainder. -/
theorem ExportNameOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.ExportName}
    {afterLeft afterRight : Remainder}
    (leftParsed : ExportNameOrdinaryParses input left afterLeft)
    (rightParsed : ExportNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Export-name rejection fixes the priority-selected failing endpoint. -/
theorem ExportNameRejects.output_unique {input left right : Remainder}
    (leftRejected : ExportNameRejects input left)
    (rightRejected : ExportNameRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [exportName_present_conflicts_absent,
      selectorNameExactOutcomeSpec.rejectOutputUnique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      constructorSelectionExactOutcomeSpec.rejectOutputUnique]

/-- Export names have unconditional exact ordinary outcomes. -/
theorem exportNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ExportNameOrdinaryParses ExportNameRejects where
  toDeterministicOutcomeSpec := exportNameDeterministicOutcomeSpec
  successValueUnique := ExportNameOrdinaryParses.value_unique
  rejectOutputUnique := ExportNameRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
