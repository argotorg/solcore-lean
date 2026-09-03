import Solcore.Syntax.DeclarativeSelectedImportExactnessProperties
import Solcore.Syntax.DeclarativeSelectedImportsOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties

/-! Exact nonempty source-order selected-import lists, including delimiter spans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A selected-import list fixes its nonempty elements and complete range. -/
theorem SelectedImportsOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) : left = right := by
  have valueEq := NonemptyTrailingDelimitedListParses.value_unique
    selectedImportExactOutcomeSpec leftParsed rightParsed
  cases left with
  | mk _ leftElements =>
      cases leftElements
      cases right with
      | mk _ rightElements =>
          cases rightElements
          simp_all [Syntax.NonemptyList.toList]

/-- The complete selected-import-list result is unique. -/
theorem SelectedImportsOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A selected-import list has one exact first-failure endpoint. -/
theorem SelectedImportsRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedImportsRejects input left)
    (rightRejected : SelectedImportsRejects input right) : left = right :=
  (nonemptyTrailingDelimitedListExactOutcomeSpec .leftBrace .rightBrace
    selectedImportExactOutcomeSpec).rejectOutputUnique leftRejected rightRejected

/-- Required selected-import lists are fully exact. -/
theorem selectedImportsExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedImportsOrdinaryParses SelectedImportsRejects where
  toDeterministicOutcomeSpec := selectedImportsDeterministicOutcomeSpec
  successValueUnique := SelectedImportsOrdinaryParses.value_unique
  rejectOutputUnique := SelectedImportsRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
