import Solcore.Syntax.DeclarativeSelectedAliasExactnessProperties
import Solcore.Syntax.DeclarativeSelectedImportOutcomeProperties
import Solcore.Syntax.DeclarativeSelectorNameExactnessProperties

/-! Exact source names, optional aliases, and covered selected-import spans. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A selected import fixes its full source/alias record and covered span. -/
theorem SelectedImportOrdinaryParses.value_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) : left = right := by
  rcases leftParsed with ⟨leftAfterSource, leftSource, leftAlias, leftSpan⟩
  rcases rightParsed with ⟨rightAfterSource, rightSource, rightAlias, rightSpan⟩
  rcases selectorNameExactOutcomeSpec.successResultUnique leftSource rightSource with
    ⟨sourceEq, afterSourceEq⟩
  subst afterSourceEq
  have aliasEq := selectedAliasExactOutcomeSpec.successValueUnique leftAlias rightAlias
  cases left with
  | mk _ leftValue =>
      cases right with
      | mk _ rightValue =>
          cases leftValue
          cases rightValue
          simp_all

/-- Selected-import success fixes both the full located AST and remainder. -/
theorem SelectedImportOrdinaryParses.result_unique
    {input afterLeft afterRight : Remainder} {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- The first failing selected-import stage fixes its exact endpoint. -/
theorem SelectedImportRejects.output_unique {input left right : Remainder}
    (leftRejected : SelectedImportRejects input left)
    (rightRejected : SelectedImportRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [selectorNameExactOutcomeSpec.successOutputUnique,
      selectorNameExactOutcomeSpec.rejectOutputUnique,
      selectorNameExactOutcomeSpec.successRejectDisjoint,
      SelectedAliasRejects.output_unique]

/-- Complete selected-import outcomes have exact values and rejecting endpoints. -/
theorem selectedImportExactOutcomeSpec :
    ExactDeterministicOutcomeSpec SelectedImportOrdinaryParses SelectedImportRejects where
  toDeterministicOutcomeSpec := selectedImportDeterministicOutcomeSpec
  successValueUnique := SelectedImportOrdinaryParses.value_unique
  rejectOutputUnique := SelectedImportRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
