import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties
import Solcore.Syntax.DeclarativeSelectedImportOutcomeProperties
import Solcore.Syntax.DeclarativeSelectedImportsOutcomeGrammar

/-! Deterministic and exclusive broad outcomes for selected-import lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import lists have one final remainder. -/
theorem SelectedImportsOrdinaryParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : NonemptyDelimitedList Syntax.SelectedImport}
    (leftParsed : SelectedImportsOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold SelectedImportsOrdinaryParses SelectedImportsParses at leftParsed rightParsed
  exact NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftBrace) (closing := .rightBrace)
    (elementParses := SelectedImportOrdinaryParses)
    SelectedImportOrdinaryParses.output_unique leftParsed rightParsed

/-- Exact list rejection excludes every ordinary selected-import-list
success. -/
theorem SelectedImportsRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedImportsRejects input rejected) :
    ¬ ∃ selections output,
      SelectedImportsOrdinaryParses input selections output := by
  rintro ⟨selections, output, parsed⟩
  unfold SelectedImportsOrdinaryParses SelectedImportsParses at parsed
  exact rejection.disjointNonemptyTrailing
    selectedImportDeterministicOutcomeSpec (fun ordinary => ordinary)
      ⟨_, _, parsed⟩

/-- Required selected-import lists have deterministic and exclusive broad
ordinary outcomes. -/
theorem selectedImportsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedImportsOrdinaryParses
      SelectedImportsRejects where
  successOutputUnique := SelectedImportsOrdinaryParses.output_unique
  successRejectDisjoint := SelectedImportsRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
