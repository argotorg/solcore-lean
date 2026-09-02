import Solcore.Syntax.DeclarativeSelectedAliasOutcomeProperties
import Solcore.Syntax.DeclarativeSelectedImportOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeProperties

/-! Deterministic and exclusive broad outcomes for one selected import. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary selected-import success has one final remainder. -/
theorem SelectedImportOrdinaryParses.output_unique
    {input afterLeft afterRight : Remainder}
    {left right : Syntax.SelectedImport}
    (leftParsed : SelectedImportOrdinaryParses input left afterLeft)
    (rightParsed : SelectedImportOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold SelectedImportOrdinaryParses SelectedImportParses at leftParsed rightParsed
  rcases leftParsed with
    ⟨afterLeftSource, leftSource, leftAlias, leftSpan⟩
  rcases rightParsed with
    ⟨afterRightSource, rightSource, rightAlias, rightSpan⟩
  have afterSourceEq :=
    selectorNameDeterministicOutcomeSpec.successOutputUnique leftSource
      rightSource
  subst afterRightSource
  exact selectedAliasDeterministicOutcomeSpec.successOutputUnique leftAlias
    rightAlias

/-- Exact selected-import rejection excludes every ordinary success. -/
theorem SelectedImportRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : SelectedImportRejects input rejected) :
    ¬ ∃ selection output,
      SelectedImportOrdinaryParses input selection output := by
  rintro ⟨selection, output, successful⟩
  unfold SelectedImportOrdinaryParses SelectedImportParses at successful
  rcases successful with
    ⟨afterSource, sourceParsed, aliasParsed, spanEq⟩
  cases rejection with
  | sourceRejected sourceRejected =>
      exact selectorNameDeterministicOutcomeSpec.successRejectDisjoint
        sourceRejected ⟨_, afterSource, sourceParsed⟩
  | aliasRejected rejectedSourceParsed aliasRejected =>
      have afterSourceEq :=
        selectorNameDeterministicOutcomeSpec.successOutputUnique
          rejectedSourceParsed sourceParsed
      subst afterSource
      exact selectedAliasDeterministicOutcomeSpec.successRejectDisjoint
        aliasRejected ⟨_, output, aliasParsed⟩

/-- Selected imports have deterministic and exclusive broad ordinary
outcomes. -/
theorem selectedImportDeterministicOutcomeSpec :
    DeterministicOutcomeSpec SelectedImportOrdinaryParses
      SelectedImportRejects where
  successOutputUnique := SelectedImportOrdinaryParses.output_unique
  successRejectDisjoint := SelectedImportRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
