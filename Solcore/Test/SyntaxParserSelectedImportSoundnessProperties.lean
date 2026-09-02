import Solcore.Syntax.Parser.SelectedAliasOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportOrdinaryOutcomeSoundnessProperties

/-! External consumers for selected-import item grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectedImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectedAliasParses
example := @SelectedAliasOrdinaryParses
example := @SelectedAliasRejects
example := @selectedAliasDeterministicOutcomeSpec
example := @SelectedImportParses
example := @SelectedImportOrdinaryParses
example := @SelectedImportRejects
example := @selectedImportDeterministicOutcomeSpec
example := @keywordAbsentAt_of_isKeyword_eq_false
example := @selectedAlias_success_sound
example := @selectedAlias_success_sound_and_validFor
example := @selectedAlias_success_ordinaryOutcome_sound
example := @selectedAlias_reject_ordinaryOutcome_sound
example := @selectedAlias_ordinaryOutcome_sound
example := @selectedAlias_ordinaryOutcomeSpec
example := @selectedImport_success_sound
example := @selectedImport_success_sound_and_validFor
example := @selectedImport_success_ordinaryOutcome_sound
example := @selectedImport_reject_ordinaryOutcome_sound
example := @selectedImport_ordinaryOutcome_sound
example := @selectedImport_ordinaryOutcomeSpec

example {input next : State} {selection : SelectedImport}
    (inputValid : input.ValidFor)
    (result : selectedImport input = .ok selection next) :
    SelectedImportParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  selectedImport_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserSelectedImportSoundnessProperties
