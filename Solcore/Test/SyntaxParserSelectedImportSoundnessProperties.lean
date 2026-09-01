import Solcore.Syntax.Parser.SelectedImportSoundnessProperties

/-! External consumers for selected-import item grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectedImportSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectedAliasParses
example := @SelectedImportParses
example := @keywordAbsentAt_of_isKeyword_eq_false
example := @selectedAlias_success_sound
example := @selectedAlias_success_sound_and_validFor
example := @selectedImport_success_sound
example := @selectedImport_success_sound_and_validFor

example {input next : State} {selection : SelectedImport}
    (inputValid : input.ValidFor)
    (result : selectedImport input = .ok selection next) :
    SelectedImportParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  selectedImport_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserSelectedImportSoundnessProperties
