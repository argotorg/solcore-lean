import Solcore.Syntax.Parser.SelectedImportsSoundnessProperties

/-! External consumers for selected-import list grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserSelectedImportsSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @SelectedImportsParses
example := @requireSelected_success_shape
example := @selectedImports_success_sound
example := @selectedImports_success_sound_and_validFor

example {input next : State}
    {selection : NonemptyDelimitedList SelectedImport}
    (inputValid : input.ValidFor)
    (result : ImportInternals.selectedImports input = .ok selection next) :
    SelectedImportsParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor SelectedImport.ValidFor input.file
        selection :=
  selectedImports_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserSelectedImportsSoundnessProperties
