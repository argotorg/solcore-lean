import Solcore.Syntax.Parser.ExportSelectionOrdinaryOutcomeSoundnessProperties

/-! External consumers for remote export-selection grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportSelectionSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ExportSelectionParses
example := @ExportSelectionOrdinaryParses
example := @ExportSelectionRejects
example := @exportSelectionDeterministicOutcomeSpec
example := @exportSelection_success_sound
example := @exportSelection_success_sound_and_validFor
example := @exportSelection_success_ordinaryOutcome_sound
example := @exportSelection_reject_ordinaryOutcome_sound
example := @exportSelection_ordinaryOutcome_sound
example := @exportSelection_ordinaryOutcomeSpec

example {input next : State} {selection : ExportSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.exportSelection input = .ok selection next) :
    ExportSelectionParses input.declarativeRemainder selection
        next.declarativeRemainder ∧
      selection.ValidFor input.file :=
  exportSelection_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserExportSelectionSoundnessProperties
