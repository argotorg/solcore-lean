import Solcore.Syntax.Parser.LocalExportItemOrdinaryOutcomeSoundnessProperties

/-! External consumers for local export-item grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLocalExportItemSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @IdentifierDotAbsentAt
example := @LocalExportItemParses
example := @LocalExportItemQualifiedStartAt
example := @LocalExportItemOrdinaryParses
example := @LocalExportItemRejects
example := @localExportItemDeterministicOutcomeSpec
example := @localExportItem_success_sound
example := @localExportItem_success_sound_and_validFor
example := @localExportItem_success_ordinaryOutcome_sound
example := @localExportItem_reject_ordinaryOutcome_sound
example := @localExportItem_ordinaryOutcome_sound
example := @localExportItem_ordinaryOutcomeSpec

example {input next : State} {item : LocalExportItem}
    (inputValid : input.ValidFor)
    (result : ExportInternals.localExportItem input = .ok item next) :
    LocalExportItemParses input.declarativeRemainder item
        next.declarativeRemainder ∧
      item.ValidFor input.file :=
  localExportItem_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserLocalExportItemSoundnessProperties
