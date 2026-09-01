import Solcore.Syntax.Parser.FileItemsSoundnessProperties

/-! External consumers for generic complete-file item-loop soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFileItemsSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @TopItemsParses
example := @TopItemsParses.output_atEnd
example := @parseItems_success_sound_of_diagnosticFree

example
    (itemParses : Remainder → TopItem → Remainder → Prop)
    (itemSound : ∀ {input next : State} {item : TopItem},
      next.diagnosticsRev = [] →
      parseItemsItem input = .ok item next →
      itemParses input.declarativeRemainder item next.declarativeRemainder)
    (itemReflectsDiagnosticFree : ∀ {input next : State} {item : TopItem},
      parseItemsItem input = .ok item next →
      next.diagnosticsRev = [] → input.diagnosticsRev = [])
    {fuel : Nat} {itemsRev : List TopItem} {input next : State}
    {items : List TopItem} (diagnosticFree : next.diagnosticsRev = [])
    (parsed : parseItems fuel itemsRev input = .ok items next) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      TopItemsParses itemParses input.declarativeRemainder suffix
        next.declarativeRemainder :=
  parseItems_success_sound_of_diagnosticFree itemParses itemSound
    itemReflectsDiagnosticFree diagnosticFree parsed

end Solcore.Test.SyntaxParserFileItemsSoundnessProperties
