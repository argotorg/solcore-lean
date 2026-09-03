import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.Parser.FileItemsTotalityProperties
import Solcore.Syntax.Parser.SyntaxExactnessProperties

/-! Complete ordinary file-item grammar correspondence at sufficient fuel.
The fixed reverse accumulator stays outside the declarative grammar. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- At sufficient fuel, grammar success for a fresh suffix is exactly loop
execution returning the fixed accumulated prefix followed by that suffix. -/
theorem parseItems_ordinary_success_iff_of_remainingCount_lt
    (fuel : Nat) (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, parseItems fuel itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder := by
  constructor
  · intro parsed
    rcases parseItems_exists_ok_of_remainingCount_lt
        productionParseItemsItemInvariantFree fuel itemsRev input inputValid
          adequate with ⟨items, output, result⟩
    rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        items output result with ⟨actual, itemsEq, actualParsed⟩
    rcases parseItems_exactOutcomeSpec.successResultUnique actualParsed parsed with
      ⟨suffixEq, remainderEq⟩
    refine ⟨output, ?_, remainderEq⟩
    simpa only [itemsEq, suffixEq] using result
  · rintro ⟨output, result, remainderEq⟩
    rcases parseItems_success_ordinaryOutcome_sound_strong fuel itemsRev input
        (itemsRev.reverse ++ suffix) output result with
      ⟨actual, itemsEq, actualParsed⟩
    have suffixEq : suffix = actual := List.append_cancel_left itemsEq
    cases suffixEq
    exact remainderEq ▸ actualParsed

/-- The production fuel discharges adequacy while retaining the exact
forward prefix and fresh suffix in the executable result. -/
theorem parseItems_production_ordinary_success_iff (itemsRev : List TopItem)
    {input : State} (inputValid : input.ValidFor)
    {suffix : List TopItem} {remainder : DeclarativeGrammar.Remainder} :
    DeclarativeGrammar.FileItemsOrdinaryParses
      input.declarativeRemainder suffix remainder ↔
      ∃ output, parseItems (input.remainingCount + 1) itemsRev input =
        .ok (itemsRev.reverse ++ suffix) output ∧
        output.declarativeRemainder = remainder :=
  parseItems_ordinary_success_iff_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev inputValid (by omega)

end Solcore.Syntax.Parser.FileInternals
