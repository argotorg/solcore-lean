import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties

/-!
Deterministic ordinary outcomes for possibly empty comma-separated lists that
allow a trailing comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Construct the deterministic outcome contract for an allow-empty,
allow-trailing delimited list. -/
theorem trailingDelimitedListDeterministicOutcomeSpec {alpha : Type}
    (opening closing : Symbol)
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec ordinaryParses nestedRejects) :
    DeterministicOutcomeSpec
      (TrailingDelimitedListParses opening closing ordinaryParses)
      (DelimitedListRejects opening closing true true ordinaryParses
        nestedRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact TrailingDelimitedListParses.output_unique
      (opening := opening) (closing := closing)
      (elementParses := ordinaryParses) outcomes.successOutputUnique leftParsed
      rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    exact rejection.disjointAllowEmptyTrailing outcomes (fun parsed => parsed)

end Solcore.Syntax.DeclarativeGrammar
