import Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
import Solcore.Syntax.Parser.HidingClauseSoundnessProperties

/-! Broad ordinary-success soundness for required and optional hiding clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable required hiding success follows the exact marker and
nonempty allow-trailing selector-list grammar. -/
theorem hidingClause_success_ordinaryOutcome_sound
    {input output : State} {clause : HidingClause}
    (result : ImportInternals.hidingClause input = .ok clause output) :
    DeclarativeGrammar.HidingClauseOrdinaryParses
      input.declarativeRemainder clause output.declarativeRemainder :=
  hidingClause_success_sound result

/-- Every executable optional hiding success follows its exact guarded
present-or-nonconsuming-absent grammar. -/
theorem optionalHiding_success_ordinaryOutcome_sound
    {input output : State} {hidden : Option HidingClause}
    (result : ImportInternals.optionalHiding input = .ok hidden output) :
    DeclarativeGrammar.OptionalHidingOrdinaryParses
      input.declarativeRemainder hidden output.declarativeRemainder :=
  optionalHiding_success_sound result

end Solcore.Syntax.Parser
