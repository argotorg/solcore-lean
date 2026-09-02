import Solcore.Syntax.DeclarativeHidingClauseOutcomeProperties
import Solcore.Syntax.Parser.HidingClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.HidingClauseOrdinarySuccessSoundnessProperties

/-! Complete executable broad ordinary outcomes for required and optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package required hiding-clause success and exact sequential rejection. -/
theorem hidingClause_ordinaryOutcome_sound :
    (∀ {input output : State} {clause : HidingClause},
      ImportInternals.hidingClause input = .ok clause output →
        DeclarativeGrammar.HidingClauseOrdinaryParses
          input.declarativeRemainder clause output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.hidingClause input = .reject failure rejected →
        DeclarativeGrammar.HidingClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨hidingClause_success_ordinaryOutcome_sound,
    hidingClause_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive required hiding outcomes. -/
theorem hidingClause_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.HidingClauseOrdinaryParses
      DeclarativeGrammar.HidingClauseRejects :=
  DeclarativeGrammar.hidingClauseDeterministicOutcomeSpec

/-- Package guarded optional hiding success and exact committed rejection. -/
theorem optionalHiding_ordinaryOutcome_sound :
    (∀ {input output : State} {hidden : Option HidingClause},
      ImportInternals.optionalHiding input = .ok hidden output →
        DeclarativeGrammar.OptionalHidingOrdinaryParses
          input.declarativeRemainder hidden output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.optionalHiding input = .reject failure rejected →
        DeclarativeGrammar.OptionalHidingRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨optionalHiding_success_ordinaryOutcome_sound,
    optionalHiding_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive optional hiding outcomes. -/
theorem optionalHiding_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalHidingOrdinaryParses
      DeclarativeGrammar.OptionalHidingRejects :=
  DeclarativeGrammar.optionalHidingDeterministicOutcomeSpec

end Solcore.Syntax.Parser
