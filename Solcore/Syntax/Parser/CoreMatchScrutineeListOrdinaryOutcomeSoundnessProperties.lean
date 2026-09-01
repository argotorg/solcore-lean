import Solcore.Syntax.DeclarativeCoreMatchScrutineeListOutcomeProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedSoundnessProperties

/-!
Executable ordinary outcomes for the parenthesized Core match scrutinee list.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/-- Every executable scrutinee-list success follows the exact nonempty,
allow-trailing grammar and retains its active token window. -/
theorem matchScrutineeList_success_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression)
    {input output : State} {values : DelimitedList Expr}
    (result : delimited .leftParen .rightParen false expression .expression
      .statement input = .ok values output) :
    DeclarativeGrammar.MatchScrutineeListOrdinaryParses expressionOrdinary
      input.declarativeRemainder values output.declarativeRemainder :=
  delimited_nonempty_trailing_success_sound .leftParen .rightParen expression
    expressionOrdinary .expression .statement expressionSuccessSound
      expressionWindow result

/-- Every executable scrutinee-list rejection records the exact first failing
stage with required-nonempty and allow-trailing priorities. -/
theorem matchScrutineeList_reject_ordinary_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : delimited .leftParen .rightParen false expression .expression
      .statement input = .reject failure rejected) :
    DeclarativeGrammar.MatchScrutineeListRejects expressionOrdinary
      expressionRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  delimited_reject_sound .leftParen .rightParen false expression
    expressionOrdinary expressionRejects .expression .statement
      expressionSuccessSound expressionRejectSound result

/-- Package executable success and rejection for the Core match scrutinee
list. -/
theorem matchScrutineeList_ordinaryOutcome_sound
    (expression : Parser Expr)
    (expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSuccessSound : ∀ {input output : State} {value : Expr},
      expression input = .ok value output → expressionOrdinary
        input.declarativeRemainder value output.declarativeRemainder)
    (expressionRejectSound : ∀ {input rejected : State} {failure : Failure},
      expression input = .reject failure rejected → expressionRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (expressionWindow : Parser.PreservesTokenWindow expression) :
    (∀ {input output : State} {values : DelimitedList Expr},
      delimited .leftParen .rightParen false expression .expression
          .statement input = .ok values output →
        DeclarativeGrammar.MatchScrutineeListOrdinaryParses
          expressionOrdinary input.declarativeRemainder values
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      delimited .leftParen .rightParen false expression .expression
          .statement input = .reject failure rejected →
        DeclarativeGrammar.MatchScrutineeListRejects expressionOrdinary
          expressionRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨matchScrutineeList_success_ordinary_sound expression expressionOrdinary
      expressionSuccessSound expressionWindow,
    matchScrutineeList_reject_ordinary_sound expression expressionOrdinary
      expressionRejects expressionSuccessSound expressionRejectSound⟩

/-- Re-export deterministic Core match scrutinee-list outcomes. -/
theorem matchScrutineeList_ordinaryOutcomeSpec
    {expressionOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {expressionRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (expressionOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      expressionOrdinary expressionRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.MatchScrutineeListOrdinaryParses
        expressionOrdinary)
      (DeclarativeGrammar.MatchScrutineeListRejects expressionOrdinary
        expressionRejects) :=
  DeclarativeGrammar.matchScrutineeListDeterministicOutcomeSpec
    expressionOutcomes

end Solcore.Syntax.Parser.MatchInternals
