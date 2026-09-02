import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-! Exact rejection-endpoint functionality for generic delimited lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex index : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex index kind)
    (present : TokenAt tokens endIndex index { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- A delimited-tail rejection has one exact failing endpoint whenever the
nested production has exact ordinary outcomes. -/
theorem DelimitedTailRejects.output_unique {alpha : Type}
    {closing : Symbol} {allowTrailing : Bool}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : DelimitedTailRejects closing allowTrailing
      ordinaryParses nestedRejects input left)
    (rightRejects : DelimitedTailRejects closing allowTrailing
      ordinaryParses nestedRejects input right) : left = right := by
  induction leftRejects generalizing right with
  | delimiterMissing leftCommaAbsent leftClosingAbsent =>
      cases rightRejects with
      | delimiterMissing => rfl
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightComma)
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_token leftCommaAbsent rightComma)
  | elementRejected leftCommaSpan leftComma leftContinues
        leftNestedRejects =>
      cases rightRejects with
      | delimiterMissing rightCommaAbsent rightClosingAbsent =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftComma)
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact outcomes.rejectOutputUnique leftNestedRejects
            rightNestedRejects
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          exact False.elim
            (outcomes.successRejectDisjoint leftNestedRejects
              ⟨_, _, rightElement⟩)
  | laterRejected leftCommaSpan leftComma leftContinues leftElement
        leftProgress leftTail inductionHypothesis =>
      cases rightRejects with
      | delimiterMissing rightCommaAbsent rightClosingAbsent =>
          exact False.elim
            (absent_conflicts_token rightCommaAbsent leftComma)
      | elementRejected rightCommaSpan rightComma rightContinues
            rightNestedRejects =>
          exact False.elim
            (outcomes.successRejectDisjoint rightNestedRejects
              ⟨_, _, leftElement⟩)
      | laterRejected rightCommaSpan rightComma rightContinues
            rightElement rightProgress rightTail =>
          have afterElementEq :=
            outcomes.successOutputUnique leftElement rightElement
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- A complete delimited-list rejection has one exact failing endpoint
whenever the nested production has exact ordinary outcomes. -/
theorem DelimitedListRejects.output_unique {alpha : Type}
    {opening closing : Symbol} {allowEmpty allowTrailing : Bool}
    {ordinaryParses : Remainder → alpha → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input left right : Remainder}
    (leftRejects : DelimitedListRejects opening closing allowEmpty
      allowTrailing ordinaryParses nestedRejects input left)
    (rightRejects : DelimitedListRejects opening closing allowEmpty
      allowTrailing ordinaryParses nestedRejects input right) : left = right :=
  by
    cases leftRejects with
    | openingMissing leftOpeningAbsent =>
        cases rightRejects with
        | openingMissing => rfl
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening)
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            exact False.elim
              (absent_conflicts_token leftOpeningAbsent rightOpening)
    | firstRejected leftOpeningSpan leftOpening leftContinues
          leftNestedRejects =>
        cases rightRejects with
        | openingMissing rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening)
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact outcomes.rejectOutputUnique leftNestedRejects
              rightNestedRejects
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            exact False.elim
              (outcomes.successRejectDisjoint leftNestedRejects
                ⟨_, _, rightFirst⟩)
    | tailRejected leftOpeningSpan leftOpening leftContinues leftFirst
          leftProgress leftTail =>
        cases rightRejects with
        | openingMissing rightOpeningAbsent =>
            exact False.elim
              (absent_conflicts_token rightOpeningAbsent leftOpening)
        | firstRejected rightOpeningSpan rightOpening rightContinues
              rightNestedRejects =>
            exact False.elim
              (outcomes.successRejectDisjoint rightNestedRejects
                ⟨_, _, leftFirst⟩)
        | tailRejected rightOpeningSpan rightOpening rightContinues
              rightFirst rightProgress rightTail =>
            have afterFirstEq :=
              outcomes.successOutputUnique leftFirst rightFirst
            subst afterFirstEq
            exact leftTail.output_unique outcomes rightTail

end Solcore.Syntax.DeclarativeGrammar
