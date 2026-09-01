import Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties

/-! Deterministic ordinary outcomes for guarded Core array literals. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary array-literal success has the unique output of its exact
allow-empty, no-trailing element list. -/
theorem ArrayLiteralExpressionOrdinaryParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input : Remainder} {left right : Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      left afterLeft)
    (rightParsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftValues =>
      cases rightParsed with
      | parsed rightValues =>
          exact NoTrailingDelimitedListParses.output_unique
            (opening := .leftBracket) (closing := .rightBracket)
            (elementParses := nestedOrdinary)
            nestedOutcomes.successOutputUnique leftValues rightValues

/-- A selected array-literal rejection excludes every ordinary array
success. -/
theorem ArrayLiteralExpressionRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ArrayLiteralExpressionRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ expression output,
      ArrayLiteralExpressionOrdinaryParses nestedOrdinary input expression
        output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | present openingSpan openingToken valuesRejected =>
      cases successful with
      | parsed valuesParsed =>
          exact valuesRejected.disjointAllowEmptyNoTrailing nestedOutcomes
            ⟨_, _, valuesParsed⟩

/-- Lift deterministic nested expression outcomes to the guarded array
literal branch. -/
theorem arrayLiteralExpressionDeterministicOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    DeterministicOutcomeSpec
      (ArrayLiteralExpressionOrdinaryParses nestedOrdinary)
      (ArrayLiteralExpressionRejects nestedOrdinary nestedRejects) where
  successOutputUnique :=
    ArrayLiteralExpressionOrdinaryParses.output_unique nestedOutcomes
  successRejectDisjoint :=
    ArrayLiteralExpressionRejects.disjointOrdinary nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
