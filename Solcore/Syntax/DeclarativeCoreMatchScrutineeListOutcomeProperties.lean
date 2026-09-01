import Solcore.Syntax.DeclarativeDelimitedNonemptyTrailingOutcomeProperties

/-!
Diagnostic-inclusive deterministic outcomes for the parenthesized,
nonempty, trailing-comma Core match scrutinee list.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of the exact Core match scrutinee list parser. -/
abbrev MatchScrutineeListOrdinaryParses
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop) :=
  NonemptyTrailingDelimitedListParses .leftParen .rightParen
    expressionOrdinary

/-- Exact rejection of the required, allow-trailing scrutinee list. -/
abbrev MatchScrutineeListRejects
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop) :=
  DelimitedListRejects .leftParen .rightParen false true
    expressionOrdinary expressionRejects

/-- Ordinary Core match scrutinee-list success has one final remainder. -/
theorem MatchScrutineeListOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight :=
  NonemptyTrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := expressionOrdinary)
    expressionOutcomes.successOutputUnique leftParsed rightParsed

/-- Exact scrutinee-list rejection excludes ordinary success. -/
theorem MatchScrutineeListRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : MatchScrutineeListRejects expressionOrdinary
      expressionRejects input rejected) :
    ¬ ∃ values output,
      MatchScrutineeListOrdinaryParses expressionOrdinary input values
        output :=
  rejection.disjointNonemptyTrailing expressionOutcomes
    (fun parsed => parsed)

/-- Lift expression outcomes through the Core match scrutinee list. -/
theorem matchScrutineeListDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (MatchScrutineeListOrdinaryParses expressionOrdinary)
      (MatchScrutineeListRejects expressionOrdinary expressionRejects) where
  successOutputUnique := MatchScrutineeListOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := MatchScrutineeListRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
