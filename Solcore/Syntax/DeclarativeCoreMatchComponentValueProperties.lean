import Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
import Solcore.Syntax.DeclarativeCoreMatchCaseOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchDefaultOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchScrutineeListOutcomeProperties
import Solcore.Syntax.DeclarativeCoreMatchScrutineesOutcomeProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingExactnessProperties

/-! Exact success values for Core match scrutinees, cases, and default bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact expressions fix a required trailing-comma scrutinee list and its
remainder, including the list's retained delimiter span. -/
theorem MatchScrutineeListOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight :=
  (nonemptyTrailingDelimitedListExactOutcomeSpec .leftParen .rightParen
    expressionOutcomes).successResultUnique leftParsed rightParsed

/-- A match scrutinee list fixes its complete forward AST value. -/
theorem MatchScrutineeListOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : DelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : MatchScrutineeListOrdinaryParses expressionOrdinary input
      right afterRight) : left = right :=
  (MatchScrutineeListOrdinaryParses.result_unique expressionOutcomes
    leftParsed rightParsed).1

/-- Converting the same parsed list fixes the nonempty carrier and remainder. -/
theorem RequireScrutineesOrdinaryParses.result_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed
  cases rightParsed
  exact ⟨rfl, rfl⟩

/-- Nonempty conversion fixes exactly the supplied scrutinee list value. -/
theorem RequireScrutineesOrdinaryParses.value_unique
    {values : DelimitedList Syntax.Expr} {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : RequireScrutineesOrdinaryParses values input left afterLeft)
    (rightParsed : RequireScrutineesOrdinaryParses values input right
      afterRight) : left = right :=
  (RequireScrutineesOrdinaryParses.result_unique leftParsed rightParsed).1

/-- Exact recursive statement and pattern outcomes fix a match case's AST,
covering source span, and final remainder. -/
theorem MatchCaseOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftPattern leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightPattern rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨markerEq, inputEq⟩
          subst markerEq
          subst inputEq
          rcases patternOutcomes.successResultUnique leftPattern rightPattern
            with ⟨patternEq, inputEq⟩
          subst patternEq
          subst inputEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          subst bodyEq
          exact ⟨rfl, outputEq⟩

/-- A successful match case fixes its full pattern-and-body AST. -/
theorem MatchCaseOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop}
    {patternRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (patternOutcomes : ExactDeterministicOutcomeSpec patternOrdinary
      patternRejects)
    {input : Remainder} {left right : Syntax.MatchCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input left afterLeft)
    (rightParsed : MatchCaseOrdinaryParses statementOrdinary patternOrdinary
      input right afterRight) : left = right :=
  (MatchCaseOrdinaryParses.result_unique statementOutcomes patternOutcomes
    leftParsed rightParsed).1

/-- Default-token priority and exact recursive statements fix an optional
default body's value and remainder. -/
theorem OptionalDefaultBodyOrdinaryParses.result_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl⟩
      | present rightSpan rightMarker rightBody =>
          exact False.elim (leftAbsent ⟨rightSpan, rightMarker.1⟩)
  | present leftSpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (rightAbsent ⟨leftSpan, leftMarker.1⟩)
      | present rightSpan rightMarker rightBody =>
          have inputEq := leftMarker.output_unique rightMarker
          subst inputEq
          rcases leftBody.result_unique statementOutcomes rightBody with
            ⟨bodyEq, outputEq⟩
          exact ⟨congrArg some bodyEq, outputEq⟩

/-- A prioritized optional default body fixes its exact optional AST. -/
theorem OptionalDefaultBodyOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Option Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : OptionalDefaultBodyOrdinaryParses statementOrdinary input
      right afterRight) : left = right :=
  (OptionalDefaultBodyOrdinaryParses.result_unique statementOutcomes
    leftParsed rightParsed).1

end Solcore.Syntax.DeclarativeGrammar
