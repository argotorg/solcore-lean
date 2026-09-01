import Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar

/-! Determinism and rejection exclusion for the parenthesized tuple tail. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Every successful tuple tail starts with the selected comma. -/
theorem ParenthesizedTupleTailParses.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {input output : Remainder} {elements : List Syntax.Expr}
    {closingSpan : SourceSpan}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (parsed : ParenthesizedTupleTailParses nestedOrdinary input elements
      closingSpan output) : False := by
  cases parsed with
  | trailing commaSpan closingSpan commaParsed closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | final commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress laterCommaAbsent closingParsed =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | next commaSpan closingSpan commaParsed closingAbsent elementParsed
        progress tail =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- Every rejected tuple tail likewise starts with the selected comma. -/
theorem ParenthesizedTupleTailRejects.comma_conflicts_absent
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {input rejected : Remainder}
    (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .comma))
    (rejection : ParenthesizedTupleTailRejects nestedOrdinary nestedRejects
      input rejected) : False := by
  cases rejection with
  | elementRejected commaSpan commaParsed closingAbsent elementRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | closingMissing commaSpan commaParsed closingAbsentAfterComma
        elementParsed progress laterCommaAbsent closingAbsent =>
      exact absent_conflicts_exact commaAbsent commaParsed
  | laterRejected commaSpan commaParsed closingAbsent elementParsed progress
        tailRejected =>
      exact absent_conflicts_exact commaAbsent commaParsed

/-- A successful maximal tuple tail has a unique output remainder whenever a
nested ordinary expression does. -/
theorem ParenthesizedTupleTailParses.output_unique
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    (nestedOutputUnique : ∀ {input : Remainder}
      {left right : Syntax.Expr} {afterLeft afterRight : Remainder},
      nestedOrdinary input left afterLeft →
      nestedOrdinary input right afterRight → afterLeft = afterRight) :
    ∀ {input : Remainder} {left right : List Syntax.Expr}
      {leftClosing rightClosing : SourceSpan}
      {afterLeft afterRight : Remainder},
      ParenthesizedTupleTailParses nestedOrdinary input left leftClosing
          afterLeft →
      ParenthesizedTupleTailParses nestedOrdinary input right rightClosing
          afterRight →
      afterLeft = afterRight := by
  intro input left right leftClosing rightClosing afterLeft afterRight
    leftParsed
  induction leftParsed generalizing right rightClosing afterRight with
  | trailing leftCommaSpan leftClosingSpan leftComma leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact exactToken_output_unique leftClosing rightClosing
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosing)
  | final leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftCommaAbsent leftClosing =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact exactToken_output_unique leftClosing rightClosing
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (rightTail.comma_conflicts_absent leftCommaAbsent)
  | next leftCommaSpan leftClosingSpan leftComma leftClosingAbsent
        leftElement leftProgress leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | trailing rightCommaSpan rightClosingSpan rightComma rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosing)
      | final rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightCommaAbsent rightClosing =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact False.elim
            (leftTail.comma_conflicts_absent rightCommaAbsent)
      | next rightCommaSpan rightClosingSpan rightComma rightClosingAbsent
            rightElement rightProgress rightTail =>
          have afterCommaEq := exactToken_output_unique leftComma rightComma
          subst afterCommaEq
          have afterElementEq := nestedOutputUnique leftElement rightElement
          subst afterElementEq
          exact inductionHypothesis rightTail

/-- Exact tuple-tail rejection excludes every successful tuple tail. -/
theorem ParenthesizedTupleTailRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    {input rejected : Remainder}
    (rejection : ParenthesizedTupleTailRejects nestedOrdinary nestedRejects
      input rejected) :
    ¬ ∃ elements closingSpan output,
      ParenthesizedTupleTailParses nestedOrdinary input elements closingSpan
        output := by
  induction rejection with
  | elementRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact nestedOutcomes.successRejectDisjoint rejectedElement
            ⟨_, _, successfulElement⟩
  | closingMissing rejectedCommaSpan rejectedComma
        rejectedClosingAbsentAfterComma rejectedElement rejectedProgress
        rejectedCommaAbsent rejectedClosingAbsent =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsentAfterComma
            successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact successfulTail.comma_conflicts_absent rejectedCommaAbsent
  | laterRejected rejectedCommaSpan rejectedComma rejectedClosingAbsent
        rejectedElement rejectedProgress rejectedTail inductionHypothesis =>
      rintro ⟨elements, closingSpan, output, parsed⟩
      cases parsed with
      | trailing successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          exact absent_conflicts_exact rejectedClosingAbsent successfulClosing
      | final successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulCommaAbsent successfulClosing =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact rejectedTail.comma_conflicts_absent successfulCommaAbsent
      | next successfulCommaSpan successfulClosingSpan successfulComma
            successfulClosingAbsent successfulElement successfulProgress
            successfulTail =>
          have afterCommaEq := exactToken_output_unique rejectedComma
            successfulComma
          subst afterCommaEq
          have afterElementEq := nestedOutcomes.successOutputUnique
            rejectedElement successfulElement
          subst afterElementEq
          exact inductionHypothesis ⟨_, _, _, successfulTail⟩

end Solcore.Syntax.DeclarativeGrammar
