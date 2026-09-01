import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Functionality, rejection exclusivity, and clean embedding for ordinary raw
Core-block outcomes.
-/

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

/-- Ordinary block-item success has one final remainder. -/
theorem CoreBlockItemsParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftBody rightBody : List Syntax.Statement}
    {leftClosing rightClosing : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockItemsParses statementOrdinary input leftBody
      leftClosing afterLeft)
    (rightParsed : CoreBlockItemsParses statementOrdinary input rightBody
      rightClosing afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightBody rightClosing afterRight with
  | close leftClosing leftToken =>
      cases rightParsed with
      | close rightClosing rightToken =>
          exact exactToken_output_unique leftToken rightToken
      | next notAtEnd closingAbsent statementParsed progress tail =>
          exact False.elim (absent_conflicts_exact closingAbsent leftToken)
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      cases rightParsed with
      | close rightClosing rightToken =>
          exact False.elim (absent_conflicts_exact closingAbsent rightToken)
      | next otherNotAtEnd otherClosingAbsent otherStatementParsed
            otherProgress otherTail =>
          have afterStatementEq := outcomes.successOutputUnique statementParsed
            otherStatementParsed
          subst afterStatementEq
          exact inductionHypothesis otherTail

/-- Diagnostic-inclusive complete Core-block success has one final remainder. -/
theorem CoreBlockOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.Block}
    {afterLeft afterRight : Remainder}
    (leftParsed : CoreBlockOrdinaryParses statementOrdinary policy input left
      afterLeft)
    (rightParsed : CoreBlockOrdinaryParses statementOrdinary policy input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftClosing leftToken leftBody =>
      cases rightParsed with
      | parsed rightOpening rightClosing rightToken rightBody =>
          have afterOpeningEq := exactToken_output_unique leftToken rightToken
          subst afterOpeningEq
          exact leftBody.output_unique outcomes rightBody

/-- Ordinary block success preserves the carrier and active window whenever
ordinary statements do. -/
theorem CoreBlockOrdinaryParses.output_window
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (statementWindow : ∀ {input statement output},
      statementOrdinary input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {block : Syntax.Block}
    (parsed : CoreBlockOrdinaryParses statementOrdinary policy input block
      output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan closingSpan openingToken bodyParsed =>
      rcases openingToken with ⟨openingAt, rfl⟩
      exact bodyParsed.output_window statementWindow

/-- An exact item rejection excludes every ordinary item success. -/
theorem CoreBlockItemsRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : CoreBlockItemsRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ body closingSpan output,
      CoreBlockItemsParses statementOrdinary input body closingSpan output := by
  induction rejection with
  | missingClose closingAbsent atEnd =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next notAtEnd otherAbsent statementParsed progress tail =>
          exact (Nat.not_lt_of_ge atEnd) notAtEnd
  | statementRejected notAtEnd closingAbsent statementRejected =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherAbsent statementParsed progress tail =>
          exact outcomes.successRejectDisjoint statementRejected
            ⟨_, _, statementParsed⟩
  | laterRejected notAtEnd closingAbsent statementParsed progress tailRejected
        inductionHypothesis =>
      rintro ⟨body, closingSpan, output, parsed⟩
      cases parsed with
      | close span closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherAbsent otherStatementParsed otherProgress
            otherTail =>
          have afterStatementEq := outcomes.successOutputUnique statementParsed
            otherStatementParsed
          subst afterStatementEq
          exact inductionHypothesis ⟨_, _, _, otherTail⟩

/-- Exact complete-block rejection excludes ordinary complete-block success. -/
theorem CoreBlockRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    {policy : CoreBlockTailPolicy}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : CoreBlockRejects statementOrdinary statementRejects policy
      input rejected) :
    ¬ ∃ block output,
      CoreBlockOrdinaryParses statementOrdinary policy input block output := by
  rintro ⟨block, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed bodyParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | itemsRejected rejectedSpan rejectedOpening itemsRejected =>
      cases parsed with
      | parsed openingSpan closingSpan openingParsed bodyParsed =>
          have afterOpeningEq := exactToken_output_unique rejectedOpening
            openingParsed
          subst afterOpeningEq
          exact itemsRejected.disjointOrdinary outcomes
            ⟨_, _, _, bodyParsed⟩

/-- Raw Core-block ordinary outcomes are deterministic and exclusive. -/
theorem coreBlockDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (policy : CoreBlockTailPolicy)
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (CoreBlockOrdinaryParses statementOrdinary policy)
      (CoreBlockRejects statementOrdinary statementRejects policy) where
  successOutputUnique := CoreBlockOrdinaryParses.output_unique outcomes
  successRejectDisjoint := CoreBlockRejects.disjointOrdinary outcomes

/-- Clean block items embed when clean statement success embeds. -/
theorem CoreBlockItemsParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {body : List Syntax.Statement}
    {closingSpan : SourceSpan}
    (parsed : CoreBlockItemsParses statementClean input body closingSpan
      output) :
    CoreBlockItemsParses statementOrdinary input body closingSpan output := by
  induction parsed with
  | close span closing => exact .close span closing
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      exact .next notAtEnd closingAbsent (cleanToOrdinary statementParsed)
        progress inductionHypothesis

/-- Diagnostic-free Core-block grammar embeds into ordinary success. -/
theorem CoreBlockParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {policy : CoreBlockTailPolicy} {input output : Remainder}
    {block : Syntax.Block}
    (parsed : CoreBlockParses statementClean policy input block output) :
    CoreBlockOrdinaryParses statementOrdinary policy input block output := by
  cases parsed with
  | parsed openingSpan closingSpan openingParsed bodyParsed tailsValid =>
      exact .parsed openingSpan closingSpan openingParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
