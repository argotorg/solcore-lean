import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeYulBlockOutcomeGrammar

/-!
Functionality, rejection exclusivity, and clean embedding for ordinary
inline-Yul block outcomes.
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

private theorem exactToken_span_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftSpan = rightSpan := by
  have tokenEq :
      ({ span := leftSpan, value := kind } : Token) =
        { span := rightSpan, value := kind } :=
    Option.some.inj (leftParsed.1.2.symm.trans rightParsed.1.2)
  exact congrArg (fun token : Token => token.span) tokenEq

/-- Ordinary block-item success has a unique final remainder whenever one
ordinary statement has a unique final remainder. -/
theorem YulBlockItemsParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {openingSpan : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockItemsParses statementOrdinary openingSpan input
      leftSpan leftBody afterLeft)
    (rightParsed : YulBlockItemsParses statementOrdinary openingSpan input
      rightSpan rightBody afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightSpan rightBody afterRight with
  | close leftClosingSpan leftClosingParsed =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact exactToken_output_unique leftClosingParsed rightClosingParsed
      | next rightNotAtEnd rightClosingAbsent rightStatementParsed
            rightProgress rightTail =>
          exact False.elim
            (absent_conflicts_exact rightClosingAbsent leftClosingParsed)
  | next leftNotAtEnd leftClosingAbsent leftStatementParsed leftProgress
        leftTail inductionHypothesis =>
      cases rightParsed with
      | close rightClosingSpan rightClosingParsed =>
          exact False.elim
            (absent_conflicts_exact leftClosingAbsent rightClosingParsed)
      | next rightNotAtEnd rightClosingAbsent rightStatementParsed
            rightProgress rightTail =>
          have afterStatementEq := outcomes.successOutputUnique
            leftStatementParsed rightStatementParsed
          subst afterStatementEq
          exact inductionHypothesis rightTail

/-- Ordinary complete block success has a unique final remainder. -/
theorem YulBlockParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockOrdinaryParses statementOrdinary input leftSpan
      leftBody afterLeft)
    (rightParsed : YulBlockOrdinaryParses statementOrdinary input rightSpan
      rightBody afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpeningSpan leftOpeningParsed leftItemsParsed =>
      cases rightParsed with
      | parsed rightOpeningSpan rightOpeningParsed rightItemsParsed =>
          have openingSpanEq := exactToken_span_unique leftOpeningParsed
            rightOpeningParsed
          subst openingSpanEq
          have afterOpeningEq := exactToken_output_unique leftOpeningParsed
            rightOpeningParsed
          subst afterOpeningEq
          exact leftItemsParsed.output_unique outcomes rightItemsParsed

/-- An exact block-item rejection excludes every ordinary block-item
success from the same remainder. -/
theorem YulBlockItemsRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockItemsRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ openingSpan bodySpan body output,
      YulBlockItemsParses statementOrdinary openingSpan input bodySpan body
        output := by
  induction rejection with
  | missingClose closingAbsent atEnd =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next notAtEnd otherClosingAbsent statementParsed progress tail =>
          exact (Nat.not_lt_of_ge atEnd) notAtEnd
  | statementRejected notAtEnd closingAbsent rejectedStatement =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherClosingAbsent statementParsed progress tail =>
          exact outcomes.successRejectDisjoint rejectedStatement
            ⟨_, _, statementParsed⟩
  | laterRejected notAtEnd closingAbsent rejectedStatementParsed progress
        tailRejected inductionHypothesis =>
      rintro ⟨openingSpan, bodySpan, body, output, parsed⟩
      cases parsed with
      | close closingSpan closingParsed =>
          exact absent_conflicts_exact closingAbsent closingParsed
      | next otherNotAtEnd otherClosingAbsent successfulStatementParsed
            otherProgress successfulTail =>
          have afterStatementEq := outcomes.successOutputUnique
            rejectedStatementParsed successfulStatementParsed
          subst afterStatementEq
          exact inductionHypothesis ⟨_, _, _, _, successfulTail⟩

/-- Exact complete-block rejection excludes ordinary complete-block success. -/
theorem YulBlockRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulBlockRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ bodySpan body output,
      YulBlockOrdinaryParses statementOrdinary input bodySpan body output := by
  rintro ⟨bodySpan, body, output, parsed⟩
  cases rejection with
  | openingMissing openingAbsent =>
      cases parsed with
      | parsed openingSpan openingParsed itemsParsed =>
          exact absent_conflicts_exact openingAbsent openingParsed
  | itemsRejected rejectedOpeningSpan rejectedOpeningParsed itemsRejected =>
      cases parsed with
      | parsed openingSpan openingParsed itemsParsed =>
          have afterOpeningEq := exactToken_output_unique
            rejectedOpeningParsed openingParsed
          subst afterOpeningEq
          exact itemsRejected.disjointOrdinary outcomes
            ⟨_, _, _, _, itemsParsed⟩

/-- Ordinary block success and exact block rejection form a deterministic
outcome contract. -/
theorem yulBlockDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulBlockOutcomeParses statementOrdinary)
      (YulBlockRejects statementOrdinary statementRejects) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique outcomes rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨block, output, parsed⟩
    exact rejection.disjointOrdinary outcomes
      ⟨block.span, block.body, output, parsed⟩

/-- A clean block-item derivation embeds into an ordinary derivation when
each clean statement embeds into the supplied ordinary statement relation. -/
theorem YulBlockItemsParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementClean openingSpan input bodySpan
      body output) :
    YulBlockItemsParses statementOrdinary openingSpan input bodySpan body
      output := by
  induction parsed with
  | close closingSpan closingParsed => exact .close closingSpan closingParsed
  | next notAtEnd closingAbsent statementParsed progress tail
        inductionHypothesis =>
      exact .next notAtEnd closingAbsent (cleanToOrdinary statementParsed)
        progress inductionHypothesis

/-- A clean complete block derivation embeds into the corresponding ordinary
block derivation without changing its span, body, or remainder. -/
theorem YulBlockParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementClean input bodySpan body output) :
    YulBlockOrdinaryParses statementOrdinary input bodySpan body output := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      exact .parsed openingSpan openingParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
