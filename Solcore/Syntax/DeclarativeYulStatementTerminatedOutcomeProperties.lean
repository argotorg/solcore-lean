import Solcore.Syntax.DeclarativeCoreYulStatementBasicGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for a Yul statement core followed by its
maximal optional semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of a core statement followed by its optional semicolon. -/
abbrev YulStatementTerminatedOrdinaryParses
    (coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulStatementTerminatedParses coreOrdinary

/-- Optional semicolon parsing cannot reject, so a terminated attempt rejects
exactly where its core attempt rejects. -/
abbrev YulStatementTerminatedRejects
    (coreRejects : Remainder → Remainder → Prop) :=
  coreRejects

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Maximal optional-semicolon parsing has one output remainder. -/
theorem OptionalYulSemicolonParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulSemicolonParses input left afterLeft)
    (rightParsed : OptionalYulSemicolonParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
  | present leftSpan leftToken =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken =>
          rw [leftToken.2, rightToken.2]

/-- Optional termination preserves functional output of the core relation. -/
theorem YulStatementTerminatedOrdinaryParses.output_unique
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input
      left afterLeft)
    (rightParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input
      right afterRight) :
    afterLeft = afterRight := by
  rcases leftParsed with ⟨leftCore, leftCoreParsed, leftSemicolon⟩
  rcases rightParsed with ⟨rightCore, rightCoreParsed, rightSemicolon⟩
  have coreEq := outcomes.successOutputUnique leftCoreParsed rightCoreParsed
  subst rightCore
  exact leftSemicolon.output_unique rightSemicolon

/-- Core rejection excludes every optionally terminated ordinary success. -/
theorem YulStatementTerminatedRejects.disjointOrdinary
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects)
    {input rejected : Remainder}
    (rejection : YulStatementTerminatedRejects coreRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementTerminatedOrdinaryParses coreOrdinary input statement
        output := by
  rintro ⟨statement, output, afterCore, coreParsed, semicolonParsed⟩
  exact outcomes.successRejectDisjoint rejection
    ⟨statement, afterCore, coreParsed⟩

/-- Construct the deterministic outcome contract for optional termination. -/
theorem yulStatementTerminatedDeterministicOutcomeSpec
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec coreOrdinary coreRejects) :
    DeterministicOutcomeSpec
      (YulStatementTerminatedOrdinaryParses coreOrdinary)
      (YulStatementTerminatedRejects coreRejects) where
  successOutputUnique :=
    YulStatementTerminatedOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulStatementTerminatedRejects.disjointOrdinary outcomes

/-- Clean core success embeds into ordinary optional termination unchanged. -/
theorem YulStatementTerminatedParses.toOrdinary
    {coreClean coreOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      coreClean input statement output →
        coreOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulStatementTerminatedParses coreClean input statement output) :
    YulStatementTerminatedOrdinaryParses coreOrdinary input statement
      output := by
  rcases parsed with ⟨afterCore, coreParsed, semicolonParsed⟩
  exact ⟨afterCore, cleanToOrdinary coreParsed, semicolonParsed⟩

end Solcore.Syntax.DeclarativeGrammar
