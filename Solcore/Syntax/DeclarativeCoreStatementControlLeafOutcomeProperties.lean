import Solcore.Syntax.DeclarativeCoreBlockOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeGrammar

/-! Deterministic outcomes for Core block and terminated-control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Keyword-plus-semicolon control success has a unique remainder. -/
theorem TerminatedControlStatementOrdinaryParses.output_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker
            rightSemicolon =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact terminated-control rejection excludes success. -/
theorem TerminatedControlStatementRejects.disjointOrdinary
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input rejected : Remainder}
    (rejection : TerminatedControlStatementRejects keyword input rejected) :
    ¬ ∃ statement output,
      TerminatedControlStatementOrdinaryParses keyword statementValue input
        statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulSemicolonSpan successfulMarker
        successfulSemicolon =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | semicolonMissing rejectedMarkerSpan rejectedMarker
            semicolonAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Deterministic outcome of one fixed terminated-control statement. -/
theorem terminatedControlStatementDeterministicOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    DeterministicOutcomeSpec
      (TerminatedControlStatementOrdinaryParses keyword statementValue)
      (TerminatedControlStatementRejects keyword) where
  successOutputUnique :=
    TerminatedControlStatementOrdinaryParses.output_unique
  successRejectDisjoint :=
    TerminatedControlStatementRejects.disjointOrdinary

/-- Diagnostic-inclusive block statements have a unique remainder. -/
theorem BlockStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : BlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : BlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          exact (coreBlockDeterministicOutcomeSpec .require
            statementOutcomes).successOutputUnique leftBody rightBody

/-- Raw block rejection excludes a block-statement success. -/
theorem BlockStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : BlockStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      BlockStatementOrdinaryParses statementOrdinary input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed bodyParsed =>
      exact (coreBlockDeterministicOutcomeSpec .require
        statementOutcomes).successRejectDisjoint rejection
          ⟨_, _, bodyParsed⟩

/-- Lift recursive statement outcomes through `blockStatement`. -/
theorem blockStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (BlockStatementOrdinaryParses statementOrdinary)
      (BlockStatementRejects statementOrdinary statementRejects) where
  successOutputUnique := BlockStatementOrdinaryParses.output_unique
    statementOutcomes
  successRejectDisjoint := BlockStatementRejects.disjointOrdinary
    statementOutcomes

end Solcore.Syntax.DeclarativeGrammar
