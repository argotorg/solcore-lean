import Solcore.Syntax.DeclarativeCoreBlockExactnessProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties

/-! Exact Core block statements and keyword-plus-semicolon control leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- The fixed control value retains the unique marker/semicolon cover span. -/
theorem TerminatedControlStatementOrdinaryParses.value_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftMarkerSpan leftSemicolonSpan leftMarker leftSemicolon =>
      cases rightParsed with
      | parsed rightMarkerSpan rightSemicolonSpan rightMarker rightSemicolon =>
          rcases leftMarker.result_unique rightMarker with
            ⟨markerSpanEq, afterMarkerEq⟩
          subst markerSpanEq
          subst afterMarkerEq
          have semicolonSpanEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonSpanEq
          rfl

/-- Control leaves fix the complete statement and successful remainder. -/
theorem TerminatedControlStatementOrdinaryParses.result_unique
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input left afterLeft)
    (rightParsed : TerminatedControlStatementOrdinaryParses keyword
      statementValue input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- A control rejection fixes either the original or post-marker endpoint. -/
theorem TerminatedControlStatementRejects.output_unique
    {keyword : HardKeyword} {input left right : Remainder}
    (leftRejects : TerminatedControlStatementRejects keyword input left)
    (rightRejects : TerminatedControlStatementRejects keyword input right) :
    left = right := by
  cases leftRejects with
  | markerMissing leftAbsent =>
      cases rightRejects with
      | markerMissing => rfl
      | semicolonMissing rightSpan rightMarker rightAbsent =>
          exact False.elim (absent_conflicts_exact leftAbsent rightMarker)
  | semicolonMissing leftSpan leftMarker leftAbsent =>
      cases rightRejects with
      | markerMissing rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftMarker)
      | semicolonMissing rightSpan rightMarker rightAbsent =>
          exact leftMarker.output_unique rightMarker

/-- Unconditional exact outcomes for one fixed terminated control keyword. -/
theorem terminatedControlStatementExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue) :
    ExactDeterministicOutcomeSpec
      (TerminatedControlStatementOrdinaryParses keyword statementValue)
      (TerminatedControlStatementRejects keyword) where
  toDeterministicOutcomeSpec :=
    terminatedControlStatementDeterministicOutcomeSpec keyword statementValue
  successValueUnique := TerminatedControlStatementOrdinaryParses.value_unique
  rejectOutputUnique := TerminatedControlStatementRejects.output_unique

/-- A block statement retains its child's exact body and source span. -/
theorem BlockStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.Statement}
    {afterLeft afterRight : Remainder}
    (leftParsed : BlockStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : BlockStatementOrdinaryParses statementOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftBody =>
      cases rightParsed with
      | parsed rightBody =>
          have bodyEq := (coreBlockExactOutcomeSpec .require
            statementOutcomes).successValueUnique leftBody rightBody
          subst bodyEq
          rfl

/-- Recursive exact statement outcomes lift through a required braced block. -/
theorem blockStatementExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : ExactDeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    ExactDeterministicOutcomeSpec
      (BlockStatementOrdinaryParses statementOrdinary)
      (BlockStatementRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec := blockStatementDeterministicOutcomeSpec
    statementOutcomes.toDeterministicOutcomeSpec
  successValueUnique := BlockStatementOrdinaryParses.value_unique statementOutcomes
  rejectOutputUnique := (coreBlockExactOutcomeSpec .require
    statementOutcomes).rejectOutputUnique

end Solcore.Syntax.DeclarativeGrammar
