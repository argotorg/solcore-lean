import Solcore.Syntax.DeclarativeTerminatedControlTraceProperties
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeProperties
import Solcore.Syntax.DeclarativeCoreBlockTraceExactnessProperties

/-! Total, mutually exclusive exact control-leaf traces, derived only from
token observations. Their joint laws instantiate raw and isolated block laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem TerminatedControlStatementTraceRejects.disjoint_success
    {keyword : HardKeyword} {statementValue : Syntax.StatementValue}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TerminatedControlStatementTraceRejects keyword source endByte
      input rejected diagnostic trace) :
    ¬ ∃ statement output events, TerminatedControlStatementTraceParses keyword statementValue
      source endByte input statement output events := by
  rintro ⟨statement, output, events, parsed⟩
  exact rejection.ordinary.disjointOrdinary ⟨statement, output, parsed.1⟩

/-- Every carrier, including an exhausted window or missing array slot,
determines either silent success or one silent first-failure report. -/
theorem terminatedControlStatementTrace_exists_outcome
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ statement output, TerminatedControlStatementTraceParses keyword statementValue
      source endByte input statement output []) ∨
    (∃ rejected diagnostic, TerminatedControlStatementTraceRejects keyword
      source endByte input rejected diagnostic []) := by
  by_cases marker : ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword keyword }
  · rcases marker with ⟨markerSpan, marker⟩
    let afterMarker : Remainder := { input with cursor := input.cursor + 1 }
    have parsedMarker : ExactTokenParses (.keyword keyword) input markerSpan afterMarker :=
      ⟨marker, rfl⟩
    by_cases semicolon : ∃ span, TokenAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
        { span, value := .symbol .semicolon }
    · rcases semicolon with ⟨semicolonSpan, semicolon⟩
      exact Or.inl ⟨_, _, .parsed markerSpan semicolonSpan parsedMarker ⟨semicolon, rfl⟩, rfl⟩
    · rcases rejectAtReports_total source endByte { head := .symbol .semicolon, tail := [] }
          .statement afterMarker with ⟨diagnostic, reported⟩
      exact Or.inr ⟨afterMarker, diagnostic,
        .semicolonMissing markerSpan parsedMarker semicolon reported⟩
  · rcases rejectAtReports_total source endByte { head := .keyword keyword, tail := [] }
        .statement input with ⟨diagnostic, reported⟩
    exact Or.inr ⟨input, diagnostic, .markerMissing marker reported⟩

/-- Complete AST/remainder/event uniqueness and exact first-failure exclusion
are unconditional for each fixed keyword-plus-semicolon leaf. -/
theorem terminatedControlStatementTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec
      (TerminatedControlStatementTraceParses keyword statementValue)
      (TerminatedControlStatementTraceRejects keyword) source endByte where
  successResultUnique := TerminatedControlStatementTraceParses.result_unique
  rejectResultUnique := TerminatedControlStatementTraceRejects.result_unique
  successRejectDisjoint := TerminatedControlStatementTraceRejects.disjoint_success

theorem breakStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec BreakStatementTraceParses BreakStatementTraceRejects
      source endByte :=
  terminatedControlStatementTraceExactOutcomeSpec .breakKw .breakStmt source endByte

theorem continueStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec ContinueStatementTraceParses ContinueStatementTraceRejects
      source endByte :=
  terminatedControlStatementTraceExactOutcomeSpec .continueKw .continueStmt source endByte

/-- Blocks restricted to one fixed control leaf have exact independent
outcomes without an abstract statement-outcome assumption. -/
theorem terminatedControlCoreBlockTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (CoreBlockTraceParses (TerminatedControlStatementTraceParses keyword statementValue) policy)
      (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
        (TerminatedControlStatementTraceRejects keyword) policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy
    (terminatedControlStatementTraceExactOutcomeSpec keyword statementValue source endByte)

/-- Every captured child byte boundary has the same unconditional leaf laws,
so isolated restricted blocks also have jointly exact traces and reports. -/
theorem isolatedTerminatedControlCoreBlockTraceExactOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.StatementValue)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses
        (CoreBlockTraceParses (TerminatedControlStatementTraceParses keyword statementValue) policy)
        (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
          (TerminatedControlStatementTraceRejects keyword) policy))
      (IsolatedBlockTraceRejects
        (CoreBlockTraceRejects (TerminatedControlStatementTraceParses keyword statementValue)
          (TerminatedControlStatementTraceRejects keyword) policy)) source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (fun childEndByte =>
    terminatedControlStatementTraceExactOutcomeSpec keyword statementValue source childEndByte)

end Solcore.Syntax.DeclarativeGrammar
