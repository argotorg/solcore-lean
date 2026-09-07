import Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties

/-! Grammar-only consumers of complete Core tail traces. Concrete ASTs keep
full statement spans, written order, duplicate events, and protected kinds. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCoreBlockTailTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

section PublicApi

variable {statement : Statement} {policy : CoreBlockTailPolicy}
  {statements : List Statement} {left right : List ParseDiagnostic}

example (statement : Statement) :
    ∃ trace, CoreBlockStatementDiagnosticTrace statement trace :=
  CoreBlockStatementDiagnosticTrace.exists_trace statement

example (first : CoreBlockStatementDiagnosticTrace statement left)
    (second : CoreBlockStatementDiagnosticTrace statement right) : left = right :=
  first.output_unique second

example (parsed : CoreBlockStatementDiagnosticTrace statement left) :
    left = [] ↔ CoreBlockStatementTerminated statement := parsed.empty_iff

example (parsed : CoreBlockStatementDiagnosticTrace statement left)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical left left := parsed.cascadeFilters text lexical

example (policy : CoreBlockTailPolicy) (statements : List Statement) :
    ∃ trace, CoreBlockTailsDiagnosticTrace policy statements trace :=
  CoreBlockTailsDiagnosticTrace.exists_trace policy statements

example (first : CoreBlockTailsDiagnosticTrace policy statements left)
    (second : CoreBlockTailsDiagnosticTrace policy statements right) : left = right :=
  first.output_unique second

example (parsed : CoreBlockTailsDiagnosticTrace policy statements left) :
    left = [] ↔ CoreBlockTailsValid policy statements := parsed.empty_iff

example (parsed : CoreBlockTailsDiagnosticTrace policy statements left)
    (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical left left := parsed.cascadeFilters text lexical

end PublicApi

private def byteSpan (first last : Nat) : SourceSpan := {
  source := { origin := .main, path := "core-tail-trace.sol" }
  startByte := first
  endByte := last
}

private def groupedName (start : Nat) (name : String) : Expr := {
  span := byteSpan start (start + 3)
  value := .group {
    span := byteSpan (start + 1) (start + 2)
    value := .identifier { span := byteSpan (start + 1) (start + 2), value := name }
  }
}

private def firstStatement : Statement := {
  span := byteSpan 0 3, value := .expression (groupedName 0 "a") false
}

private def middleStatement : Statement := {
  span := byteSpan 4 6
  value := .expression {
    span := byteSpan 4 5
    value := .identifier { span := byteSpan 4 5, value := "b" }
  } true
}

private def lastStatement : Statement := {
  span := byteSpan 7 10, value := .expression (groupedName 7 "c") false
}

private def missingSemicolon (first last : Nat) : ParseDiagnostic := {
  span := byteSpan first last, kind := .constraintViolation .expressionRequiresSemicolon
}

private theorem firstMissing :
    CoreBlockStatementDiagnosticTrace firstStatement [missingSemicolon 0 3] :=
  .missing (fun impossible => impossible)

private theorem middleClean : CoreBlockStatementDiagnosticTrace middleStatement [] :=
  .clean trivial

private theorem lastMissing :
    CoreBlockStatementDiagnosticTrace lastStatement [missingSemicolon 7 10] :=
  .missing (fun impossible => impossible)

/-- The allowed final group is exempt; the first whole group still needs a
semicolon, whereas the middle expression already has one. -/
theorem allow_three_statements :
    CoreBlockTailsDiagnosticTrace .allow
      [firstStatement, middleStatement, lastStatement] [missingSemicolon 0 3] :=
  .cons firstMissing (.cons middleClean .lastAllowed)

/-- Requiring the final semicolon reports the two full group-statement spans,
not just the inner names at bytes 1..2 and 8..9, in written order. -/
theorem require_three_statements :
    CoreBlockTailsDiagnosticTrace .require
      [firstStatement, middleStatement, lastStatement]
      [missingSemicolon 0 3, missingSemicolon 7 10] :=
  .cons firstMissing (.cons middleClean (.lastRequired lastMissing))

/-- Repeated AST occurrences produce repeated complete reports, not a set. -/
theorem repeated_statement_preserves_duplicates :
    CoreBlockTailsDiagnosticTrace .require
      [firstStatement, firstStatement, firstStatement]
      [missingSemicolon 0 3, missingSemicolon 0 3, missingSemicolon 0 3] :=
  .cons firstMissing (.cons firstMissing (.lastRequired firstMissing))

/-- Both statement spans meet the same-LF-line lexical suppression condition
at the invalid character's span, but neither constraint report can be dropped. -/
theorem same_line_lexical_error_preserves_constraints :
    LexicalSpanSuppresses "(a) b; (c) §" (byteSpan 11 13) (byteSpan 0 3) ∧
    LexicalSpanSuppresses "(a) b; (c) §" (byteSpan 11 13) (byteSpan 7 10) ∧
    ParseDiagnosticCascadeFilters "(a) b; (c) §" [byteSpan 11 13]
      [missingSemicolon 0 3, missingSemicolon 7 10]
      [missingSemicolon 0 3, missingSemicolon 7 10] := by
  refine ⟨⟨rfl, Or.inl ?_⟩, ⟨rfl, Or.inl ?_⟩,
    require_three_statements.cascadeFilters _ _⟩ <;> decide +kernel

/-- The old diagnostic-free predicate is recovered from the allowed singleton
trace, even though the very same statement fails a mandatory check. -/
theorem allowed_singleton_recovers_old_validity :
    CoreBlockTailsValid .allow [firstStatement] ∧
      ¬ CoreBlockStatementTerminated firstStatement :=
  ⟨(CoreBlockTailsDiagnosticTrace.empty_iff
    (CoreBlockTailsDiagnosticTrace.lastAllowed (last := firstStatement))).mp rfl,
    fun impossible => impossible⟩

/-- A non-expression needs no expression-semicolon report under either policy. -/
theorem nonexpression_is_silent :
    CoreBlockStatementDiagnosticTrace
      { span := byteSpan 4 10, value := .breakStmt } [] := .clean trivial

end Solcore.Test.SyntaxCoreBlockTailTraceProperties
