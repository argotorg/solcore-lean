import Solcore.Syntax.Parser.TermStatementTotalityProperties

/-! Totality for semicolon-terminated control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ControlInternals

theorem terminatedControl_invariantFreeOnValid
    (keywordValue : HardKeyword) (value : StatementValue) :
    Parser.InvariantFreeOnValid (terminatedControl keywordValue value) := by
  unfold terminatedControl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor keywordValue .statement)
    (keyword_ordinary keywordValue .statement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .statement)
    (symbol_ordinary .semicolon .statement).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span semicolon.span
    value
  } : Statement)

end ControlInternals

theorem breakStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid breakStatement := by
  simpa only [breakStatement] using
    ControlInternals.terminatedControl_invariantFreeOnValid
      .breakKw .breakStmt

theorem continueStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid continueStatement := by
  simpa only [continueStatement] using
    ControlInternals.terminatedControl_invariantFreeOnValid
      .continueKw .continueStmt

theorem breakStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      breakStatement := {
  validFor := breakStatement_validFor expressionValueValid patternValueValid
    yulValueValid
  preservesTokenWindow := breakStatement_preservesTokenWindow
  cursorMonotoneOnSuccess := breakStatement_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    breakStatement_startsAtCurrentTokenOnSuccess
  invariantFree := breakStatement_invariantFreeOnValid
}

theorem continueStatement_totalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop) :
    TermInternals.StatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid yulValueValid)
      continueStatement := {
  validFor := continueStatement_validFor expressionValueValid
    patternValueValid yulValueValid
  preservesTokenWindow := continueStatement_preservesTokenWindow
  cursorMonotoneOnSuccess := continueStatement_cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    continueStatement_startsAtCurrentTokenOnSuccess
  invariantFree := continueStatement_invariantFreeOnValid
}

end Solcore.Syntax.Parser
