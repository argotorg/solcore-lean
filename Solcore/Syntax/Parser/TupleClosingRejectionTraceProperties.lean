import Solcore.Syntax.Parser.TupleClosingTraceProperties
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

/-! Closing failure preserves the entire state and asks only for a right
parenthesis, regardless of the accumulated reverse element prefix. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

theorem closeTuple_reject_iff_symbol (opening : Token) (elementsRev : List Expr)
    {input rejected : State} {failure : Failure} :
    closeTuple opening elementsRev input = .reject failure rejected ↔
      symbol .rightParen .expression input = .reject failure rejected := by
  rw [closeTuple_eq_of_symbol]
  cases symbol .rightParen .expression input <;> simp

theorem closeTuple_reject_state_eq (opening : Token) (elementsRev : List Expr)
    {input rejected : State} {failure : Failure}
    (result : closeTuple opening elementsRev input = .reject failure rejected) : rejected = input :=
  symbol_reject_state_eq .rightParen .expression ((closeTuple_reject_iff_symbol opening elementsRev).mp result)

theorem closeTuple_reject_reports_iff (opening : Token) (elementsRev : List Expr)
    {input : State} {report : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightParen) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightParen, tail := [] } .expression input.declarativeRemainder report) ↔
      ∃ failure, closeTuple opening elementsRev input = .reject failure input ∧ failure.toDiagnostic = report := by
  rw [symbol_reject_reports_iff .rightParen .expression]
  simp only [closeTuple_reject_iff_symbol]

end Solcore.Syntax.Parser.ExpressionAtomInternals
