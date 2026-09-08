import Solcore.Test.SyntaxExpressionAtomTotalityProperties
import Solcore.Syntax.Parser.PostfixTailTraceStateProperties
import Solcore.Syntax.Parser.PostfixTailUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties

/-! Independent witnesses for a mixed `.a-b[1](2)` postfix prefix, shared
between successful maximal tails and later exact rejection consumers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxExpressionAtomTotalityProperties

def source : SourceId := { origin := .main, path := "postfix-trace.sol" }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def sym (first last : Nat) (kind : Symbol) : Token := { span := span first last, value := .symbol kind }
def name : Identifier := { span := span 2 5, value := "a-b" }
def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def literal (first last : Nat) (spelling : String) : Expr := {
  span := span first last, value := .literal { span := span first last, value := .decimal spelling }
}
def base : Expr := { span := span 0 1, value := .identifier { span := span 0 1, value := "x" } }
def fieldValue : Expr := postfixFieldTraceValue base (span 1 2) name
def indexValue : Expr := postfixIndexTraceValue fieldValue (literal 6 7 "1") (span 5 6) (span 7 8)
def arguments : DelimitedList Expr := { span := span 8 11, elements := [literal 9 10 "2"] }
def callValue : Expr := postfixCallTraceValue indexValue arguments
def tokens (suffix : List Token) : List Token :=
  [sym 1 2 .dot, { span := name.span, value := .identifier name.value },
    sym 5 6 .leftBracket, { span := span 6 7, value := .decimalLiteral "1" }, sym 7 8 .rightBracket,
    sym 8 9 .leftParen, { span := span 9 10, value := .decimalLiteral "2" }, sym 10 11 .rightParen] ++ suffix
def rem (suffix : List Token) (cursor : Nat) : Remainder :=
  { tokens := (tokens suffix).toArray, endIndex := (tokens suffix).length, cursor }
def state (suffix : List Token) (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (tokens suffix).toArray, cursor
  window := { endIndex := (tokens suffix).length, endByte := 99 }, diagnosticsRev := prior.reverse
}

theorem prefix_name (suffix : List Token) :
    IdentifierTraceParses (rem suffix 1) name (rem suffix 2) [nameEvent] :=
  .parsed ⟨⟨by simp [rem, tokens], rfl⟩, rfl, rfl, rfl⟩
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide))

theorem prefix_index (suffix : List Token) :
    LiteralExpressionTraceParses source 99 (rem suffix 3) (literal 6 7 "1") (rem suffix 4) [] :=
  ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩

theorem prefix_arguments (suffix : List Token) :
    NoTrailingDelimitedListTraceParses .leftParen .rightParen true LiteralExpressionTraceParses
      source 99 (rem suffix 5) arguments (rem suffix 8) [] := by
  apply NoTrailingDelimitedListTraceParses.nonempty (afterOpening := rem suffix 6)
    (afterFirst := rem suffix 7) (first := literal 9 10 "2") (rest := [])
    (firstEvents := []) (tailEvents := []) (span 8 9) (span 10 11)
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact .absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens])
  · exact ⟨.parsed (.decimal ⟨by simp [rem, tokens], rfl⟩), rfl⟩
  · change 6 < 7; decide
  · exact .close (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym])
      ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩

theorem prefix_success (suffix : List Token) {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (tail : PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem suffix 8) callValue value after trace) :
    PostfixTailTraceParses LiteralExpressionTraceParses source 99 (rem suffix 0) base value after ([nameEvent] ++ trace) := by
  apply PostfixTailTraceParses.field (afterDot := rem suffix 1) (afterName := rem suffix 2)
    (nameEvents := [nameEvent]) (tailEvents := trace) (span 1 2)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact prefix_name suffix
  · apply PostfixTailTraceParses.index (afterOpening := rem suffix 3) (afterIndex := rem suffix 4)
      (afterClosing := rem suffix 5) (indexEvents := []) (tailEvents := trace) (span 5 6) (span 7 8)
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact prefix_index suffix
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact .call (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]) (prefix_arguments suffix) tail

theorem prefix_rejected (suffix : List Token) {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (tail : PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem suffix 8) callValue after report trace) :
    PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects source 99
      (rem suffix 0) base after report ([nameEvent] ++ trace) := by
  apply PostfixTailTraceRejects.fieldLaterRejected (afterDot := rem suffix 1) (afterName := rem suffix 2)
    (nameEvents := [nameEvent]) (tailEvents := trace) (span 1 2)
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]
  · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
  · exact prefix_name suffix
  · apply PostfixTailTraceRejects.indexLaterRejected (afterOpening := rem suffix 3) (afterIndex := rem suffix 4)
      (afterClosing := rem suffix 5) (indexEvents := []) (tailEvents := trace) (span 5 6) (span 7 8)
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact prefix_index suffix
    · exact ⟨⟨by simp [rem, tokens], rfl⟩, rfl⟩
    · exact .callLaterRejected (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, sym]) (prefix_arguments suffix) tail

theorem success_of_trace (block : Parser Block) {input : State} {initial value : Expr}
    {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses LiteralExpressionTraceParses input.file.id input.window.endByte
      input.declarativeRemainder initial value after trace) :
    postfixTail literalExpression block (input.remainingCount + 1) initial input =
      .ok value (input.traceResult after trace) :=
  (postfixTail_trace_success_state_iff_of_ne_invariant literalExpression_trace_success_sound
    literalExpression_trace_reject_sound literalExpression_success_context block _ initial
    (literalExpressionTraceExactOutcomeSpec _ _).toTraceExactOutcomeSpec
    (postfixTail_production_ne_invariant_of_unrestrictedElementFuel literalExpression block
      input.remainingCount (literal_child_contract _) initial input (Nat.lt_succ_self _))).mp parsed

theorem reject_of_trace (block : Parser Block) {input : State} {initial : Expr}
    {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
      input.file.id input.window.endByte input.declarativeRemainder initial after failure.toDiagnostic trace) :
    postfixTail literalExpression block (input.remainingCount + 1) initial input =
      .reject failure (input.traceResult after trace) :=
  (postfixTail_trace_reject_failure_state_iff_of_ne_invariant literalExpression_trace_success_sound
    literalExpression_trace_reject_sound literalExpression_success_context
    (fun result => ⟨(literalExpression_reject_context result).1,
      congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩) block _ initial
    (literalExpressionTraceExactOutcomeSpec _ _).toTraceExactOutcomeSpec
    (postfixTail_production_ne_invariant_of_unrestrictedElementFuel literalExpression block
      input.remainingCount (literal_child_contract _) initial input (Nat.lt_succ_self _))).mp rejection

end Solcore.Test.SyntaxPostfixTailTraceSupport
