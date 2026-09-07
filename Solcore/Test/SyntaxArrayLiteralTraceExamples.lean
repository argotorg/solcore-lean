import Solcore.Syntax.DeclarativeArrayLiteralTraceProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.Parser.ArrayLiteralTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Actual identifier/literal children in an array wrapper. Explicit trace
derivations determine the AST and ordered diagnostic suffix; only canonical
lexer fixtures use kernel decision. No general recursive expression is assumed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxArrayLiteralTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "array-literal-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def symbolToken (first last : Nat) (symbol : Symbol) : Token := {
  span := span first last, value := .symbol symbol
}
def nameA : Identifier := { span := span 1 4, value := "a-b" }
def nameC : Identifier := { span := span 5 8, value := "c-d" }
def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}
def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}

theorem name_trace {input : Remainder} (name : Identifier) (reportSource : SourceId) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses reportSource endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := TokenAt.token_unique token other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

theorem identifier_array_exact (reportSource : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ArrayLiteralTraceParses IdentifierExpressionTraceParses)
      (ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      reportSource endByte :=
  arrayLiteralTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec reportSource endByte)

theorem literal_array_exact (reportSource : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ArrayLiteralTraceParses LiteralExpressionTraceParses)
      (ArrayLiteralTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      reportSource endByte :=
  arrayLiteralTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec reportSource endByte)

def successText : String := "[a-b,c-d] tail"
def successTokens : List Token := [symbolToken 0 1 .leftBracket, nameToken nameA,
  symbolToken 4 5 .comma, nameToken nameC, symbolToken 8 9 .rightBracket,
  { span := span 10 14, value := .identifier "tail" }]
def successValues : DelimitedList Expr := { span := span 0 9, elements := [nameExpr nameA, nameExpr nameC] }
def successValue : Expr := { span := successValues.span, value := .array successValues }

theorem names_parsed : ArrayLiteralTraceParses IdentifierExpressionTraceParses source 14
    (remainder successTokens 6 0) successValue (remainder successTokens 6 5)
    [hyphen nameA, hyphen nameC] := by
  have closing : NoTrailingDelimitedTailTraceParses .rightBracket IdentifierExpressionTraceParses source 14
      (remainder successTokens 6 4) [] (span 8 9) (remainder successTokens 6 5) [] :=
    .close (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, symbolToken])
      ⟨⟨by decide, rfl⟩, rfl⟩
  have tail : NoTrailingDelimitedTailTraceParses .rightBracket IdentifierExpressionTraceParses source 14
      (remainder successTokens 6 2) [nameExpr nameC] (span 8 9)
      (remainder successTokens 6 5) [hyphen nameC] :=
    .next (span 4 5) (afterComma := remainder successTokens 6 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (name_trace nameC source 14 ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameC; decide))
      (by decide) closing
  exact .parsed (.nonempty (span 0 1) (span 8 9)
    (afterOpening := remainder successTokens 6 1) (afterFirst := remainder successTokens 6 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, nameToken]))
    (name_trace nameA source 14 ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide) tail)

/-- Both located identifiers appear in source order, with exactly two events.
The array wrapper keeps its list span, full parent context, and unread tail. -/
theorem names_array_success (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral identifierExpression (initial successText successTokens prior) =
        .ok successValue output ∧ output.declarativeRemainder = remainder successTokens 6 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file successText ∧ output.window = { endIndex := 6, endByte := 14 } ∧
      output.peek? = some { span := span 10 14, value := .identifier "tail" } := by
  rcases arrayLiteral_trace_success_complete identifierExpression_trace_success_complete
      identifierExpression_success_context (input := initial successText successTokens prior) names_parsed with
    ⟨output, result, after, events⟩
  have frame := arrayLiteral_success_context identifierExpression_success_context result
  refine ⟨output, result, after, ?_, frame.1, frame.2, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = successTokens.toArray at tokens
    change output.window.endIndex = 6 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

/-- Arbitrary lexical error contexts may filter earlier events but preserve
the complete two-name suffix, including its spans and payload order. -/
theorem names_array_protected (normalizationFile : SourceFile) (lexical : List LexicalDiagnostic)
    (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ [hyphen nameA, hyphen nameC]) =
      filterParseDiagnostics normalizationFile lexical prior ++ [hyphen nameA, hyphen nameC] := by
  rw [filterParseDiagnostics_append]
  exact congrArg (filterParseDiagnostics normalizationFile lexical prior ++ ·)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical
      (names_parsed.cascadeFilters (fun name => name.cascadeFilters _ _)))

def emptyText : String := "[] tail"
def emptyTokens : List Token := [symbolToken 0 1 .leftBracket, symbolToken 1 2 .rightBracket,
  { span := span 3 7, value := .identifier "tail" }]
def emptyValue : Expr := { span := span 0 2, value := .array { span := span 0 2, elements := [] } }

/-- The preferred empty close has an independent derivation containing no
child step. The concrete literal child adds no event and leaves `tail` unread. -/
theorem empty_array_success (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral literalExpression (initial emptyText emptyTokens prior) = .ok emptyValue output ∧
      output.declarativeRemainder = remainder emptyTokens 3 2 ∧ output.diagnostics = prior := by
  have parsed : ArrayLiteralTraceParses LiteralExpressionTraceParses source 7
      (remainder emptyTokens 3 0) emptyValue (remainder emptyTokens 3 2) [] :=
    .parsed (.empty (span 0 1) (span 1 2) rfl (afterOpening := remainder emptyTokens 3 1)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩)
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse, List.append_nil] using
    arrayLiteral_trace_success_complete literalExpression_trace_success_complete literalExpression_success_context
      (input := initial emptyText emptyTokens prior) parsed

def literalText : String := "[42] tail"
def literalTokens : List Token := [symbolToken 0 1 .leftBracket,
  { span := span 1 3, value := .decimalLiteral "42" }, symbolToken 3 4 .rightBracket,
  { span := span 5 9, value := .identifier "tail" }]
def literal42 : Expr := { span := span 1 3, value := .literal { span := span 1 3, value := .decimal "42" } }
def literalValue : Expr := {
  span := span 0 4, value := .array { span := span 0 4, elements := [literal42] }
}

theorem literal_array_success (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral literalExpression (initial literalText literalTokens prior) = .ok literalValue output ∧
      output.declarativeRemainder = remainder literalTokens 4 3 ∧ output.diagnostics = prior := by
  have leaf : LiteralExpressionTraceParses source 9 (remainder literalTokens 4 1)
      literal42 (remainder literalTokens 4 2) [] := ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩
  have parsed : ArrayLiteralTraceParses LiteralExpressionTraceParses source 9
      (remainder literalTokens 4 0) literalValue (remainder literalTokens 4 3) [] :=
    .parsed (.nonempty (span 0 1) (span 3 4) (afterOpening := remainder literalTokens 4 1)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, literalTokens])) leaf (by decide)
      (.close (by simp [TokenKindAbsentAt, TokenAt, remainder, literalTokens, symbolToken])
        ⟨⟨by decide, rfl⟩, rfl⟩))
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse, List.append_nil] using
    arrayLiteral_trace_success_complete literalExpression_trace_success_complete literalExpression_success_context
      (input := initial literalText literalTokens prior) parsed

theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem names_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 16384 in
theorem empty_lexes : Lexer.lex (file emptyText) = .ok (carrier emptyTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_names_array :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      arrayLiteral identifierExpression (State.initial (file successText) lexed) = .ok successValue output ∧
      output.declarativeRemainder = remainder successTokens 6 5 ∧
      output.diagnostics = [hyphen nameA, hyphen nameC] := by
  rcases names_array_success [] with ⟨output, result, after, events, _, _, _⟩
  exact ⟨carrier successTokens, output, names_lexes, result, after, events⟩

theorem canonical_empty_array :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      arrayLiteral literalExpression (State.initial (file emptyText) lexed) = .ok emptyValue output ∧
      output.declarativeRemainder = remainder emptyTokens 3 2 ∧ output.diagnostics = [] := by
  rcases empty_array_success [] with ⟨output, result, after, events⟩
  exact ⟨carrier emptyTokens, output, empty_lexes, result, after, events⟩

end Solcore.Test.SyntaxArrayLiteralTraceExamples
