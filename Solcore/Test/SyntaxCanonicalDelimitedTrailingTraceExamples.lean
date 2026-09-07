import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties

/-! A real checked-name child executes the generic trailing-enabled list on
canonical lexer output. This is not a general type-argument parser claim. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

def source : SourceId := { origin := .main, path := "canonical-trailing-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
def nameA : Identifier := { span := span 1 4, value := "a-b" }
def nameC : Identifier := { span := span 5 8, value := "c-d" }
def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def initial (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file text) (carrier tokens) with diagnosticsRev := prior.reverse
}
def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

theorem name_trace {input : Remainder} (name : Identifier) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses source endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := token.token_unique other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

theorem peek_of_remainder {output : State} {after : Remainder} {token : Token}
    (same : output.declarativeRemainder = after)
    (current : TokenAt after.tokens after.endIndex after.cursor token) : output.peek? = some token := by
  have actual : TokenAt output.tokens output.window.endIndex output.cursor token := by
    simpa only [← same, State.declarativeRemainder] using current
  simp only [State.peek?, actual.1, if_true, actual.2]

theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

def text : String := "<a-b,c-d,> tail"
def tokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  nameToken nameC, sym 8 9 .comma, sym 9 10 .greater,
  { span := span 11 15, value := .identifier "tail" }]
def value : DelimitedList Expr := { span := span 0 10, elements := [nameExpr nameA, nameExpr nameC] }

private theorem parsed : TrailingDelimitedListTraceParses .less .greater false
    IdentifierExpressionTraceParses source 15 (remainder tokens 0) value (remainder tokens 6)
      [hyphen nameA, hyphen nameC] :=
  .nonempty (span 0 1) (span 9 10) (afterOpening := remainder tokens 1)
    (afterFirst := remainder tokens 2) ⟨⟨by decide, rfl⟩, rfl⟩ .disabled
    (name_trace (input := remainder tokens 1) nameA 15 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.next (span 4 5) (afterComma := remainder tokens 3) (afterElement := remainder tokens 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, nameToken])
      (name_trace (input := remainder tokens 3) nameC 15 ⟨by decide, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by decide)
      (.trailing (span 8 9) (afterComma := remainder tokens 5)
        ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩))

set_option maxRecDepth 16384 in
theorem trailing_list_lexes : Lexer.lex (file text) = .ok (carrier tokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Both checked-name events follow every incoming event, while the full
list AST, parent window, exact carrier/cursor, and following token are fixed. -/
theorem canonical_trailing_list (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file text) = .ok lexed ∧
      delimited .less .greater false identifierExpression .expression .expression
        { State.initial (file text) lexed with diagnosticsRev := prior.reverse } = .ok value output ∧
      output.declarativeRemainder = remainder tokens 6 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file text ∧ output.window = { endIndex := 7, endByte := 15 } ∧
      output.peek? = some { span := span 11 15, value := .identifier "tail" } := by
  rcases delimited_trace_success_complete identifierExpression_trace_success_complete
      identifierExpression_success_context .less .greater false .expression .expression
      (input := initial text tokens prior) parsed with ⟨output, result, after, events⟩
  have frame := delimited_success_context identifierExpression_success_context
    .less .greater false .expression .expression result
  refine ⟨carrier tokens, output, trailing_list_lexes, result, after, ?_, frame.1, frame.2,
    peek_of_remainder after ⟨by decide, rfl⟩⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events

end Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
