import Solcore.Syntax.Parser.ArrayLiteralTraceProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties
import Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties
import Solcore.Syntax.Parser.CoreBlockContextProperties

/-! Actual checked-name arrays inside a return-only Core block. The five
statement contracts are composed from actual child contracts; independent
tokens derive all parser outcomes. Only canonical lexing uses kernel decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxArrayReturnBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

abbrev arrayTrace := ArrayLiteralTraceParses IdentifierExpressionTraceParses
abbrev arrayRejects := ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
abbrev returnedTrace := ReturnStatementTraceParses arrayTrace
abbrev returnedRejects := ReturnStatementTraceRejects arrayTrace arrayRejects
abbrev arrayReturn := returnStatement (arrayLiteral identifierExpression)

theorem arrayReturn_success_sound : StatementTraceSuccessSound arrayReturn returnedTrace :=
  returnStatement_trace_success_sound
    (arrayLiteral_trace_success_sound identifierExpression_trace_success_sound identifierExpression_success_context)
theorem arrayReturn_success_complete : StatementTraceSuccessComplete arrayReturn returnedTrace :=
  returnStatement_trace_success_complete
    (arrayLiteral_trace_success_complete identifierExpression_trace_success_complete identifierExpression_success_context)
theorem arrayReturn_success_context : StatementSuccessContext arrayReturn :=
  returnStatement_success_context (arrayLiteral_success_context identifierExpression_success_context)
theorem arrayReturn_reject_sound : StatementTraceRejectSound arrayReturn returnedRejects :=
  returnStatement_reject_trace_sound
    (arrayLiteral_trace_success_sound identifierExpression_trace_success_sound identifierExpression_success_context)
    (arrayLiteral_trace_reject_sound identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_success_context)
    (arrayLiteral_success_context identifierExpression_success_context)
theorem arrayReturn_reject_complete : StatementTraceRejectComplete arrayReturn returnedRejects :=
  returnStatement_trace_reject_complete
    (arrayLiteral_trace_success_complete identifierExpression_trace_success_complete identifierExpression_success_context)
    (arrayLiteral_trace_reject_complete identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context)
    (arrayLiteral_success_context identifierExpression_success_context)

def source : SourceId := { origin := .main, path := "array-return-block-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
def marker : Token := { span := span 2 8, value := .keyword .returnKw }
def nameA : Identifier := { span := span 10 13, value := "a-b" }
def nameC : Identifier := { span := span 14 17, value := "c-d" }
def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def initial (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file text) (carrier tokens) with diagnosticsRev := prior.reverse
}
def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}

theorem name_trace {input : Remainder} (name : Identifier) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses source endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := TokenAt.token_unique token other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

def successText : String := "{ return [a-b,c-d]; } tail"
def successTokens : List Token := [sym 0 1 .leftBrace, marker, sym 9 10 .leftBracket,
  nameToken nameA, sym 13 14 .comma, nameToken nameC, sym 17 18 .rightBracket,
  sym 18 19 .semicolon, sym 20 21 .rightBrace,
  { span := span 22 26, value := .identifier "tail" }]
def arrayValue : Expr := {
  span := span 9 18, value := .array { span := span 9 18, elements := [nameExpr nameA, nameExpr nameC] }
}
def returned : Statement := { span := span 2 19, value := .returnStmt (some arrayValue) }
def body : Block := { span := span 0 21, value := [returned] }

private theorem array_parsed (endByte endIndex : Nat) (inside : 8 < endIndex) :
    arrayTrace source endByte (remainder successTokens endIndex 2) arrayValue
      (remainder successTokens endIndex 7) [hyphen nameA, hyphen nameC] := by
  have closing : NoTrailingDelimitedTailTraceParses .rightBracket IdentifierExpressionTraceParses source endByte
      (remainder successTokens endIndex 6) [] (span 17 18) (remainder successTokens endIndex 7) [] :=
    .close (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, sym])
      ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩
  have tail : NoTrailingDelimitedTailTraceParses .rightBracket IdentifierExpressionTraceParses source endByte
      (remainder successTokens endIndex 4) [nameExpr nameC] (span 17 18)
      (remainder successTokens endIndex 7) [hyphen nameC] :=
    .next (span 13 14) (afterComma := remainder successTokens endIndex 5)
      ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
      (name_trace (input := remainder successTokens endIndex 5) nameC endByte
        ⟨by change 5 < endIndex; omega, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by change 5 < 6; decide) closing
  exact .parsed (.nonempty (span 9 10) (span 17 18) (input := remainder successTokens endIndex 2)
    (afterOpening := remainder successTokens endIndex 3) (afterFirst := remainder successTokens endIndex 4)
    ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, nameToken]))
    (name_trace (input := remainder successTokens endIndex 3) nameA endByte
      ⟨by change 3 < endIndex; omega, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by change 3 < 4; decide) tail)

private theorem return_parsed (endByte endIndex : Nat) (inside : 8 < endIndex) :
    returnedTrace source endByte (remainder successTokens endIndex 1) returned
      (remainder successTokens endIndex 8) [hyphen nameA, hyphen nameC] :=
  .parsed (span 2 8) (span 18 19) (afterMarker := remainder successTokens endIndex 2)
    (afterValue := remainder successTokens endIndex 7)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, sym])
      (array_parsed endByte endIndex inside))
    ⟨⟨by change 7 < endIndex; omega, rfl⟩, rfl⟩

private theorem block_parsed (policy : CoreBlockTailPolicy) (endByte endIndex : Nat)
    (inside : 8 < endIndex) :
    CoreBlockTraceParses returnedTrace policy source endByte (remainder successTokens endIndex 0)
      body (remainder successTokens endIndex 9) [hyphen nameA, hyphen nameC] := by
  have closing : CoreBlockItemsTraceParses returnedTrace source endByte (remainder successTokens endIndex 8)
      [] (span 20 21) (remainder successTokens endIndex 9) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have validation : CoreBlockTailsDiagnosticTrace policy [returned] [] := by
    cases policy with
    | allow => exact .lastAllowed
    | require => exact .lastRequired (.clean trivial)
  exact .parsed (span 0 1) (span 20 21) (afterOpening := remainder successTokens endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩
    (.next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, successTokens, marker])
      (return_parsed endByte endIndex inside) (by change 1 < 8; decide) closing) validation

private def capture : BalancedBlockCapture := { span := span 0 21, endIndex := 9, endByte := 21 }
private theorem captured : BalancedBlockCaptures (remainder successTokens 10 0) capture :=
  .captured (input := remainder successTokens 10 0) (openingSpan := span 0 1) (closingSpan := span 20 21)
    ⟨by decide, rfl⟩
    (.other (token := marker) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := sym 9 10 .leftBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := sym 13 14 .comma) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := nameToken nameC) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.other (token := sym 17 18 .rightBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
                (.other (token := sym 18 19 .semicolon) ⟨by decide, rfl⟩ (by decide) (by decide)
                  (.close ⟨by decide, rfl⟩))))))))

/-- Array, return and raw block add no events beyond the ordered two name
reports. All prior events and the complete nested AST remain intact. -/
theorem array_return_raw_success (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock arrayReturn policy (initial successText successTokens prior) = .ok body output ∧
      output.declarativeRemainder = remainder successTokens 10 9 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file successText ∧ output.window = { endIndex := 10, endByte := 26 } := by
  rcases (coreBlock_trace_success_iff arrayReturn_success_sound arrayReturn_success_complete
      arrayReturn_success_context policy (input := initial successText successTokens prior)).mp
      (block_parsed policy.declarative 26 10 (by decide)) with ⟨output, result, after, events⟩
  have frame := coreBlock_success_context_eq arrayReturn_success_context policy result
  refine ⟨output, result, after, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events

/-- One outer isolation preserves the complete successful array-return body
and restores parent byte boundary 26 after child 21, stopping before `tail`. -/
theorem array_return_isolated_success (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock arrayReturn policy) (initial successText successTokens prior) =
        .ok body output ∧ output.declarativeRemainder = remainder successTokens 10 9 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file successText ∧ output.window = { endIndex := 10, endByte := 26 } ∧
      output.peek? = some { span := span 22 26, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses returnedTrace policy.declarative)
      (CoreBlockTraceRejects returnedTrace returnedRejects policy.declarative) source 26
      (remainder successTokens 10 0) body (remainder successTokens 10 9) [hyphen nameA, hyphen nameC] :=
    .captured captured (block_parsed policy.declarative 21 9 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff arrayReturn_success_sound arrayReturn_reject_sound
      arrayReturn_success_complete arrayReturn_reject_complete arrayReturn_success_context policy
      (input := initial successText successTokens prior)).mp parsed with ⟨output, result, after, events⟩
  rcases BlockInternals.captureBlock?_complete (input := initial successText successTokens prior) captured with
    ⟨runtimeCapture, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = successTokens.toArray at tokens
    change output.window.endIndex = 10 at endpoint
    change output.cursor = 9 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem success_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_array_return_raw_success (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      coreBlock (returnStatement (arrayLiteral identifierExpression)) policy
        (State.initial (file successText) lexed) = .ok body output ∧
      output.declarativeRemainder = remainder successTokens 10 9 ∧
      output.diagnostics = [hyphen nameA, hyphen nameC] := by
  rcases array_return_raw_success policy [] with ⟨output, result, after, events, _, _⟩
  exact ⟨carrier successTokens, output, success_lexes, result, after, events⟩

theorem canonical_array_return_success (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      isolateBlock (coreBlock (returnStatement (arrayLiteral identifierExpression)) policy)
        (State.initial (file successText) lexed) = .ok body output ∧
      output.declarativeRemainder = remainder successTokens 10 9 ∧
      output.diagnostics = [hyphen nameA, hyphen nameC] ∧
      output.window = { endIndex := 10, endByte := 26 } ∧
      output.peek? = some { span := span 22 26, value := .identifier "tail" } := by
  rcases array_return_isolated_success policy [] with ⟨output, result, after, events, _, window, next⟩
  exact ⟨carrier successTokens, output, success_lexes, result, after, events, window, next⟩

end Solcore.Test.SyntaxArrayReturnBlockTraceExamples
