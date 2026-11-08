import Solcore.Syntax.Parser.Internal.ParenthesizedTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomTrace
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Internal.PragmaTrace
import Solcore.Syntax.Parser.Internal.StatementTotality
import Solcore.Syntax.Parser.Internal.BlockSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.ControlSoundness
import Solcore.Syntax.Parser
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Syntax.Parser.Internal.SimpleStatementSoundness
import Solcore.Syntax.Parser.Internal.TermTotality
import Solcore.Syntax.Parser.Internal.PublicTermTotality
import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Validity

/-!
# Statement and block tests

Statements, blocks, return and control forms, with worked block traces, fuel totality of each
statement form, and the term level that ties expressions and statements together.
-/

section
-- leanmerge: from Solcore.Test.SyntaxArrayReturnBlockTraceExamples
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
end

section
-- leanmerge: from Solcore.Test.SyntaxArrayReturnBlockRejectionTraceExamples
/-! A checked name event precedes an identifier-child failure in the array.
The return and raw block preserve that full report without committing it.
Only the single outer isolation recovers, restoring the exact parent tail. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxArrayReturnBlockRejectionTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxArrayReturnBlockTraceExamples

def rejectionText : String := "{ return [a-b,+]; } tail"
def rejectionTokens : List Token := [sym 0 1 .leftBrace, marker, sym 9 10 .leftBracket,
  nameToken nameA, sym 13 14 .comma, sym 14 15 .plus, sym 15 16 .rightBracket,
  sym 16 17 .semicolon, sym 18 19 .rightBrace,
  { span := span 20 24, value := .identifier "tail" }]
def childFailure : Failure := {
  span := span 14 15, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem array_rejected (endByte endIndex : Nat) (inside : 8 < endIndex) :
    arrayRejects source endByte (remainder rejectionTokens endIndex 2)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [hyphen nameA] := by
  have child : IdentifierExpressionTraceRejects source endByte (remainder rejectionTokens endIndex 5)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [] :=
    ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, sym],
      .absent (by simp [IdentifierAbsentAt, TokenAt, remainder, rejectionTokens, sym]),
      .reported (.token (current := sym 14 15 .plus) ⟨by change 5 < endIndex; omega, rfl⟩), rfl⟩
  unfold arrayRejects ArrayLiteralTraceRejects
  exact .tailRejected (span 9 10) (input := remainder rejectionTokens endIndex 2)
    (opening := .leftBracket) (closing := .rightBracket)
    (afterOpening := remainder rejectionTokens endIndex 3) (afterFirst := remainder rejectionTokens endIndex 4)
    ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, nameToken]))
    (name_trace (input := remainder rejectionTokens endIndex 3) nameA endByte
      ⟨by change 3 < endIndex; omega, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by change 3 < 4; decide)
    (.elementRejected (span 13 14) (afterComma := remainder rejectionTokens endIndex 5)
      ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩ child)

private theorem return_rejected (endByte endIndex : Nat) (inside : 8 < endIndex) :
    returnedRejects source endByte (remainder rejectionTokens endIndex 1)
      (remainder rejectionTokens endIndex 5) childFailure.toDiagnostic [hyphen nameA] :=
  .valueRejected (span 2 8) (afterMarker := remainder rejectionTokens endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.expressionRejected (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, sym])
      (array_rejected endByte endIndex inside))

private theorem block_rejected (policy : CoreBlockTailPolicy) (endByte endIndex : Nat)
    (inside : 8 < endIndex) :
    CoreBlockTraceRejects returnedTrace returnedRejects policy source endByte
      (remainder rejectionTokens endIndex 0) (remainder rejectionTokens endIndex 5)
      childFailure.toDiagnostic [hyphen nameA] :=
  .itemsRejected (span 0 1) (afterOpening := remainder rejectionTokens endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩
    (.statementRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, rejectionTokens, marker])
      (return_rejected endByte endIndex inside))

private def capture : BalancedBlockCapture := { span := span 0 19, endIndex := 9, endByte := 19 }
private theorem captured : BalancedBlockCaptures (remainder rejectionTokens 10 0) capture :=
  .captured (input := remainder rejectionTokens 10 0) (openingSpan := span 0 1) (closingSpan := span 18 19)
    ⟨by decide, rfl⟩
    (.other (token := marker) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := sym 9 10 .leftBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := sym 13 14 .comma) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := sym 14 15 .plus) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.other (token := sym 15 16 .rightBracket) ⟨by decide, rfl⟩ (by decide) (by decide)
                (.other (token := sym 16 17 .semicolon) ⟨by decide, rfl⟩ (by decide) (by decide)
                  (.close ⟨by decide, rfl⟩))))))))

/-- The array child's complete identifier report escapes return and raw block
unchanged. The following semicolon/brace are not reached and no report is committed. -/
theorem array_return_raw_rejection (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock arrayReturn policy (initial rejectionText rejectionTokens prior) =
        .reject childFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 10 5 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.peek? = some (sym 14 15 .plus) := by
  rcases (coreBlock_trace_reject_failure_iff arrayReturn_success_sound arrayReturn_reject_sound
      arrayReturn_success_complete arrayReturn_reject_complete arrayReturn_success_context policy
      (input := initial rejectionText rejectionTokens prior)).mp
      (block_rejected policy.declarative 24 10 (by decide)) with ⟨output, result, after, events⟩
  refine ⟨output, result, after, ?_, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 10 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

/-- One isolation discards the rejected body and appends the one child report
after the name event. Parent byte boundary 24 replaces child 19; `tail` is unread. -/
theorem array_return_isolated_recovery (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock arrayReturn policy) (initial rejectionText rejectionTokens prior) =
        .ok { span := span 0 19, value := [] } output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 9 ∧
      output.diagnostics = prior ++ [hyphen nameA, childFailure.toDiagnostic] ∧
      output.file = file rejectionText ∧ output.window = { endIndex := 10, endByte := 24 } ∧
      output.peek? = some { span := span 20 24, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses returnedTrace policy.declarative)
      (CoreBlockTraceRejects returnedTrace returnedRejects policy.declarative) source 24
      (remainder rejectionTokens 10 0) { span := span 0 19, value := [] }
      (remainder rejectionTokens 10 9) [hyphen nameA, childFailure.toDiagnostic] :=
    .recovered captured (block_rejected policy.declarative 19 9 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff arrayReturn_success_sound arrayReturn_reject_sound
      arrayReturn_success_complete arrayReturn_reject_complete arrayReturn_success_context policy
      (input := initial rejectionText rejectionTokens prior)).mp parsed with ⟨output, result, after, events⟩
  rcases BlockInternals.captureBlock?_complete (input := initial rejectionText rejectionTokens prior) captured with
    ⟨runtimeCapture, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 10 at endpoint
    change output.cursor = 9 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_array_return_rejection (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      coreBlock (returnStatement (arrayLiteral identifierExpression)) policy
        (State.initial (file rejectionText) lexed) = .reject childFailure output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 5 ∧ output.diagnostics = [hyphen nameA] := by
  rcases array_return_raw_rejection policy [] with ⟨output, result, after, events, _⟩
  exact ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events⟩

theorem canonical_array_return_recovery (policy : TailExpressionPolicy) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      isolateBlock (coreBlock (returnStatement (arrayLiteral identifierExpression)) policy)
        (State.initial (file rejectionText) lexed) = .ok { span := span 0 19, value := [] } output ∧
      output.declarativeRemainder = remainder rejectionTokens 10 9 ∧
      output.diagnostics = [hyphen nameA, childFailure.toDiagnostic] ∧
      output.window = { endIndex := 10, endByte := 24 } ∧
      output.peek? = some { span := span 20 24, value := .identifier "tail" } := by
  rcases array_return_isolated_recovery policy [] with ⟨output, result, after, events, _, window, next⟩
  exact ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events, window, next⟩

end Solcore.Test.SyntaxArrayReturnBlockRejectionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxBlockIdentifierTraceContracts
/-! A deliberately small test-only statement parser: checked names become
unterminated expression statements. Its independent contracts quantify all
source contexts, windows, and prior diagnostics; this is not the Core parser. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxBlockIdentifierTraceContracts

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

def nameStatement (name : Identifier) : Statement := {
  span := name.span
  value := .expression { span := name.span, value := .identifier name } false
}

def checkedNameStatement : Parser Statement := fun input =>
  match identifier .statement input with
  | .ok name output => .ok (nameStatement name) output
  | .reject failure rejected => .reject failure rejected
  | .invariant error => .invariant error

inductive NameStatementTraceParses (_source : SourceId) (_endByte : Nat) :
    Remainder → Statement → Remainder → List ParseDiagnostic → Prop where
  | parsed {input output : Remainder} {name : Identifier} {trace : List ParseDiagnostic}
      (nameParsed : IdentifierTraceParses input name output trace) :
      NameStatementTraceParses _source _endByte input (nameStatement name) output trace

def NameStatementTraceRejects (source : SourceId) (endByte : Nat)
    (input rejected : Remainder) (diagnostic : ParseDiagnostic)
    (trace : List ParseDiagnostic) : Prop :=
  IdentifierRejects input rejected ∧
    RejectAtReports source endByte { head := .identifier, tail := [] }
      .statement rejected diagnostic ∧ trace = []

theorem checkedNameStatement_success_sound :
    StatementTraceSuccessSound checkedNameStatement NameStatementTraceParses := by
  intro input output statement result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | reject failure rejected => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | ok name next =>
      simp only [nameResult] at result
      cases result
      rcases identifier_success_trace_sound .statement nameResult with
        ⟨trace, parsed, diagnostics⟩
      exact ⟨trace, .parsed parsed, diagnostics⟩

theorem checkedNameStatement_success_complete :
    StatementTraceSuccessComplete checkedNameStatement NameStatementTraceParses := by
  intro input statement after trace parsed
  cases parsed with
  | parsed nameParsed =>
      rcases (identifier_trace_success_iff .statement).mp nameParsed with
        ⟨output, result, remainder, diagnostics⟩
      exact ⟨output, by simp only [checkedNameStatement, result], remainder, diagnostics⟩

theorem checkedNameStatement_success_context :
    StatementSuccessContext checkedNameStatement := by
  intro input output statement result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | reject failure rejected => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | ok name next =>
      simp only [nameResult] at result
      cases result
      exact identifier_success_context_eq .statement nameResult

theorem checkedNameStatement_reject_sound :
    StatementTraceRejectSound checkedNameStatement NameStatementTraceRejects := by
  intro input rejected failure result
  unfold checkedNameStatement at result
  cases nameResult : identifier .statement input with
  | ok name output => simp [nameResult] at result
  | invariant error => simp [nameResult] at result
  | reject actual output =>
      simp only [nameResult] at result
      cases result
      have stateEq := identifier_reject_state_eq .statement nameResult
      subst rejected
      have reports := (identifier_reject_reports_iff .statement).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], ⟨.absent reports.1, reports.2, rfl⟩, by simp⟩

theorem checkedNameStatement_reject_complete :
    StatementTraceRejectComplete checkedNameStatement NameStatementTraceRejects := by
  intro input after diagnostic trace rejected
  rcases rejected with ⟨ordinary, report, rfl⟩
  cases ordinary with
  | absent missing =>
      rcases (identifier_reject_reports_iff .statement).mp ⟨missing, report⟩ with
        ⟨failure, result, diagnosticEq⟩
      exact ⟨failure, input, by simp only [checkedNameStatement, result],
        rfl, diagnosticEq, by simp⟩

end Solcore.Test.SyntaxBlockIdentifierTraceContracts
end

section
-- leanmerge: from Solcore.Test.SyntaxBlockIdentifierTraceExamples
/-! Concrete token-carrier consumers of the test-only checked-name statement
parser. Independent derivations, not evaluation of a complete parser, determine
every AST, endpoint, and diagnostic. No canonical lexer claim is made here. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxBlockIdentifierTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxBlockIdentifierTraceContracts

private def source : SourceId := { origin := .main, path := "block-name-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 2 5, value := "a-b" }
private def nameC : Identifier := { span := span 6 9, value := "c-d" }
private def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
private def missing (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .constraintViolation .expressionRequiresSemicolon
}
private def successTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := nameA.span, value := .identifier nameA.value },
  { span := nameC.span, value := .identifier nameC.value },
  { span := span 10 11, value := .symbol .rightBrace }]
private def successRem (cursor : Nat) : Remainder := { tokens := successTokens, endIndex := 4, cursor }
private def successState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ a-b c-d }" }
  tokens := successTokens, cursor := 0, window := { endIndex := 4, endByte := 11 }
  diagnosticsRev := prior.reverse
}
private def successBody : Block := {
  span := span 0 11, value := [nameStatement nameA, nameStatement nameC]
}

private theorem firstName : IdentifierTraceParses (successRem 1) nameA
    (successRem 2) [hyphen nameA] :=
  .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by
    unfold IdentifierHyphenSpelling nameA; decide))

private theorem secondName : IdentifierTraceParses (successRem 2) nameC
    (successRem 3) [hyphen nameC] :=
  .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by
    unfold IdentifierHyphenSpelling nameC; decide))

private theorem successItems (reportSource : SourceId) (endByte : Nat) :
    CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte (successRem 1)
      [nameStatement nameA, nameStatement nameC] (span 10 11) (successRem 4)
      [hyphen nameA, hyphen nameC] := by
  have closing : CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte
      (successRem 3) [] (span 10 11) (successRem 4) [] :=
    .close _ ⟨⟨by decide, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses NameStatementTraceParses reportSource endByte
      (successRem 2) [nameStatement nameC] (span 10 11) (successRem 4) [hyphen nameC] :=
    .next (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens])
      (.parsed secondName) (by decide) closing
  exact .next (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens])
    (.parsed firstName) (by decide) last

private theorem nameMissing (name : Identifier) :
    CoreBlockStatementDiagnosticTrace (nameStatement name) [missing name] :=
  .missing (fun impossible => impossible)

private theorem opening : ExactTokenParses (.symbol .leftBrace)
    (successRem 0) (span 0 1) (successRem 1) := ⟨⟨by decide, rfl⟩, rfl⟩

private theorem requireParsed (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses NameStatementTraceParses .require reportSource endByte
      (successRem 0) successBody (successRem 4)
      [hyphen nameA, hyphen nameC, missing nameA, missing nameC] :=
  .parsed (span 0 1) (span 10 11) opening (successItems _ _)
    (.cons (nameMissing nameA) (.lastRequired (nameMissing nameC)))

private theorem allowParsed (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses NameStatementTraceParses .allow reportSource endByte
      (successRem 0) successBody (successRem 4)
      [hyphen nameA, hyphen nameC, missing nameA] :=
  .parsed (span 0 1) (span 10 11) opening (successItems _ _)
    (.cons (nameMissing nameA) .lastAllowed)

/-- Both name events precede both full-statement termination events, after
every arbitrary prior event. The exact source-order block and endpoint agree. -/
theorem require_names_then_both_semicolons (prior : List ParseDiagnostic) :
    ∃ output, coreBlock checkedNameStatement .require (successState prior) = .ok successBody output ∧
      output.declarativeRemainder = successRem 4 ∧ output.diagnostics =
        prior ++ [hyphen nameA, hyphen nameC, missing nameA, missing nameC] := by
  simpa only [successState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_success_iff checkedNameStatement_success_sound
      checkedNameStatement_success_complete checkedNameStatement_success_context .require
      (input := successState prior)).mp (requireParsed _ _)

/-- Allowing a final expression removes only the last termination event;
both earlier checked-name events and the first missing semicolon remain. -/
theorem allow_names_then_first_semicolon (prior : List ParseDiagnostic) :
    ∃ output, coreBlock checkedNameStatement .allow (successState prior) = .ok successBody output ∧
      output.declarativeRemainder = successRem 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, missing nameA] := by
  simpa only [successState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_success_iff checkedNameStatement_success_sound
      checkedNameStatement_success_complete checkedNameStatement_success_context .allow
      (input := successState prior)).mp (allowParsed _ _)

private def rejectionTokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := nameA.span, value := .identifier nameA.value },
  { span := span 6 7, value := .symbol .plus },
  { span := span 8 9, value := .symbol .rightBrace },
  { span := span 10 14, value := .identifier "tail" }]
private def rejectionRem (endIndex cursor : Nat) : Remainder := { tokens := rejectionTokens, endIndex, cursor }
private def rejectionState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ a-b + } tail" }
  tokens := rejectionTokens, cursor := 0, window := { endIndex := 5, endByte := 14 }
  diagnosticsRev := prior.reverse
}
private def plusReport : ParseDiagnostic := {
  span := span 6 7
  kind := .unexpected (some (.symbol .plus)) { head := .identifier, tail := [] } .statement
}
private def capturedWindow : BalancedBlockCapture := {
  span := span 0 9, endIndex := 4, endByte := 9
}

private theorem rejectionParsed (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 2 < endIndex) :
    CoreBlockTraceRejects NameStatementTraceParses NameStatementTraceRejects policy
      reportSource endByte (rejectionRem endIndex 0) (rejectionRem endIndex 2)
      plusReport [hyphen nameA] := by
  have nameParsed : NameStatementTraceParses reportSource endByte
      (rejectionRem endIndex 1) (nameStatement nameA) (rejectionRem endIndex 2) [hyphen nameA] :=
    .parsed (.parsed ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide)))
  have rejected : NameStatementTraceRejects reportSource endByte
      (rejectionRem endIndex 2) (rejectionRem endIndex 2) plusReport [] :=
    ⟨.absent (by simp [IdentifierAbsentAt, TokenAt, rejectionRem, rejectionTokens]),
      .reported (.token (current := { span := span 6 7, value := .symbol .plus })
        ⟨inside, rfl⟩), rfl⟩
  have last : CoreBlockItemsTraceRejects NameStatementTraceParses NameStatementTraceRejects
      reportSource endByte (rejectionRem endIndex 2) (rejectionRem endIndex 2) plusReport [] :=
    .statementRejected inside
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens]) rejected
  have items : CoreBlockItemsTraceRejects NameStatementTraceParses NameStatementTraceRejects
      reportSource endByte (rejectionRem endIndex 1) (rejectionRem endIndex 2)
      plusReport [hyphen nameA] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens])
      nameParsed (by change 1 < 2; decide) last
  exact .itemsRejected (span 0 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem balancedCapture : BalancedBlockCaptures (rejectionRem 5 0) capturedWindow :=
  .captured (input := rejectionRem 5 0) (openingSpan := span 0 1)
    (closingSpan := span 8 9) ⟨by decide, rfl⟩
    (.other (token := { span := nameA.span, value := .identifier nameA.value })
      ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := { span := span 6 7, value := .symbol .plus })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.close ⟨by decide, rfl⟩)))

/-- Rejecting the plus leaves only the preceding name event under either
tail policy. No semicolon validation or final-report commit has happened. -/
theorem raw_rejection_keeps_only_name_event
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ failure output,
      coreBlock checkedNameStatement policy (rejectionState prior) = .reject failure output ∧
      output.declarativeRemainder = rejectionRem 5 2 ∧ failure.toDiagnostic = plusReport ∧
      output.diagnostics = prior ++ [hyphen nameA] := by
  simpa only [rejectionState, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_reject_iff checkedNameStatement_success_sound checkedNameStatement_reject_sound
      checkedNameStatement_success_complete checkedNameStatement_reject_complete
      checkedNameStatement_success_context policy (input := rejectionState prior)).mp
      (rejectionParsed policy.declarative _ _ 5 (by decide))

/-- Captured rejection emits its report once after the name event, returns an
empty body, restores the full parent window, and leaves `tail` as the next token.
The child's byte boundary is 9 while the parent's remains 14. -/
theorem captured_rejection_preserves_tail
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output,
      isolateBlock (coreBlock checkedNameStatement policy) (rejectionState prior) =
        .ok { span := span 0 9, value := [] } output ∧
      output.declarativeRemainder = rejectionRem 5 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, plusReport] ∧
      output.file = (rejectionState prior).file ∧
      output.window = (rejectionState prior).window ∧
      output.peek? = some { span := span 10 14, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses NameStatementTraceParses policy.declarative)
      (CoreBlockTraceRejects NameStatementTraceParses NameStatementTraceRejects policy.declarative)
      source 14 (rejectionRem 5 0) { span := span 0 9, value := [] }
      (rejectionRem 5 4) [hyphen nameA, plusReport] :=
    .recovered balancedCapture (rejectionParsed policy.declarative source 9 4 (by decide))
  rcases isolateBlock_success_trace_complete
      (coreBlock_trace_success_complete checkedNameStatement_success_complete
        checkedNameStatement_success_context policy)
      (coreBlock_trace_reject_complete checkedNameStatement_success_complete
        checkedNameStatement_reject_complete checkedNameStatement_success_context policy)
      (input := rejectionState prior) parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectionState prior) balancedCapture with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame
    (input := rejectionState prior) captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectionState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens at tokens
    change output.window.endIndex = 5 at endpoint
    change output.cursor = 4 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxBlockIdentifierTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxControlLeafBlockRejectionExamples
/-! Actual control-leaf rejection inside a block. The explicit carrier for
`{ break; break + } tail` distinguishes the first keyword failure from the later
semicolon failure, and tests recovered parent continuation with prior events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafBlockRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "control-block-reject.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def tokens : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := span 2 7, value := .keyword .breakKw },
  { span := span 7 8, value := .symbol .semicolon },
  { span := span 9 14, value := .keyword .breakKw },
  { span := span 15 16, value := .symbol .plus },
  { span := span 17 18, value := .symbol .rightBrace },
  { span := span 19 23, value := .identifier "tail" }]
private def remainder (endIndex cursor : Nat) : Remainder := { tokens, endIndex, cursor }
private def inputState (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ break; break + } tail" }
  tokens, cursor := 0, window := { endIndex := 7, endByte := 23 }
  diagnosticsRev := prior.reverse
}
private def semicolonFailure : Failure := {
  span := span 15 16, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}
private def keywordFailure : Failure := {
  span := span 2 7, found := some (.keyword .breakKw)
  expected := { head := .keyword .continueKw, tail := [] }, context := .statement
}
private def capture : BalancedBlockCapture := { span := span 0 18, endIndex := 6, endByte := 18 }

private theorem firstBreak (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 5 < endIndex) :
    BreakStatementTraceParses reportSource endByte (remainder endIndex 1)
      { span := span 2 8, value := .breakStmt } (remainder endIndex 3) [] :=
  ⟨.parsed (span 2 7) (span 7 8) (afterMarker := remainder endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩

private theorem breakRejected (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 5 < endIndex) :
    CoreBlockTraceRejects BreakStatementTraceParses BreakStatementTraceRejects policy
      reportSource endByte (remainder endIndex 0) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] := by
  have last : BreakStatementTraceRejects reportSource endByte (remainder endIndex 3)
      (remainder endIndex 4) semicolonFailure.toDiagnostic [] :=
    .semicolonMissing (span 9 14) ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (.reported (.token (current := { span := span 15 16, value := .symbol .plus })
        ⟨by change 4 < endIndex; omega, rfl⟩))
  have lastItem : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (remainder endIndex 3) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 3 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens]) last
  have items : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (remainder endIndex 1) (remainder endIndex 4)
      semicolonFailure.toDiagnostic [] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (firstBreak reportSource endByte endIndex inside) (by change 1 < 3; decide) lastItem
  exact .itemsRejected (span 0 1) (afterOpening := remainder endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem continueRejected (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy
      reportSource endByte (remainder 7 0) (remainder 7 1) keywordFailure.toDiagnostic [] := by
  have leaf : ContinueStatementTraceRejects reportSource endByte
      (remainder 7 1) (remainder 7 1) keywordFailure.toDiagnostic [] :=
    .markerMissing (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens])
      (.reported (.token (current := { span := span 2 7, value := .keyword .breakKw })
        ⟨by decide, rfl⟩))
  exact .itemsRejected (span 0 1) (afterOpening := remainder 7 1)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.statementRejected (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens]) leaf)

private theorem balancedCapture : BalancedBlockCaptures (remainder 7 0) capture :=
  .captured (input := remainder 7 0) (openingSpan := span 0 1) (closingSpan := span 17 18)
    ⟨by decide, rfl⟩
    (.other (token := { span := span 2 7, value := .keyword .breakKw })
      ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := { span := span 7 8, value := .symbol .semicolon })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := span 9 14, value := .keyword .breakKw })
          ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := { span := span 15 16, value := .symbol .plus })
            ⟨by decide, rfl⟩ (by decide) (by decide) (.close ⟨by decide, rfl⟩)))))

/-- The real break leaf consumes the first complete statement and the next
keyword, then returns the exact semicolon failure without committing it. -/
theorem break_later_semicolon_failure (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock breakStatement policy (inputState prior) = .reject semicolonFailure output ∧
      output.declarativeRemainder = remainder 7 4 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete breakStatement_success_context
      policy (input := inputState prior)).mp (breakRejected policy.declarative _ _ 7 (by decide))

/-- With the real continue leaf, the same input fails at the first break
keyword, before reaching either semicolon position or the later plus token. -/
theorem continue_keyword_failure_has_priority (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock continueStatement policy (inputState prior) = .reject keywordFailure output ∧
      output.declarativeRemainder = remainder 7 1 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff continueStatement_trace_success_sound continueStatement_trace_reject_sound
      continueStatement_trace_success_complete continueStatement_trace_reject_complete continueStatement_success_context
      policy (input := inputState prior)).mp (continueRejected policy.declarative _ _)

/-- Balanced recovery drops the unfinished body, commits only the semicolon
report once, and restores the byte-23 parent window after the byte-18 child.
All earlier events survive and the following `tail` token remains unread. -/
theorem break_captured_failure_restores_parent
    (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock breakStatement policy) (inputState prior) =
        .ok { span := span 0 18, value := [] } output ∧
      output.declarativeRemainder = remainder 7 6 ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = (inputState prior).file ∧ output.window = (inputState prior).window ∧
      output.peek? = some { span := span 19 23, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses BreakStatementTraceParses policy.declarative)
      (CoreBlockTraceRejects BreakStatementTraceParses BreakStatementTraceRejects policy.declarative)
      source 23 (remainder 7 0) { span := span 0 18, value := [] }
      (remainder 7 6) [semicolonFailure.toDiagnostic] :=
    .recovered balancedCapture (breakRejected policy.declarative source 18 6 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff (statement := breakStatement)
      breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete
      breakStatement_success_context policy (input := inputState prior)).mp parsed with
    ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := inputState prior) balancedCapture with
    ⟨captured, capturedResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame capturedResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [inputState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have carrier := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = tokens at carrier
    change output.window.endIndex = 7 at endpoint
    change output.cursor = 6 at cursor
    simp only [State.peek?, carrier, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxControlLeafBlockRejectionExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxControlLeafBlockTraceExamples
/-! Actual break/continue leaves consume two complete statements inside a raw
or isolated block. Explicit token fixtures preserve exact spans, full prior
diagnostics, and the following parent token; no lexer evaluation is assumed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "control-block-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def pairTokens (marker : HardKeyword) (width : Nat) : Array Token := #[
  { span := span 0 1, value := .symbol .leftBrace },
  { span := span 2 (2 + width), value := .keyword marker },
  { span := span (2 + width) (3 + width), value := .symbol .semicolon },
  { span := span (4 + width) (4 + 2 * width), value := .keyword marker },
  { span := span (4 + 2 * width) (5 + 2 * width), value := .symbol .semicolon },
  { span := span (6 + 2 * width) (7 + 2 * width), value := .symbol .rightBrace },
  { span := span (8 + 2 * width) (12 + 2 * width), value := .identifier "tail" }]
private def pairRem (marker : HardKeyword) (width endIndex cursor : Nat) : Remainder := {
  tokens := pairTokens marker width, endIndex, cursor
}
private def pairState (marker : HardKeyword) (width : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "{ " ++ marker.spelling ++ "; " ++ marker.spelling ++ "; } tail" }
  tokens := pairTokens marker width, cursor := 0
  window := { endIndex := 7, endByte := 12 + 2 * width }, diagnosticsRev := prior.reverse
}
private def pairBody (value : StatementValue) (width : Nat) : Block := {
  span := span 0 (7 + 2 * width)
  value := [{ span := span 2 (3 + width), value },
    { span := span (4 + width) (5 + 2 * width), value }]
}

private theorem pairParsed (marker : HardKeyword) (value : StatementValue)
    (width endIndex : Nat) (inside : 5 < endIndex) (policy : CoreBlockTailPolicy)
    (terminated : ∀ location, CoreBlockStatementTerminated { span := location, value })
    (reportSource : SourceId) (endByte : Nat) :
    CoreBlockTraceParses (TerminatedControlStatementTraceParses marker value) policy
      reportSource endByte (pairRem marker width endIndex 0) (pairBody value width)
      (pairRem marker width endIndex 6) [] := by
  have first : TerminatedControlStatementTraceParses marker value reportSource endByte
      (pairRem marker width endIndex 1) { span := span 2 (3 + width), value }
      (pairRem marker width endIndex 3) [] :=
    ⟨.parsed (span 2 (2 + width)) (span (2 + width) (3 + width))
      (afterMarker := pairRem marker width endIndex 2)
      ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have second : TerminatedControlStatementTraceParses marker value reportSource endByte
      (pairRem marker width endIndex 3) { span := span (4 + width) (5 + 2 * width), value }
      (pairRem marker width endIndex 5) [] :=
    ⟨.parsed (span (4 + width) (4 + 2 * width)) (span (4 + 2 * width) (5 + 2 * width))
      (afterMarker := pairRem marker width endIndex 4)
      ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 5) []
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 3)
      [{ span := span (4 + width) (5 + 2 * width), value }]
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .next (by change 3 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, pairRem, pairTokens]) second
      (by change 3 < 5; decide) closing
  have items : CoreBlockItemsTraceParses (TerminatedControlStatementTraceParses marker value)
      reportSource endByte (pairRem marker width endIndex 1) (pairBody value width).value
      (span (6 + 2 * width) (7 + 2 * width)) (pairRem marker width endIndex 6) [] :=
    .next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, pairRem, pairTokens]) first
      (by change 1 < 3; decide) last
  have tails : CoreBlockTailsDiagnosticTrace policy (pairBody value width).value [] := by
    cases policy with
    | allow => exact .cons (.clean (terminated _)) .lastAllowed
    | require => exact .cons (.clean (terminated _)) (.lastRequired (.clean (terminated _)))
  exact .parsed (span 0 1) (span (6 + 2 * width) (7 + 2 * width))
    (afterOpening := pairRem marker width endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items tails

private def pairCapture (width : Nat) : BalancedBlockCapture := {
  span := span 0 (7 + 2 * width), endIndex := 6, endByte := 7 + 2 * width
}

private theorem pairCaptured (marker : HardKeyword) (width : Nat) :
    BalancedBlockCaptures (pairRem marker width 7 0) (pairCapture width) :=
  .captured (input := pairRem marker width 7 0) (openingSpan := span 0 1)
    (closingSpan := span (6 + 2 * width) (7 + 2 * width)) ⟨by change 0 < 7; decide, rfl⟩
    (.other (token := { span := span 2 (2 + width), value := .keyword marker })
      ⟨by change 1 < 7; decide, rfl⟩ (by simp) (by simp)
      (.other (token := { span := span (2 + width) (3 + width), value := .symbol .semicolon })
        ⟨by change 2 < 7; decide, rfl⟩ (by simp) (by simp)
        (.other (token := { span := span (4 + width) (4 + 2 * width), value := .keyword marker })
          ⟨by change 3 < 7; decide, rfl⟩ (by simp) (by simp)
          (.other (token := { span := span (4 + 2 * width) (5 + 2 * width), value := .symbol .semicolon })
            ⟨by change 4 < 7; decide, rfl⟩ (by simp) (by simp)
            (.close ⟨by change 5 < 7; decide, rfl⟩)))))

/-- Two actual break statements retain full spans and every prior diagnostic
under either tail policy, and stop before the parent token following the block. -/
theorem break_pair_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock breakStatement policy (pairState .breakKw 5 prior) =
        .ok (pairBody .breakStmt 5) output ∧
      output.declarativeRemainder = pairRem .breakKw 5 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff breakStatement_trace_success_sound breakStatement_trace_success_complete
      breakStatement_success_context policy (input := pairState .breakKw 5 prior)).mp
      (pairParsed .breakKw .breakStmt 5 7 (by decide) policy.declarative (fun _ => trivial) _ _)

theorem continue_pair_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock continueStatement policy (pairState .continueKw 8 prior) =
        .ok (pairBody .continueStmt 8) output ∧
      output.declarativeRemainder = pairRem .continueKw 8 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff continueStatement_trace_success_sound
      continueStatement_trace_success_complete continueStatement_success_context policy
      (input := pairState .continueKw 8 prior)).mp
      (pairParsed .continueKw .continueStmt 8 7 (by decide) policy.declarative (fun _ => trivial) _ _)

/-- Captured success uses a child ending at byte 17 and resumes after its
closing token, retaining the original seven-token parent carrier. -/
theorem break_pair_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock breakStatement policy) (pairState .breakKw 5 prior) =
        .ok (pairBody .breakStmt 5) output ∧
      output.declarativeRemainder = pairRem .breakKw 5 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil,
    pairRem, pairCapture, BalancedBlockCapture.parentRemainder, State.declarativeRemainder] using
    (isolatedCoreBlock_trace_success_iff (statement := breakStatement)
      breakStatement_trace_success_sound breakStatement_trace_reject_sound
      breakStatement_trace_success_complete breakStatement_trace_reject_complete
      breakStatement_success_context policy (input := pairState .breakKw 5 prior)).mp
      (.captured (pairCaptured .breakKw 5)
        (pairParsed .breakKw .breakStmt 5 6 (by decide) policy.declarative (fun _ => trivial) _ _))

theorem continue_pair_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock continueStatement policy) (pairState .continueKw 8 prior) =
        .ok (pairBody .continueStmt 8) output ∧
      output.declarativeRemainder = pairRem .continueKw 8 7 6 ∧ output.diagnostics = prior := by
  simpa only [pairState, State.diagnostics, List.reverse_reverse, List.append_nil,
    pairRem, pairCapture, BalancedBlockCapture.parentRemainder, State.declarativeRemainder] using
    (isolatedCoreBlock_trace_success_iff (statement := continueStatement)
      continueStatement_trace_success_sound continueStatement_trace_reject_sound
      continueStatement_trace_success_complete continueStatement_trace_reject_complete
      continueStatement_success_context policy (input := pairState .continueKw 8 prior)).mp
      (.captured (pairCaptured .continueKw 8)
        (pairParsed .continueKw .continueStmt 8 6 (by decide) policy.declarative (fun _ => trivial) _ _))

end Solcore.Test.SyntaxControlLeafBlockTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxControlLeafTraceExactnessProperties
/-! Independent totality and joint exactness consumers for concrete control
leaves, including malformed token carriers and recovered block results. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxControlLeafTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

/-- Every incoming state has a silent ordinary leaf outcome; in particular,
there is no validity or diagnostic-free premise hiding invariant cases. -/
theorem every_control_leaf_has_silent_outcome
    (keywordValue : HardKeyword) (statementValue : StatementValue) (input : State) :
    (∃ statement output,
      ControlInternals.terminatedControl keywordValue statementValue input = .ok statement output ∧
      output.diagnostics = input.diagnostics) ∨
    (∃ failure rejected,
      ControlInternals.terminatedControl keywordValue statementValue input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics) := by
  rcases terminatedControlStatementTrace_exists_outcome keywordValue statementValue
      input.file.id input.window.endByte input.declarativeRemainder with successful | rejected
  · rcases successful with ⟨statement, after, parsed⟩
    rcases (ControlInternals.terminatedControl_trace_success_iff keywordValue statementValue).mp
        parsed with ⟨output, result, _, diagnostics⟩
    exact Or.inl ⟨statement, output, result, by simpa only [List.append_nil] using diagnostics⟩
  · rcases rejected with ⟨after, diagnostic, traced⟩
    rcases (ControlInternals.terminatedControl_trace_reject_iff keywordValue statementValue).mp
        traced with ⟨failure, rejected, result, _, _, diagnostics⟩
    exact Or.inr ⟨failure, rejected, result, by simpa only [List.append_nil] using diagnostics⟩

theorem break_rejection_excludes_all_success_traces
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : BreakStatementTraceRejects source endByte input rejected report trace) :
    ¬ ∃ statement output events, BreakStatementTraceParses source endByte
      input statement output events :=
  (breakStatementTraceExactOutcomeSpec source endByte).successRejectDisjoint rejection

/-- A missing slot inside an oversized window reports the explicit window
byte boundary without consuming a token or discarding incoming diagnostics. -/
theorem missing_array_slot_reports_break_at_window_byte
    {input : State} (inside : input.cursor < input.window.endIndex)
    (missing : input.tokens[input.cursor]? = none) :
    ∃ rejected, breakStatement input = .reject {
        span := { source := input.file.id
                  startByte := input.window.endByte
                  endByte := input.window.endByte },
        found := none, expected := { head := .keyword .breakKw, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = input.declarativeRemainder ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.keyword .breakKw) := by
    rintro ⟨span, _, present⟩
    simp only [missing] at present
    cases present
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.markerMissing absent (.reported (.missingToken inside missing)))

/-- Recovery does not introduce ambiguity in restricted continue blocks:
the AST, resumed parent remainder, and complete event list all stay unique. -/
theorem isolated_continue_block_trace_is_unique
    (policy : CoreBlockTailPolicy) {source : SourceId} {endByte : Nat}
    {input afterLeft afterRight : Remainder} {left right : Block}
    {leftTrace rightTrace : List ParseDiagnostic}
    (leftParsed : IsolatedBlockTraceParses (CoreBlockTraceParses ContinueStatementTraceParses policy)
      (CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy)
      source endByte input left afterLeft leftTrace)
    (rightParsed : IsolatedBlockTraceParses (CoreBlockTraceParses ContinueStatementTraceParses policy)
      (CoreBlockTraceRejects ContinueStatementTraceParses ContinueStatementTraceRejects policy)
      source endByte input right afterRight rightTrace) :
    left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace :=
  (isolatedTerminatedControlCoreBlockTraceExactOutcomeSpec .continueKw .continueStmt
    policy source endByte).successResultUnique leftParsed rightParsed

end Solcore.Test.SyntaxControlLeafTraceExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples
/-! Actual checked identifier expressions in a restricted return-only block.
The canonical lexer fixtures alone use kernel decision; parser results follow
independent trace derivations. No general expression/statement claim is made. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "identifier-return-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def marker (offset : Nat) : Token := { span := span offset (offset + 6), value := .keyword .returnKw }
def nameA : Identifier := { span := span 9 12, value := "a-b" }
def nameC : Identifier := { span := span 21 24, value := "c-d" }
def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}

theorem name_trace {input : Remainder} (name : Identifier)
    (reportSource : SourceId) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    IdentifierExpressionTraceParses reportSource endByte input (nameExpr name)
      { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := TokenAt.token_unique token other <;> cases impossible
  exact .parsed (.identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling)))

def successText : String := "{ return a-b; return c-d; } tail"
def successTokens : List Token := [
  { span := span 0 1, value := .symbol .leftBrace }, marker 2, nameToken nameA,
  { span := span 12 13, value := .symbol .semicolon }, marker 14, nameToken nameC,
  { span := span 24 25, value := .symbol .semicolon },
  { span := span 26 27, value := .symbol .rightBrace },
  { span := span 28 32, value := .identifier "tail" }]
def successRem (endIndex cursor : Nat) : Remainder := { tokens := successTokens.toArray, endIndex, cursor }
def successState (prior : List ParseDiagnostic) : State := initial successText successTokens prior
def firstReturn : Statement := { span := span 2 13, value := .returnStmt (some (nameExpr nameA)) }
def lastReturn : Statement := { span := span 14 25, value := .returnStmt (some (nameExpr nameC)) }
def successBody : Block := { span := span 0 27, value := [firstReturn, lastReturn] }

private theorem firstParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 7 < endIndex) :
    ReturnStatementTraceParses IdentifierExpressionTraceParses reportSource endByte
      (successRem endIndex 1) firstReturn (successRem endIndex 4) [hyphen nameA] :=
  .parsed (span 2 8) (span 12 13)
    (afterMarker := successRem endIndex 2) (afterValue := successRem endIndex 3)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens, nameToken])
      (name_trace nameA reportSource endByte ⟨by change 2 < endIndex; omega, rfl⟩ (by
        unfold IdentifierHyphenSpelling nameA; decide)))
    ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩

private theorem lastParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 7 < endIndex) :
    ReturnStatementTraceParses IdentifierExpressionTraceParses reportSource endByte
      (successRem endIndex 4) lastReturn (successRem endIndex 7) [hyphen nameC] :=
  .parsed (span 14 20) (span 24 25)
    (afterMarker := successRem endIndex 5) (afterValue := successRem endIndex 6)
    ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens, nameToken])
      (name_trace nameC reportSource endByte ⟨by change 5 < endIndex; omega, rfl⟩ (by
        unfold IdentifierHyphenSpelling nameC; decide)))
    ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩

private theorem successParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 7 < endIndex) (policy : CoreBlockTailPolicy) :
    CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses) policy
      reportSource endByte (successRem endIndex 0) successBody (successRem endIndex 8)
      [hyphen nameA, hyphen nameC] := by
  have closing : CoreBlockItemsTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      reportSource endByte (successRem endIndex 7) [] (span 26 27) (successRem endIndex 8) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      reportSource endByte (successRem endIndex 4) [lastReturn] (span 26 27)
      (successRem endIndex 8) [hyphen nameC] :=
    .next (by change 4 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens, marker])
      (lastParsed reportSource endByte endIndex inside) (by change 4 < 7; decide) closing
  have items : CoreBlockItemsTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      reportSource endByte (successRem endIndex 1) [firstReturn, lastReturn] (span 26 27)
      (successRem endIndex 8) [hyphen nameA, hyphen nameC] :=
    .next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, successRem, successTokens, marker])
      (firstParsed reportSource endByte endIndex inside) (by change 1 < 4; decide) last
  have tails : CoreBlockTailsDiagnosticTrace policy [firstReturn, lastReturn] [] := by
    have firstClean : CoreBlockStatementDiagnosticTrace firstReturn [] := .clean trivial
    have lastClean : CoreBlockStatementDiagnosticTrace lastReturn [] := .clean trivial
    cases policy with
    | allow => exact .cons firstClean .lastAllowed
    | require => exact .cons firstClean (.lastRequired lastClean)
  exact .parsed (span 0 1) (span 26 27) (afterOpening := successRem endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items tails

private def capture : BalancedBlockCapture := { span := span 0 27, endIndex := 8, endByte := 27 }

private theorem successCaptured : BalancedBlockCaptures (successRem 9 0) capture :=
  .captured (input := successRem 9 0) (openingSpan := span 0 1) (closingSpan := span 26 27)
    ⟨by decide, rfl⟩
    (.other (token := marker 2) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := span 12 13, value := .symbol .semicolon })
          ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := marker 14) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := nameToken nameC) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.other (token := { span := span 24 25, value := .symbol .semicolon })
                ⟨by decide, rfl⟩ (by decide) (by decide) (.close ⟨by decide, rfl⟩)))))))

/-- Return statements add no tail constraint events under either policy:
only the two located name events follow every prior event, in source order. -/
theorem name_returns_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (returnStatement identifierExpression) policy (successState prior) =
        .ok successBody output ∧ output.declarativeRemainder = successRem 9 8 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] := by
  simpa only [successState, initial, State.initial, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_success_iff (returnStatement_trace_success_sound identifierExpression_trace_success_sound)
      (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
      (returnStatement_success_context identifierExpression_success_context) policy
      (input := successState prior)).mp (successParsed source 32 9 (by decide) policy.declarative)

/-- Isolation preserves the same AST/events, restores the complete parent
context, and leaves the following token unread (child endByte 27, parent 32). -/
theorem name_returns_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (returnStatement identifierExpression) policy) (successState prior) =
        .ok successBody output ∧ output.declarativeRemainder = successRem 9 8 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = (successState prior).file ∧ output.window = (successState prior).window ∧
      output.peek? = some { span := span 28 32, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
        (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects) policy.declarative)
      source 32 (successRem 9 0) successBody (successRem 9 8) [hyphen nameA, hyphen nameC] :=
    .captured successCaptured (successParsed source 27 8 (by decide) policy.declarative)
  rcases isolateBlock_success_trace_complete
      (coreBlock_trace_success_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (coreBlock_trace_reject_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_trace_reject_complete identifierExpression_trace_success_complete
          identifierExpression_trace_reject_complete identifierExpression_success_context)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (input := successState prior) parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := successState prior) successCaptured with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [successState, initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = successTokens.toArray at tokens
    change output.window.endIndex = 9 at endpoint
    change output.cursor = 8 at cursor
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

end Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxIdentifierReturnBlockRejectionTraceExamples
/-! An actual checked identifier expression succeeds before its return's
mandatory semicolon rejects. Canonical lexing and independent trace derivations
keep the name event separate from the final report and isolation commit. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxIdentifierReturnBlockRejectionTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxIdentifierReturnBlockTraceExamples

def rejectionText : String := "{ return a-b + } tail"
def rejectionTokens : List Token := [
  { span := span 0 1, value := .symbol .leftBrace }, marker 2, nameToken nameA,
  { span := span 13 14, value := .symbol .plus },
  { span := span 15 16, value := .symbol .rightBrace },
  { span := span 17 21, value := .identifier "tail" }]
def rejectionRem (endIndex cursor : Nat) : Remainder := { tokens := rejectionTokens.toArray, endIndex, cursor }
def rejectionState (prior : List ParseDiagnostic) : State := initial rejectionText rejectionTokens prior
def semicolonFailure : Failure := {
  span := span 13 14, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}

private theorem rejectionParsed (policy : CoreBlockTailPolicy)
    (reportSource : SourceId) (endByte endIndex : Nat) (inside : 3 < endIndex) :
    CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects) policy
      reportSource endByte (rejectionRem endIndex 0) (rejectionRem endIndex 3)
      semicolonFailure.toDiagnostic [hyphen nameA] := by
  have rejected : ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      reportSource endByte (rejectionRem endIndex 1) (rejectionRem endIndex 3)
      semicolonFailure.toDiagnostic [hyphen nameA] :=
    .semicolonRejected (span 2 8)
      (afterMarker := rejectionRem endIndex 2) (afterValue := rejectionRem endIndex 3)
      ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
      (.present (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens, nameToken])
        (name_trace nameA reportSource endByte ⟨by change 2 < endIndex; omega, rfl⟩ (by
          unfold IdentifierHyphenSpelling nameA; decide)))
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens])
      (.reported (.token (current := { span := span 13 14, value := .symbol .plus }) ⟨inside, rfl⟩))
  exact .itemsRejected (span 0 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩
    (.statementRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, rejectionRem, rejectionTokens, marker]) rejected)

private def capture : BalancedBlockCapture := { span := span 0 16, endIndex := 5, endByte := 16 }

private theorem rejectionCaptured : BalancedBlockCaptures (rejectionRem 6 0) capture :=
  .captured (input := rejectionRem 6 0) (openingSpan := span 0 1) (closingSpan := span 15 16)
    ⟨by decide, rfl⟩
    (.other (token := marker 2) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := nameToken nameA) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := span 13 14, value := .symbol .plus })
          ⟨by decide, rfl⟩ (by decide) (by decide) (.close ⟨by decide, rfl⟩))))

/-- The exact semicolon failure is still uncommitted. Only the successful
name's event follows prior events; neither tail validation nor recovery ran. -/
theorem name_return_rejection_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (returnStatement identifierExpression) policy (rejectionState prior) =
        .reject semicolonFailure output ∧ output.declarativeRemainder = rejectionRem 6 3 ∧
      output.diagnostics = prior ++ [hyphen nameA] := by
  simpa only [rejectionState, initial, State.initial, State.diagnostics, List.reverse_reverse] using
    (coreBlock_trace_reject_failure_iff
      (returnStatement_trace_success_sound identifierExpression_trace_success_sound)
      (returnStatement_reject_trace_sound identifierExpression_trace_success_sound
        identifierExpression_trace_reject_sound identifierExpression_success_context)
      (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
      (returnStatement_trace_reject_complete identifierExpression_trace_success_complete
        identifierExpression_trace_reject_complete identifierExpression_success_context)
      (returnStatement_success_context identifierExpression_success_context) policy
      (input := rejectionState prior)).mp (rejectionParsed policy.declarative source 21 6 (by decide))

/-- One isolation commits exactly one report after the name event and returns
the captured empty block. The child byte boundary is 16, parent 21; `tail` remains
unread with the complete parent file/window restored. -/
theorem name_return_rejection_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (returnStatement identifierExpression) policy) (rejectionState prior) =
        .ok { span := span 0 16, value := [] } output ∧
      output.declarativeRemainder = rejectionRem 6 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, semicolonFailure.toDiagnostic] ∧
      output.file = (rejectionState prior).file ∧ output.window = (rejectionState prior).window ∧
      output.peek? = some { span := span 17 21, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
        (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects) policy.declarative)
      source 21 (rejectionRem 6 0) { span := span 0 16, value := [] } (rejectionRem 6 5)
      [hyphen nameA, semicolonFailure.toDiagnostic] :=
    .recovered rejectionCaptured (rejectionParsed policy.declarative source 16 5 (by decide))
  rcases isolateBlock_success_trace_complete
      (coreBlock_trace_success_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (coreBlock_trace_reject_complete (returnStatement_trace_success_complete identifierExpression_trace_success_complete)
        (returnStatement_trace_reject_complete identifierExpression_trace_success_complete
          identifierExpression_trace_reject_complete identifierExpression_success_context)
        (returnStatement_success_context identifierExpression_success_context) policy)
      (input := rejectionState prior) parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectionState prior) rejectionCaptured with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectionState, initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 6 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxIdentifierReturnBlockRejectionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxNestedBreakBlockTraceExamples
/-! Two nonempty nested block statements are composed from the actual break
leaf's five trace contracts. Explicit tokens exercise exact nested ASTs and
parent continuation without evaluating a whole parser by decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNestedBreakBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

abbrev innerTrace := BlockStatementTraceParses BreakStatementTraceParses
abbrev innerRejects := BlockStatementTraceRejects BreakStatementTraceParses BreakStatementTraceRejects

theorem inner_success_sound : StatementTraceSuccessSound (blockStatement breakStatement) innerTrace :=
  blockStatement_trace_success_sound breakStatement_trace_success_sound breakStatement_success_context
theorem inner_success_complete : StatementTraceSuccessComplete (blockStatement breakStatement) innerTrace :=
  blockStatement_trace_success_complete breakStatement_trace_success_complete breakStatement_success_context
theorem inner_success_context : StatementSuccessContext (blockStatement breakStatement) :=
  blockStatement_success_context breakStatement_success_context
theorem inner_reject_sound : StatementTraceRejectSound (blockStatement breakStatement) innerRejects :=
  blockStatement_trace_reject_sound breakStatement_trace_success_sound
    breakStatement_trace_reject_sound breakStatement_success_context
theorem inner_reject_complete : StatementTraceRejectComplete (blockStatement breakStatement) innerRejects :=
  blockStatement_trace_reject_complete breakStatement_trace_success_complete
    breakStatement_trace_reject_complete breakStatement_success_context

def source : SourceId := { origin := .main, path := "nested-break-trace.sol" }
def byteSpan (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def nestedTokens (secondTerminator : Symbol) : Array Token := #[
  { span := byteSpan 0 1, value := .symbol .leftBrace },
  { span := byteSpan 2 3, value := .symbol .leftBrace },
  { span := byteSpan 4 9, value := .keyword .breakKw },
  { span := byteSpan 9 10, value := .symbol .semicolon },
  { span := byteSpan 11 12, value := .symbol .rightBrace },
  { span := byteSpan 13 14, value := .symbol .leftBrace },
  { span := byteSpan 15 20, value := .keyword .breakKw },
  { span := byteSpan 20 21, value := .symbol secondTerminator },
  { span := byteSpan 22 23, value := .symbol .rightBrace },
  { span := byteSpan 24 25, value := .symbol .rightBrace },
  { span := byteSpan 26 30, value := .identifier "tail" }]
def atCursor (secondTerminator : Symbol) (endIndex cursor : Nat) : Remainder := {
  tokens := nestedTokens secondTerminator, endIndex, cursor
}
def inputState (content : String) (secondTerminator : Symbol) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content }, tokens := nestedTokens secondTerminator
  cursor := 0, window := { endIndex := 11, endByte := 30 }, diagnosticsRev := prior.reverse
}
def leftBreak : Statement := { span := byteSpan 4 10, value := .breakStmt }
def rightBreak : Statement := { span := byteSpan 15 21, value := .breakStmt }
def leftInner : Statement := { span := byteSpan 2 12, value := .block [leftBreak] }
def rightInner : Statement := { span := byteSpan 13 23, value := .block [rightBreak] }
def outerBody : Block := { span := byteSpan 0 25, value := [leftInner, rightInner] }

theorem left_inner_trace (secondTerminator : Symbol) (reportSource : SourceId)
    (endByte endIndex : Nat) (inside : 9 < endIndex) :
    innerTrace reportSource endByte (atCursor secondTerminator endIndex 1)
      leftInner (atCursor secondTerminator endIndex 5) [] := by
  have leaf : BreakStatementTraceParses reportSource endByte (atCursor secondTerminator endIndex 2)
      leftBreak (atCursor secondTerminator endIndex 4) [] :=
    ⟨.parsed (byteSpan 4 9) (byteSpan 9 10) (afterMarker := atCursor secondTerminator endIndex 3)
      ⟨⟨by change 2 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses BreakStatementTraceParses reportSource endByte
      (atCursor secondTerminator endIndex 4) [] (byteSpan 11 12)
      (atCursor secondTerminator endIndex 5) [] := .close _ ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
  exact .parsed (.parsed (byteSpan 2 3) (byteSpan 11 12)
    (afterOpening := atCursor secondTerminator endIndex 2)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.next (by change 2 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
      (by change 2 < 4; decide) closing)
    (.lastRequired (.clean (statement := leftBreak) trivial)))

private theorem right_inner_trace (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    innerTrace reportSource endByte (atCursor .semicolon endIndex 5)
      rightInner (atCursor .semicolon endIndex 9) [] := by
  have leaf : BreakStatementTraceParses reportSource endByte (atCursor .semicolon endIndex 6)
      rightBreak (atCursor .semicolon endIndex 8) [] :=
    ⟨.parsed (byteSpan 15 20) (byteSpan 20 21) (afterMarker := atCursor .semicolon endIndex 7)
      ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩
      ⟨⟨by change 7 < endIndex; omega, rfl⟩, rfl⟩, rfl⟩
  have closing : CoreBlockItemsTraceParses BreakStatementTraceParses reportSource endByte
      (atCursor .semicolon endIndex 8) [] (byteSpan 22 23) (atCursor .semicolon endIndex 9) [] :=
    .close _ ⟨⟨by change 8 < endIndex; omega, rfl⟩, rfl⟩
  exact .parsed (.parsed (byteSpan 13 14) (byteSpan 22 23)
    (afterOpening := atCursor .semicolon endIndex 6)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩
    (.next (by change 6 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
      (by change 6 < 8; decide) closing)
    (.lastRequired (.clean (statement := rightBreak) trivial)))

private theorem outer_trace : CoreBlockTraceParses innerTrace .require source 30
    (atCursor .semicolon 11 0) outerBody (atCursor .semicolon 11 10) [] := by
  have closing : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 9)
      [] (byteSpan 24 25) (atCursor .semicolon 11 10) [] := .close _ ⟨⟨by decide, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 5)
      [rightInner] (byteSpan 24 25) (atCursor .semicolon 11 10) [] :=
    .next (by decide) (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (right_inner_trace source 30 11 (by decide)) (by decide) closing
  have items : CoreBlockItemsTraceParses innerTrace source 30 (atCursor .semicolon 11 1)
      [leftInner, rightInner] (byteSpan 24 25) (atCursor .semicolon 11 10) [] :=
    .next (by decide) (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (left_inner_trace .semicolon source 30 11 (by decide)) (by decide) last
  exact .parsed (byteSpan 0 1) (byteSpan 24 25) (afterOpening := atCursor .semicolon 11 1)
    ⟨⟨by decide, rfl⟩, rfl⟩ items
    (.cons (.clean (statement := leftInner) trivial) (.lastRequired (.clean (statement := rightInner) trivial)))

/-- Two actual nested block statements retain all nested spans and written
order. The raw outer block stops at `tail`, with no new diagnostic event. -/
theorem nested_raw_success (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require
        (inputState "{ { break; } { break; } } tail" .semicolon prior) = .ok outerBody output ∧
      output.declarativeRemainder = atCursor .semicolon 11 10 ∧ output.diagnostics = prior := by
  simpa only [inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff inner_success_sound inner_success_complete inner_success_context .require
      (input := inputState "{ { break; } { break; } } tail" .semicolon prior)).mp outer_trace

/-- Adding the outer statement wrapper preserves the same full output state,
while mapping the complete two-inner-block body into one outer block statement. -/
theorem nested_statement_success (prior : List ParseDiagnostic) :
    ∃ output, blockStatement (blockStatement breakStatement)
        (inputState "{ { break; } { break; } } tail" .semicolon prior) =
        .ok { span := outerBody.span, value := .block outerBody.value } output ∧
      output.declarativeRemainder = atCursor .semicolon 11 10 ∧ output.diagnostics = prior ∧
      output.file = (inputState "{ { break; } { break; } } tail" .semicolon prior).file ∧
      output.window = { endIndex := 11, endByte := 30 } ∧
      output.peek? = some { span := byteSpan 26 30, value := .identifier "tail" } := by
  rcases nested_raw_success prior with ⟨output, raw, after, diagnostics⟩
  have result := blockStatement_success_iff_raw.mpr ⟨outerBody, raw, rfl⟩
  have frame := blockStatement_success_context inner_success_context result
  refine ⟨output, result, after, diagnostics, frame.1, frame.2, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = nestedTokens .semicolon at tokens
  change output.window.endIndex = 11 at endpoint
  change output.cursor = 10 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

end Solcore.Test.SyntaxNestedBreakBlockTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxNestedBreakBlockRejectionExamples
/-! The second nested break rejects at its plus token. Both statement wrappers
propagate that raw failure; one outer isolation recovers exactly once. The
explicit balanced scan crosses two nested brace pairs before restoring `tail`. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNestedBreakBlockRejectionExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxNestedBreakBlockTraceExamples

private def rejectedInput (prior : List ParseDiagnostic) : State :=
  inputState "{ { break; } { break+ } } tail" .plus prior
private def semicolonFailure : Failure := {
  span := byteSpan 20 21, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}
private def capture : BalancedBlockCapture := {
  span := byteSpan 0 25, endIndex := 10, endByte := 25
}

private theorem right_inner_rejected (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    innerRejects reportSource endByte (atCursor .plus endIndex 5)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] := by
  have leaf : BreakStatementTraceRejects reportSource endByte (atCursor .plus endIndex 6)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .semicolonMissing (byteSpan 15 20)
      ⟨⟨by change 6 < endIndex; omega, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (.reported (.token (current := { span := byteSpan 20 21, value := .symbol .plus })
        ⟨by change 7 < endIndex; omega, rfl⟩))
  have item : CoreBlockItemsTraceRejects BreakStatementTraceParses BreakStatementTraceRejects
      reportSource endByte (atCursor .plus endIndex 6)
      (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 6 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens]) leaf
  exact .rejected (.itemsRejected (byteSpan 13 14) (afterOpening := atCursor .plus endIndex 6)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩ item)

private theorem outer_rejected (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 9 < endIndex) :
    CoreBlockTraceRejects innerTrace innerRejects .require reportSource endByte
      (atCursor .plus endIndex 0) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] := by
  have last : CoreBlockItemsTraceRejects innerTrace innerRejects reportSource endByte
      (atCursor .plus endIndex 5) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .statementRejected (by change 5 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (right_inner_rejected reportSource endByte endIndex inside)
  have items : CoreBlockItemsTraceRejects innerTrace innerRejects reportSource endByte
      (atCursor .plus endIndex 1) (atCursor .plus endIndex 7) semicolonFailure.toDiagnostic [] :=
    .laterRejected (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, atCursor, nestedTokens])
      (left_inner_trace .plus reportSource endByte endIndex inside) (by change 1 < 5; decide) last
  exact .itemsRejected (byteSpan 0 1) (afterOpening := atCursor .plus endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items

private theorem balanced_capture : BalancedBlockCaptures (atCursor .plus 11 0) capture :=
  .captured (input := atCursor .plus 11 0) (openingSpan := byteSpan 0 1)
    (closingSpan := byteSpan 24 25) ⟨by decide, rfl⟩
    (.opening (openingSpan := byteSpan 2 3) ⟨by decide, rfl⟩
      (.other (token := { span := byteSpan 4 9, value := .keyword .breakKw })
        ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := { span := byteSpan 9 10, value := .symbol .semicolon })
          ⟨by decide, rfl⟩ (by decide) (by decide)
          (.nestedClosing (nestedSpan := byteSpan 11 12) ⟨by decide, rfl⟩
            (.opening (openingSpan := byteSpan 13 14) ⟨by decide, rfl⟩
              (.other (token := { span := byteSpan 15 20, value := .keyword .breakKw })
                ⟨by decide, rfl⟩ (by decide) (by decide)
                (.other (token := { span := byteSpan 20 21, value := .symbol .plus })
                  ⟨by decide, rfl⟩ (by decide) (by decide)
                  (.nestedClosing (nestedSpan := byteSpan 22 23) ⟨by decide, rfl⟩
                    (.close ⟨by decide, rfl⟩)))))))))

/-- The actual inner statement has no isolation: the second break's missing
semicolon escapes both raw blocks at cursor 7, without committing its report. -/
theorem nested_raw_rejects_at_inner_plus (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require (rejectedInput prior) =
        .reject semicolonFailure output ∧
      output.declarativeRemainder = atCursor .plus 11 7 ∧ output.diagnostics = prior := by
  simpa only [rejectedInput, inputState, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_reject_failure_iff inner_success_sound inner_reject_sound
      inner_success_complete inner_reject_complete inner_success_context .require
      (input := rejectedInput prior)).mp (outer_rejected source 30 11 (by decide))

/-- A second statement wrapper retains the identical failure and full output
state. Neither nested closing brace nor the outer closing brace is consumed. -/
theorem nested_statement_rejects_without_skipping (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (blockStatement breakStatement) .require (rejectedInput prior) =
        .reject semicolonFailure output ∧
      blockStatement (blockStatement breakStatement) (rejectedInput prior) =
        .reject semicolonFailure output ∧
      output.declarativeRemainder = atCursor .plus 11 7 ∧ output.diagnostics = prior ∧
      output.peek? = some { span := byteSpan 20 21, value := .symbol .plus } := by
  rcases nested_raw_rejects_at_inner_plus prior with ⟨output, raw, after, diagnostics⟩
  refine ⟨output, raw, blockStatement_reject_iff_raw.mpr raw, after, diagnostics, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = nestedTokens .plus at tokens
  change output.window.endIndex = 11 at endpoint
  change output.cursor = 7 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

/-- Only the outer wrapper isolates. It drops the unfinished nested body and
appends one report, restoring the byte-30 parent after its byte-25 child window. -/
theorem one_outer_isolation_recovers_once (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (blockStatement breakStatement) .require) (rejectedInput prior) =
        .ok { span := byteSpan 0 25, value := [] } output ∧
      output.declarativeRemainder = atCursor .plus 11 10 ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = (rejectedInput prior).file ∧ output.window = (rejectedInput prior).window ∧
      output.peek? = some { span := byteSpan 26 30, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses (CoreBlockTraceParses innerTrace .require)
      (CoreBlockTraceRejects innerTrace innerRejects .require) source 30 (atCursor .plus 11 0)
      { span := byteSpan 0 25, value := [] } (atCursor .plus 11 10) [semicolonFailure.toDiagnostic] :=
    .recovered balanced_capture (outer_rejected source 25 10 (by decide))
  rcases (isolatedCoreBlock_trace_success_iff (statement := blockStatement breakStatement)
      inner_success_sound inner_reject_sound inner_success_complete inner_reject_complete
      inner_success_context .require (input := rejectedInput prior)).mp parsed with
    ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := rejectedInput prior) balanced_capture with
    ⟨captured, capturedResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame capturedResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [rejectedInput, inputState, State.diagnostics, List.reverse_reverse] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = nestedTokens .plus at tokens
    change output.window.endIndex = 11 at endpoint
    change output.cursor = 10 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxNestedBreakBlockRejectionExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBlockFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockFuelTotalityProperties

open Solcore.Syntax.Parser

example := @coreBlock_ordinary_of_statementFuel
example := @coreBlock_ne_invariant_of_statementFuel
example := @isolatedCoreBlock_ordinary_of_statementFuel
example := @isolatedCoreBlock_ne_invariant_of_statementFuel
example := @coreBlock_fuelTotalityContract
example := @isolatedCoreBlock_fuelTotalityContract

end Solcore.Test.SyntaxParserBlockFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBlockProperties
/-! External consumers for canonical Core-block progress contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @coreBlock_preservesTokensOnSuccess
example := @coreBlock_preservesTokenWindow
example := @coreBlock_cursor_lt_onSuccess
example := @coreBlock_cursorMonotoneOnSuccess
example := @coreBlock_startsAtCurrentTokenOnSuccess
example := @coreBlock_validFor
example := @BlockInternals.captureBlockTail_validFor
example := @BlockInternals.captureBlock?_validFor
example := @BlockInternals.captureBlock?_startsAtCurrentToken
example := @hasBalancedBlockCapture
example := @isolateBlock_validFor
example := @isolateBlock_preservesTokensOnSuccess
example := @isolateBlock_preservesTokenWindow
example := @isolateBlock_cursor_lt_onSuccess_of_balancedCapture
example := @isolateBlock_cursorMonotoneOnSuccess
example := @isolateBlock_startsAtCurrentTokenOnSuccess
example := @isolatedCoreBlock_validFor
example := @isolatedCoreBlock_preservesTokenWindow
example := @isolatedCoreBlock_preservesTokensOnSuccess
example := @isolatedCoreBlock_cursorMonotoneOnSuccess
example := @isolatedCoreBlock_startsAtCurrentTokenOnSuccess

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokenWindow statement) :
    Parser.PreservesTokenWindow (coreBlock statement policy) :=
  coreBlock_preservesTokenWindow statement policy statementShape

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement) :
    Parser.PreservesTokensOnSuccess (coreBlock statement policy) :=
  coreBlock_preservesTokensOnSuccess statement policy statementShape

example (statementValid : SourceFile → Statement → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (valid : statement.ValidFor statementValid)
    (shape : Parser.PreservesTokensOnSuccess statement)
    (spanValid : ∀ file retained,
      statementValid file retained → retained.span.ValidFor file) :
    (coreBlock statement policy).ValidFor (Block.ValidFor statementValid) :=
  coreBlock_validFor statementValid statement policy valid shape spanValid

example (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementShape : Parser.PreservesTokensOnSuccess statement)
    {input next : State} {body : Block}
    (result : coreBlock statement policy input = .ok body next) :
    next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  ⟨coreBlock_preservesTokensOnSuccess statement policy statementShape
      input body next result,
    coreBlock_cursor_lt_onSuccess statement policy result⟩

example (parser : Parser Block)
    (shape : Parser.PreservesTokensOnSuccess parser)
    (monotone : Parser.CursorMonotoneOnSuccess parser) :
    Parser.PreservesTokensOnSuccess (isolateBlock parser) ∧
      Parser.CursorMonotoneOnSuccess (isolateBlock parser) :=
  ⟨isolateBlock_preservesTokensOnSuccess parser shape,
    isolateBlock_cursorMonotoneOnSuccess parser monotone⟩

example (parser : Parser Block)
    (shape : Parser.PreservesTokenWindow parser) :
    Parser.PreservesTokenWindow (isolateBlock parser) :=
  isolateBlock_preservesTokenWindow parser shape

example (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Block)
    (valid : parser.ValidFor (Block.ValidFor statementValid)) :
    (isolateBlock parser).ValidFor (Block.ValidFor statementValid) :=
  isolateBlock_validFor statementValid parser valid

example (parser : Parser Block)
    (starts : Parser.StartsAtCurrentTokenOnSuccess parser (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess (isolateBlock parser) (·.span) :=
  isolateBlock_startsAtCurrentTokenOnSuccess parser starts

example (statementValid : SourceFile → Statement → Prop)
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (valid : statement.ValidFor statementValid)
    (shape : Parser.PreservesTokensOnSuccess statement)
    (spanValid : ∀ file retained,
      statementValid file retained → retained.span.ValidFor file) :
    (isolateBlock (coreBlock statement policy)).ValidFor
      (Block.ValidFor statementValid) :=
  isolatedCoreBlock_validFor statementValid statement policy valid shape
    spanValid

example (parser : Parser Block) {input next : State} {body : Block}
    (captured : hasBalancedBlockCapture input = true)
    (result : isolateBlock parser input = .ok body next) :
    input.cursor < next.cursor :=
  isolateBlock_cursor_lt_onSuccess_of_balancedCapture parser captured result

example {input : State} {captured : BlockInternals.CapturedBlock}
    (inputValid : input.ValidFor)
    (result : BlockInternals.captureBlock? input = some captured) :
    captured.span.ValidFor input.file ∧
      input.cursor < captured.window.endIndex ∧
      captured.window.endIndex ≤ input.window.endIndex ∧
      captured.window.endIndex ≤ input.tokens.size ∧
      captured.window.endByte ≤ input.file.content.utf8ByteSize ∧
      isUtf8Boundary input.file.content captured.window.endByte = true ∧
      (input.enterWindow input.cursor captured.window).ValidFor := by
  have valid :=
    BlockInternals.captureBlock?_validFor inputValid result
  exact ⟨valid.span, valid.cursor_lt_endIndex, valid.endIndex_le_window,
    valid.endIndex_le_tokens, valid.endByte_le_source,
    valid.endByte_boundary, valid.entered⟩

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBlockStatementTraceProperties
/-! Exact raw block-statement consumers retain the AST and every prior event,
require the final expression semicolon, and propagate failures without recovery. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockStatementTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {statement : Parser Statement}
  {statementTrace : SourceId → Nat → Remainder → Statement → Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

example := @BlockStatementTraceParses.ordinary
example := @BlockStatementTraceRejects.ordinary
example := @BlockStatementTraceParses.result_unique
example := @BlockStatementTraceRejects.result_unique
example := @BlockStatementTraceRejects.disjoint_success
example := @blockStatementTraceExactOutcomeSpec
example := @coreBlockItems_success_context_eq
example := @coreBlock_success_context_eq
example := @blockStatement_trace_success_sound
example := @blockStatement_trace_reject_sound
example := @blockStatement_trace_success_complete
example := @blockStatement_trace_reject_complete
example := @blockStatement_success_context
example := @blockStatement_trace_success_iff
example := @blockStatement_trace_reject_iff
example := @blockStatement_trace_reject_failure_iff

/-- A raw failure leaves the same complete rejected state and failure record.
This statement boundary performs no balanced-window recovery or report commit. -/
theorem raw_rejection_propagates_whole_state
    {input rejected : State} {failure : Failure}
    (result : coreBlock statement .require input = .reject failure rejected) :
    blockStatement statement input = .reject failure rejected :=
  blockStatement_reject_iff_raw.mpr result

/-- The statement wrapper requires even the final expression's semicolon.
Its diagnostic follows both identical inner events after every prior event. -/
theorem block_statement_requires_last_expression_semicolon
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {afterOpening beforeClose remainder : Remainder}
    {openingSpan closingSpan expressionSpan : SourceSpan} {expressionValue : Expr}
    {event : ParseDiagnostic}
    (opening : ExactTokenParses (.symbol .leftBrace)
      input.declarativeRemainder openingSpan afterOpening)
    (inside : afterOpening.cursor < afterOpening.endIndex)
    (notClosing : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightBrace))
    (valueParsed : statementTrace input.file.id input.window.endByte afterOpening
      { span := expressionSpan, value := .expression expressionValue false } beforeClose [event, event])
    (progress : afterOpening.cursor < beforeClose.cursor)
    (closing : ExactTokenParses (.symbol .rightBrace) beforeClose closingSpan remainder) :
    ∃ output, blockStatement statement input = .ok {
        span := SourceSpan.cover openingSpan closingSpan,
        value := .block [{ span := expressionSpan, value := .expression expressionValue false }]
      } output ∧ output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ [event, event,
        { span := expressionSpan, kind := .constraintViolation .expressionRequiresSemicolon }] :=
  blockStatement_trace_success_complete successComplete contextFrame
    (.parsed (.parsed openingSpan closingSpan opening
      (.next inside notClosing valueParsed progress (.close closingSpan closing))
      (.lastRequired (.missing (fun impossible => impossible)))))

/-- Independent raw rejection keeps its earlier inner events, while the
specified whole failure remains separate from the appended diagnostic list. -/
theorem block_statement_rejection_keeps_report_uncommitted
    (successSound : StatementTraceSuccessSound statement statementTrace)
    (rejectSound : StatementTraceRejectSound statement statementRejects)
    (successComplete : StatementTraceSuccessComplete statement statementTrace)
    (rejectComplete : StatementTraceRejectComplete statement statementRejects)
    (contextFrame : StatementSuccessContext statement)
    {input : State} {remainder : Remainder} {failure : Failure}
    {first second : ParseDiagnostic}
    (rejection : CoreBlockTraceRejects statementTrace statementRejects .require
      input.file.id input.window.endByte input.declarativeRemainder remainder
      failure.toDiagnostic [first, second, first]) :
    ∃ rejected, blockStatement statement input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  (blockStatement_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame).mp (.rejected rejection)

/-- Only the inner frame law is required for successful source/window
preservation; neither validity nor empty incoming diagnostics is assumed. -/
theorem successful_block_statement_retains_full_context
    (contextFrame : StatementSuccessContext statement)
    {input output : State} {value : Statement}
    (result : blockStatement statement input = .ok value output) :
    output.file = input.file ∧ output.window = input.window :=
  blockStatement_success_context contextFrame result

/-- Independent nested block statements retain strict progress and the active
token carrier when the corresponding inner trace law is available. -/
theorem independent_block_statement_keeps_window_and_progress
    {source : SourceId} {endByte : Nat}
    (statementWindow : ∀ {input statement output trace},
      statementTrace source endByte input statement output trace →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {value : Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses statementTrace source endByte input value output trace) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex ∧
      input.cursor < output.cursor ∧ output.cursor ≤ output.endIndex :=
  ⟨(parsed.output_window statementWindow).1, (parsed.output_window statementWindow).2,
    parsed.cursor_lt, parsed.output_cursor_le_endIndex⟩

end Solcore.Test.SyntaxParserBlockStatementTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserBlockTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserBlockTotalityProperties

open Solcore.Syntax.Parser

example := @coreBlockItems_ne_invariant_of_remainingCount_lt

example := @coreBlock_invariantFreeOnValid

example := @BlockInternals.isolateBlock_invariantFreeOnValid

example := @BlockInternals.isolateBlock_cursor_lt_onSuccess

example := @isolatedCoreBlock_elementTotalityContract

end Solcore.Test.SyntaxParserBlockTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserControlLeafDiagnosticTraceProperties
/-! Concrete Core control leaves retain prior events, exact spans, and ordered
first-failure reports, without any abstract child-parser assumption. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserControlLeafDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @TerminatedControlStatementTraceParses.result_unique
example := @TerminatedControlStatementTraceRejects.result_unique
example := @breakStatement_trace_reject_sound
example := @continueStatement_trace_reject_complete

theorem break_retains_exact_spans_and_prior_events
    {input : State} {afterMarker after : Remainder} {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .breakKw) input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, breakStatement input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .breakStmt
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using breakStatement_trace_success_iff.mp
    ⟨.parsed markerSpan semicolonSpan marker semicolon, rfl⟩

theorem continue_retains_exact_spans_and_prior_events
    {input : State} {afterMarker after : Remainder} {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .continueKw)
      input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, continueStatement input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .continueStmt
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using continueStatement_trace_success_iff.mp
    ⟨.parsed markerSpan semicolonSpan marker semicolon, rfl⟩

/-- Even a semicolon at the initial cursor must first fail the required
`break` keyword; it is not consumed or reported as a missing semicolon. -/
theorem leading_semicolon_reports_missing_break
    {input : State} {span : SourceSpan} {afterSemicolon : Remainder}
    (semicolon : ExactTokenParses (.symbol .semicolon)
      input.declarativeRemainder span afterSemicolon) :
    ∃ rejected, breakStatement input = .reject {
        span, found := some (.symbol .semicolon),
        expected := { head := .keyword .breakKw, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = input.declarativeRemainder ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.keyword .breakKw) := by
    rintro ⟨otherSpan, _, found⟩
    have current := semicolon.1.2
    change input.tokens[input.cursor]? = some { span, value := .symbol .semicolon } at current
    rw [found] at current
    cases current
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.markerMissing absent (.reported (.token semicolon.1)))

/-- Once `continue` is consumed, a window end fixes every failure field at the
explicit byte boundary, regardless of any tokens outside that window. -/
theorem continue_window_end_reports_missing_semicolon
    {input : State} {afterMarker : Remainder} {markerSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .continueKw)
      input.declarativeRemainder markerSpan afterMarker)
    (atEnd : afterMarker.endIndex ≤ afterMarker.cursor) :
    ∃ rejected, continueStatement input = .reject {
        span := { source := input.file.id
                  startByte := input.window.endByte
                  endByte := input.window.endByte },
        found := none, expected := { head := .symbol .semicolon, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterMarker ∧
      rejected.diagnostics = input.diagnostics := by
  have absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
      (.symbol .semicolon) := by
    rintro ⟨span, inside, _⟩
    omega
  simpa only [List.append_nil] using continueStatement_trace_reject_failure_iff.mp
    (.semicolonMissing markerSpan marker absent (.reported (.windowEnd atEnd)))

/-- Failure on a non-semicolon after `break` reports that exact token's span
and kind, while retaining the keyword's consumption and the prior event order. -/
theorem break_missing_semicolon_retains_keyword_consumption
    {input : State} {afterMarker : Remainder} {markerSpan offendingSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .breakKw) input.declarativeRemainder markerSpan afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex afterMarker.cursor
      (.symbol .semicolon))
    (found : Option TokenKind)
    (current : CurrentInputAt input.file.id input.window.endByte afterMarker offendingSpan found) :
    ∃ rejected, breakStatement input = .reject {
        span := offendingSpan, found, expected := { head := .symbol .semicolon, tail := [] },
        context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterMarker ∧
      rejected.diagnostics = input.diagnostics := by
  simpa only [List.append_nil] using breakStatement_trace_reject_failure_iff.mp
    (.semicolonMissing markerSpan marker absent (.reported current))

/-- The actual leaf contracts instantiate raw block equivalence without
assuming any statement execution/grammar bridge from the consumer. -/
theorem break_only_raw_block_trace_iff
    (policy : TailExpressionPolicy) {input : State} {body : Block} {after : Remainder}
    {trace : List ParseDiagnostic} :
    CoreBlockTraceParses BreakStatementTraceParses policy.declarative
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, coreBlock breakStatement policy input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  coreBlock_trace_success_iff breakStatement_trace_success_sound
    breakStatement_trace_success_complete breakStatement_success_context policy

end Solcore.Test.SyntaxParserControlLeafDiagnosticTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserReturnClauseSoundnessProperties
/-! External consumers for exact function return-clause outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalReturnClauseParses
example := @OptionalReturnClauseRejects
example := @optionalReturnClauseDeterministicOutcomeSpec
example := @optionalReturnClauseExactOutcomeSpec
example := @returnClause_success_sound
example := @returnClause_success_sound_and_validFor
example := @returnClause_reject_sound
example := @returnClause_ordinaryOutcome_sound
example := @returnClause_exactOutcomeSpec
example := @returnClause_success_result_unique
example := @returnClause_reject_output_unique

example {input next : State} {clause : Option ReturnClause}
    (result : returnClause input = .ok clause next) :
    OptionalReturnClauseParses input.declarativeRemainder clause
      next.declarativeRemainder :=
  returnClause_success_sound result

example {input next : State} {clause : Option ReturnClause}
    (inputValid : input.ValidFor)
    (result : returnClause input = .ok clause next) :
    OptionalReturnClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      Option.ValidFor ReturnClause.ValidFor input.file clause :=
  returnClause_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    OptionalReturnClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  returnClause_reject_sound result

end Solcore.Test.SyntaxParserReturnClauseSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserReturnStatementSuccessTraceProperties
/-! Return-value priority, exact optional ASTs, and duplicate expression events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnStatementSuccessTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}

example := @OptionalReturnValueTraceParses.ordinary
example := @ReturnStatementTraceParses.ordinary
example := @OptionalReturnValueTraceParses.result_unique
example := @ReturnStatementTraceParses.result_unique
example := @returnStatement_success_context

/-- A semicolon suppresses expression evaluation regardless of the supplied
parser and is left in place for the required final-token consumer. -/
theorem current_semicolon_never_invokes_expression
    (expression : Parser Expr) {input : State} {span : SourceSpan}
    (current : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    StatementSimpleInternals.optionalReturnValue expression input = .ok none input :=
  StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt expression current

/-- The independent empty-return judgment itself needs no expression premise. -/
theorem empty_return_independent_trace
    {input afterMarker after : Remainder} {source : SourceId} {endByte : Nat}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ReturnStatementTraceParses expressionTrace source endByte input {
      span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
    } after [] :=
  .parsed markerSpan semicolonSpan marker (.absent semicolonSpan semicolon.1) semicolon

/-- Empty-return execution is likewise unconditional and retains every prior
event, with exact covering spans and a two-token cursor advance. -/
theorem empty_return_retains_prior_without_expression_contracts
    (expression : Parser Expr) {input : State} {afterMarker after : Remainder}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterMarker semicolonSpan after) :
    ∃ output, returnStatement expression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt none
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  refine ⟨{ input with cursor := input.cursor + 2 },
    returnStatement_eq_ok_none_of_exactTokens expression marker semicolon, ?_, rfl⟩
  rcases marker with ⟨_, rfl⟩
  exact semicolon.2.symm

/-- Nonempty returns preserve the expression AST and repeated event payloads
exactly; the keyword and terminating semicolon add no further diagnostic. -/
theorem present_return_keeps_duplicate_expression_events
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {afterMarker afterValue after : Remainder} {value : Expr}
    {markerSpan semicolonSpan : SourceSpan} (event : ParseDiagnostic)
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (valueParsed : expressionTrace input.file.id input.window.endByte
      afterMarker value afterValue [event, event])
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement expression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan, value := .returnStmt (some value)
      } output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ [event, event] :=
  returnStatement_trace_success_complete complete
    (.parsed markerSpan semicolonSpan marker (.present notSemicolon valueParsed) semicolon)

/-- General-expression completeness is conditional, and both explicit laws
remain visible when the exact execution/trace equivalence is consumed. -/
theorem return_exact_success_under_expression_contracts
    (sound : ExpressionTraceSuccessSound expression expressionTrace)
    (complete : ExpressionTraceSuccessComplete expression expressionTrace)
    {input : State} {statement : Statement} {after : Remainder} {trace : List ParseDiagnostic} :
    ReturnStatementTraceParses expressionTrace input.file.id input.window.endByte
      input.declarativeRemainder statement after trace ↔
    ∃ output, returnStatement expression input = .ok statement output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  returnStatement_trace_success_iff sound complete

end Solcore.Test.SyntaxParserReturnStatementSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementAssemblyTotalityProperties
/-! Compile-time consumers for Core inline-assembly totality. -/

namespace Solcore.Test.SyntaxParserStatementAssemblyTotalityProperties

open Solcore.Syntax.Parser

example := @assemblyStatement_ordinary
example := @assemblyStatement_invariantFreeOnValid
example := @assemblyStatement_ne_invariant
example := @assemblyStatement_elementTotalityContract
example := @assemblyStatement_fuelElementTotalityContract
example := @assemblyStatement_totalityContract
example := @assemblyStatement_fuelTotalityContract
example := @assemblyStatement_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserStatementAssemblyTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementChoiceFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementChoiceFuelTotalityProperties

open Solcore.Syntax.Parser.TermInternals

example := @FuelStatementTotalityContract.ofTotality
example := @recognizedStatementOrFallback_ordinary_of_fuels
example := @recognizedStatementOrFallback_fuelTotalityContract
example := @recognizedStatementOrFallback_cursor_lt_onSuccess_of_strict
example := @stateChoice_fuelTotalityContract
example := @stateChoice_cursor_lt_onSuccess_of_strict

end Solcore.Test.SyntaxParserStatementChoiceFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlBlockFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlBlockFuelTotalityProperties

open Solcore.Syntax.Parser

example := @blockStatement_ordinary_of_statementFuel
example := @blockStatement_ne_invariant_of_statementFuel
example := @blockStatement_fuelTotalityContract
example := @whileStatement_ordinary_of_fuels
example := @whileStatement_ne_invariant_of_fuels
example := @whileStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementControlBlockFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlForFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlForFuelContractProperties

open Solcore.Syntax.Parser

example := @forStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementControlForFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlForFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlForFuelTotalityProperties

open Solcore.Syntax.Parser

example := @forStatement_ordinary_of_fuels
example := @forStatement_ne_invariant_of_fuels

end Solcore.Test.SyntaxParserStatementControlForFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlIfFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlIfFuelTotalityProperties

open Solcore.Syntax.Parser

example := @ControlInternals.optionalElseBody_ordinary_of_blockFuel
example := @ifStatement_ordinary_of_fuels
example := @ifStatement_ne_invariant_of_fuels
example := @ifStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementControlIfFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementControlLeafTotalityProperties

open Solcore.Syntax.Parser

example := @ControlInternals.terminatedControl_invariantFreeOnValid
example := @breakStatement_invariantFreeOnValid
example := @continueStatement_invariantFreeOnValid
example := @breakStatement_totalityContract
example := @continueStatement_totalityContract

end Solcore.Test.SyntaxParserStatementControlLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementControlProperties
/-! External consumers for canonical Core control-statement contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @ControlInternals.forItemsTail_validFor
example := @ControlInternals.forItemsTail_preservesTokenWindow
example := @ControlInternals.forItemsTail_cursorMonotoneOnSuccess
example := @ControlInternals.forItems_validFor
example := @ControlInternals.forItems_preservesTokenWindow
example := @ControlInternals.forItems_preservesTokensOnSuccess
example := @ControlInternals.forItems_cursorMonotoneOnSuccess
example := @forStatement_preservesTokenWindow
example := @forStatement_preservesTokensOnSuccess
example := @forStatement_cursorMonotoneOnSuccess
example := @forStatement_startsAtCurrentTokenOnSuccess
example := @forStatement_validFor
example := @blockStatement_validFor
example := @blockStatement_preservesTokenWindow
example := @blockStatement_preservesTokensOnSuccess
example := @blockStatement_cursorMonotoneOnSuccess
example := @blockStatement_startsAtCurrentTokenOnSuccess
example := @whileStatement_span_validOnSuccess
example := @whileStatement_validFor
example := @whileStatement_preservesTokenWindow
example := @whileStatement_preservesTokensOnSuccess
example := @whileStatement_cursorMonotoneOnSuccess
example := @whileStatement_startsAtCurrentTokenOnSuccess
example := @ControlInternals.optionalElseBody_validFor
example := @ControlInternals.optionalElseBody_preservesTokenWindow
example := @ControlInternals.optionalElseBody_preservesTokensOnSuccess
example := @ControlInternals.optionalElseBody_cursorMonotoneOnSuccess
example := @ControlInternals.optionalElseBody_some_startsAfterKeyword
example := @ifStatement_validFor
example := @ifStatement_preservesTokenWindow
example := @ifStatement_preservesTokensOnSuccess
example := @ifStatement_cursorMonotoneOnSuccess
example := @ifStatement_startsAtCurrentTokenOnSuccess
example := @assemblyStatement_validFor
example := @assemblyStatement_preservesTokenWindow
example := @assemblyStatement_preservesTokensOnSuccess
example := @assemblyStatement_cursorMonotoneOnSuccess
example := @assemblyStatement_startsAtCurrentTokenOnSuccess
example := @assemblyStatement_cursor_lt_onSuccess
example := @ControlInternals.terminatedControl_validFor
example := @ControlInternals.terminatedControl_preservesTokenWindow
example := @ControlInternals.terminatedControl_cursorMonotoneOnSuccess
example := @ControlInternals.terminatedControl_startsAtCurrentTokenOnSuccess
example := @breakStatement_validFor
example := @continueStatement_validFor
example := @breakStatement_preservesTokenWindow
example := @continueStatement_preservesTokenWindow
example := @breakStatement_cursorMonotoneOnSuccess
example := @continueStatement_cursorMonotoneOnSuccess
example := @breakStatement_startsAtCurrentTokenOnSuccess
example := @continueStatement_startsAtCurrentTokenOnSuccess
example := @ControlInternals.terminatedControl_cursor_lt_onSuccess
example := @breakStatement_preservesTokensOnSuccess
example := @continueStatement_preservesTokensOnSuccess
example := @breakStatement_cursor_lt_onSuccess
example := @continueStatement_cursor_lt_onSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementFallback
/-! Regression coverage for canonical Core statement-choice fallback. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private def fallbackSource : SourceId := {
  origin := .main
  path := "parser-statement-fallback.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private structure BlockRun where
  value : Block
  state : Parser.State

private def runBlock (label content : String) : IO BlockRun := do
  let file : SourceFile := { id := fallbackSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match Parser.block .allow (Parser.State.initial file lexed) with
  | .ok value state =>
      unless state.atEnd do
        throw (IO.userError
          s!"{label}: left {state.remainingCount} token(s)")
      pure { value, state }
  | .reject failure _ => throw (IO.userError
      s!"{label}: block rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: parser invariant failed: {reprStr error}")

private def assertRecoveredPair
    (label : String) (block : Block) : IO Unit :=
  match block.value with
  | [
      { value := .expression { value := .error, .. } true, .. },
      { value := .letDecl name none none, .. }
    ] => assertEqual name.value "kept" s!"{label} following statement"
  | statements => throw (IO.userError
      s!"{label}: fallback statements changed: {reprStr statements}")

private structure FallbackCase where
  label : String
  source : String
  failureRange : ByteRange
  failureKind : ParseDiagnosticKind

private def expressionFailure (found : TokenKind) : ParseDiagnosticKind :=
  .unexpected (some found) { head := .expression, tail := [] } .expression

private def statementFailure (found : TokenKind)
    (expected : ParseExpectation) : ParseDiagnosticKind :=
  .unexpected (some found) { head := expected, tail := [] } .statement

private def fallbackCases : List FallbackCase := [
  {
    label := "let initializer"
    source := "{ let value = ; let kept; }"
    failureRange := (14, 15)
    failureKind := expressionFailure (.symbol .semicolon)
  },
  {
    label := "return expression"
    source := "{ return value + ; let kept; }"
    failureRange := (17, 18)
    failureKind := expressionFailure (.symbol .semicolon)
  },
  {
    label := "break terminator"
    source := "{ break value; let kept; }"
    failureRange := (8, 13)
    failureKind := statementFailure (.identifier "value")
      (.symbol .semicolon)
  },
  {
    label := "continue terminator"
    source := "{ continue value; let kept; }"
    failureRange := (11, 16)
    failureKind := statementFailure (.identifier "value")
      (.symbol .semicolon)
  },
  {
    label := "if opening"
    source := "{ if value; let kept; }"
    failureRange := (5, 10)
    failureKind := statementFailure (.identifier "value")
      (.symbol .leftParen)
  },
  {
    label := "match opening"
    source := "{ match value; let kept; }"
    failureRange := (8, 13)
    failureKind := .unexpected (some (.identifier "value"))
      { head := .symbol .leftParen, tail := [] } .expression
  },
  {
    label := "for opening"
    source := "{ for value; let kept; }"
    failureRange := (6, 11)
    failureKind := statementFailure (.identifier "value")
      (.symbol .leftParen)
  },
  {
    label := "assembly opening"
    source := "{ assembly value; let kept; }"
    failureRange := (11, 16)
    failureKind := .unexpected (some (.identifier "value"))
      { head := .symbol .leftBrace, tail := [] } .yulStatement
  },
  {
    label := "nested block"
    source := "{ { ; let kept; }"
    failureRange := (4, 5)
    failureKind := expressionFailure (.symbol .semicolon)
  }
]

private def testRecognizedBranchesUseFallbackShape : IO Unit := do
  for test in fallbackCases do
    let run ← runBlock test.label test.source
    assertRecoveredPair test.label run.value
    assertEqual (run.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
        (test.failureRange, test.failureKind)
      ] s!"{test.label} sole primary diagnostic"

private def semicolonRanges (tokens : List Token) : List ByteRange :=
  tokens.filterMap fun token =>
    if token.value == .symbol .semicolon then
      some (byteRange token.span)
    else
      none

private def testIndependentSameLineFailuresAndBodyIsolation : IO Unit := do
  let source := String.intercalate "\n" [
    "function broken() { let first = ; let second = ; }",
    "type Kept = word;"
  ]
  let file : SourceFile := { id := fallbackSource, content := source }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"same-line fallback parser invariant: {reprStr error}")
  assertEqual output.lexicalDiagnostics []
    "same-line fallback lexical diagnostics"
  let invalidSemicolons := (semicolonRanges output.tokens).take 2
  assertEqual (output.parseDiagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind))
    (invalidSemicolons.map fun span =>
      (span, expressionFailure (.symbol .semicolon)))
    "independent same-line primary diagnostics"
  match output.parsed.items with
  | [
      { value := .function function, .. },
      { value := .typeAlias alias, .. }
    ] =>
      assertEqual function.value.signature.name.value "broken"
        "malformed function name"
      assertEqual alias.value.name.value "Kept" "following top-level item"
      match function.value.body.value with
      | [
          { value := .expression { value := .error, .. } true, .. },
          { value := .expression { value := .error, .. } true, .. }
        ] => pure ()
      | body => throw (IO.userError
          s!"body isolation replaced recovered statements: {reprStr body}")
  | items => throw (IO.userError
      s!"same-line fallback top-level shape changed: {reprStr items}")

/-- Run statement-choice fallback and body-isolation regressions. -/
def testSyntaxParserStatementFallback : IO Unit := do
  testRecognizedBranchesUseFallbackShape
  testIndependentSameLineFailuresAndBodyIsolation

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementForItemFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementForItemFuelTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.forLetItem_ordinary_of_expressionFuel
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_ordinary_of_expressionFuel
example := @StatementSimpleInternals.forLetItem_cursor_lt_onSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
example := @forItem_ordinary_of_expressionFuel
example := @forItem_cursor_lt_onSuccess
example := @forItem_fuelElementTotalityContract

end Solcore.Test.SyntaxParserStatementForItemFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementForItemsFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementForItemsFuelTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ControlInternals

example := @forItemsTail_ordinary_of_itemFuel
example := @forItemsTail_ne_invariant_of_itemFuel
example := @forItems_ordinary_of_itemFuel
example := @forItems_ne_invariant_of_itemFuel
example := @forItems_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementForItemsFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementLayerFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementLayerFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TermInternals.statementLayerFuel
example := @TermInternals.statementLayer_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementLayerFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementLayerStrictProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementLayerStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TermInternals.statementLayer_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserStatementLayerStrictProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchCaseFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchCaseFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.matchCase_ordinary_of_fuels
example := @MatchInternals.matchCase_ne_invariant_of_fuels
example := @MatchInternals.matchCase_cursor_lt_onSuccess
example := @MatchInternals.matchCase_fuelElementTotalityContract

end Solcore.Test.SyntaxParserStatementMatchCaseFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchCasesFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchCasesFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.FuelCaseListTotalityContract.ne_invariant
example := @MatchInternals.matchCases_ordinary_of_fuels
example := @MatchInternals.matchCases_ne_invariant_of_fuels
example := @MatchInternals.matchCases_production_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementMatchCasesFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchDefaultFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchDefaultFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.optionalDefaultBody_ordinary_of_statementFuel
example := @MatchInternals.optionalDefaultBody_ne_invariant_of_statementFuel

end Solcore.Test.SyntaxParserStatementMatchDefaultFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchProperties
/-! External consumers for canonical Core match-component contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @MatchInternals.matchCase_validFor
example := @MatchInternals.matchCase_preservesTokenWindow
example := @MatchInternals.matchCase_preservesTokensOnSuccess
example := @MatchInternals.matchCase_cursorMonotoneOnSuccess
example := @MatchInternals.matchCase_startsAtCurrentTokenOnSuccess
example := @MatchInternals.matchCases_validFor
example := @MatchInternals.matchCases_preservesTokenWindow
example := @MatchInternals.matchCases_preservesTokensOnSuccess
example := @MatchInternals.matchCases_cursorMonotoneOnSuccess
example := @MatchInternals.optionalDefaultBody_validFor
example := @MatchInternals.optionalDefaultBody_preservesTokenWindow
example := @MatchInternals.optionalDefaultBody_preservesTokensOnSuccess
example := @MatchInternals.optionalDefaultBody_cursorMonotoneOnSuccess
example := @MatchInternals.optionalDefaultBody_some_startsAfterKeyword
example := @MatchInternals.requireScrutinees_validFor
example := @MatchInternals.requireScrutinees_preservesTokenWindow
example := @MatchInternals.requireScrutinees_cursorMonotoneOnSuccess
example := @MatchInternals.requireScrutinees_ordinary
example := @MatchInternals.requireScrutinees_invariantFreeOnValid
example := @MatchInternals.requireScrutinees_ne_invariant
example := @matchStatement_validFor
example := @matchStatement_preservesTokenWindow
example := @matchStatement_preservesTokensOnSuccess
example := @matchStatement_cursorMonotoneOnSuccess
example := @matchStatement_cursor_lt_onSuccess
example := @matchStatement_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchStatementFuelContractProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchStatementFuelContractProperties

open Solcore.Syntax.Parser

example := @matchStatement_ne_invariant_of_fuels
example := @matchStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementMatchStatementFuelContractProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchStatementFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchStatementFuelTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.matchStatementFuel
example := @matchStatement_ordinary_of_fuels

end Solcore.Test.SyntaxParserStatementMatchStatementFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementMatchValidationTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementMatchValidationTotalityProperties

open Solcore.Syntax.Parser

example := @MatchInternals.validateMatchCaseArity_ordinary
example := @MatchInternals.validateMatchArities_ordinary
example := @MatchInternals.validateMatchArities_invariantFreeOnValid
example := @MatchInternals.validateMatchArities_ne_invariant

end Solcore.Test.SyntaxParserStatementMatchValidationTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementSimpleBranchFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementSimpleBranchFuelTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.optionalLetInitializer_ordinary_of_expressionFuel
example := @StatementSimpleInternals.optionalReturnValue_ordinary_of_expressionFuel
example := @letStatement_ordinary_of_expressionFuel
example := @returnStatement_ordinary_of_expressionFuel
example := @letStatement_ne_invariant_of_expressionFuel
example := @returnStatement_ne_invariant_of_expressionFuel
example := @letStatement_fuelTotalityContract
example := @returnStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserStatementSimpleBranchFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementSimpleBranchTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserStatementSimpleBranchTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.optionalLetType_invariantFreeOnValid
example := @StatementSimpleInternals.optionalLetInitializer_invariantFreeOnValid
example := @StatementSimpleInternals.optionalReturnValue_invariantFreeOnValid
example := @letStatement_invariantFreeOnValid
example := @returnStatement_invariantFreeOnValid
example := @letStatement_totalityContract
example := @returnStatement_totalityContract

end Solcore.Test.SyntaxParserStatementSimpleBranchTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatementSimpleProperties
/-! External consumers for canonical Core-statement leaf contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @StatementSimpleInternals.valueAssignOperator_ok_state_shape
example := @StatementSimpleInternals.valueAssignOperator_ok_validFor
example := @StatementSimpleInternals.valueAssignOperator_reject_state_shape
example := @StatementSimpleInternals.valueAssignOperator_reject_validFor
example := @StatementSimpleInternals.valueAssignOperator_validFor
example := @StatementSimpleInternals.valueAssignOperator_preservesTokenWindow
example :=
  @StatementSimpleInternals.valueAssignOperator_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.valueAssignOperator_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.valueAssignOperator_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.AssignmentTail.ValidFor
example := @StatementSimpleInternals.AssignmentTail.startSpan
example := @StatementSimpleInternals.assignmentTail_validFor
example := @StatementSimpleInternals.optionalAssignmentTail_validFor
example :=
  @StatementSimpleInternals.assignmentTail_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.assignmentTail_cursor_lt_onSuccess
example := @StatementSimpleInternals.assignmentTail_start_le_endOnSuccess
example :=
  @StatementSimpleInternals.optionalAssignmentTail_some_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.assignmentEnd_validFor
example := @StatementSimpleInternals.statementEnd_validFor
example := @StatementSimpleInternals.assignmentTail_preservesTokenWindow
example := @StatementSimpleInternals.assignmentTail_preservesTokensOnSuccess
example := @StatementSimpleInternals.assignmentTail_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalAssignmentTail_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalAssignmentTail_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalAssignmentTail_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalSemicolon_validFor
example := @StatementSimpleInternals.optionalSemicolon_preservesTokenWindow
example := @StatementSimpleInternals.optionalSemicolon_preservesTokensOnSuccess
example := @StatementSimpleInternals.optionalSemicolon_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.optionalSemicolon_some_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.optionalReturnValue_validFor
example := @StatementSimpleInternals.optionalReturnValue_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalReturnValue_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalReturnValue_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalLetType_validFor
example := @StatementSimpleInternals.optionalLetType_preservesTokenWindow
example := @StatementSimpleInternals.optionalLetType_preservesTokensOnSuccess
example := @StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.optionalLetInitializer_validFor
example :=
  @StatementSimpleInternals.optionalLetInitializer_preservesTokenWindow
example :=
  @StatementSimpleInternals.optionalLetInitializer_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.optionalLetInitializer_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.forLetItem_preservesTokenWindow
example := @StatementSimpleInternals.forLetItem_preservesTokensOnSuccess
example := @StatementSimpleInternals.forLetItem_cursorMonotoneOnSuccess
example := @StatementSimpleInternals.forLetItem_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.forLetItem_validFor
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_preservesTokenWindow
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_preservesTokensOnSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_cursorMonotoneOnSuccess
example :=
  @StatementSimpleInternals.forAssignmentOrExpression_startsAtCurrentTokenOnSuccess
example := @StatementSimpleInternals.forAssignmentOrExpression_validFor
example := @forItem_preservesTokenWindow
example := @forItem_preservesTokensOnSuccess
example := @forItem_cursorMonotoneOnSuccess
example := @forItem_startsAtCurrentTokenOnSuccess
example := @forItem_validFor
example := @letStatement_preservesTokenWindow
example := @letStatement_preservesTokensOnSuccess
example := @letStatement_cursorMonotoneOnSuccess
example := @letStatement_startsAtCurrentTokenOnSuccess
example := @letStatement_span_validOnSuccess
example := @letStatement_validFor
example := @returnStatement_preservesTokenWindow
example := @returnStatement_preservesTokensOnSuccess
example := @returnStatement_cursorMonotoneOnSuccess
example := @returnStatement_startsAtCurrentTokenOnSuccess
example := @returnStatement_span_validOnSuccess
example := @returnStatement_validFor
example := @assignmentOrExpressionStatement_preservesTokenWindow
example := @assignmentOrExpressionStatement_preservesTokensOnSuccess
example := @assignmentOrExpressionStatement_cursorMonotoneOnSuccess
example := @assignmentOrExpressionStatement_startsAtCurrentTokenOnSuccess
example := @assignmentOrExpressionStatement_span_validFor_onSuccess
example := @assignmentOrExpressionStatement_value_validFor_onSuccess
example := @assignmentOrExpressionStatement_validFor

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserStatements
/-! Executable Core statement, block, and top-level function regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def statementSource : SourceId := {
  origin := .main
  path := "parser-statements.sol"
}

private structure DirectRun (alpha : Type) where
  value : alpha
  state : Parser.State

private def runDirect {alpha : Type} (label content : String)
    (parser : Solcore.Syntax.Parser.Parser alpha) : IO (DirectRun alpha) := do
  let file : SourceFile := { id := statementSource, content }
  let lexed ← match Lexer.lex file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"{label}: lexer invariant failed: {reprStr error}")
  assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
  match parser (Parser.State.initial file lexed) with
  | .ok value state =>
      unless state.atEnd do
        throw (IO.userError s!"{label}: left {state.remainingCount} token(s)")
      pure { value, state }
  | .reject failure _ => throw (IO.userError
      s!"{label}: rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: invariant failed: {reprStr error}")

private def runStatement (label content : String) : IO (DirectRun Statement) :=
  runDirect label content Parser.statement

private def runBlock_variant (label content : String)
    (policy : Parser.TailExpressionPolicy := .allow) : IO (DirectRun Block) :=
  runDirect label content (Parser.block policy)

private def expressionName? (expression : Expr) : Option String :=
  match expression.value with
  | .identifier name => some name.value
  | _ => none

private inductive StatementAssignment where
  | value (operator : ValueAssignOp)
  | bitNot
  deriving Repr, BEq

private def assignment? (statement : Statement) : Option StatementAssignment :=
  match statement.value with
  | .assignValue _ operator _ => some (.value operator.value)
  | .assignBitNot .. => some .bitNot
  | _ => none

private def testLetAndReturn : IO Unit := do
  let run ← runBlock_variant "let and return"
    "{ let value: word = 42; return value; return; }"
  assertEqual run.state.diagnostics [] "let/return diagnostics"
  match run.value.value with
  | [
      { value := .letDecl name (some type) (some initializer), .. },
      { value := .returnStmt (some returned), .. },
      { value := .returnStmt none, .. }
    ] =>
      assertEqual name.value "value" "let name"
      assertEqual (byteRange type.span) (13, 17) "let type span"
      match initializer.value with
      | .literal { value := .decimal "42", .. } => pure ()
      | value => throw (IO.userError s!"let initializer changed: {reprStr value}")
      assertEqual (expressionName? returned) (some "value") "return value"
  | statements => throw (IO.userError
      s!"let/return statement shapes changed: {reprStr statements}")

private def testAssignments : IO Unit := do
  for (source, expected) in [
      ("x = y;", .value .equal), ("x += y;", .value .add),
      ("x -= y;", .value .subtract), ("x *= y;", .value .multiply),
      ("x /= y;", .value .divide), ("x %= y;", .value .modulo),
      ("x &= y;", .value .bitAnd), ("x ^= y;", .value .bitXor),
      ("x |= y;", .value .bitOr), ("x ~=;", .bitNot)
    ] do
    let run ← runStatement s!"assignment {source}" source
    assertEqual (assignment? run.value) (some expected)
      s!"assignment shape {source}"
    assertEqual run.state.diagnostics [] s!"assignment diagnostics {source}"

  for source in ["x = y", "x ~="] do
    let run ← runStatement s!"unterminated assignment {source}" source
    assertEqual (run.state.diagnostics.map (fun item => item.kind)) [
      .constraintViolation .assignmentRequiresSemicolon
    ] s!"missing assignment semicolon {source}"
    assertEqual (run.state.diagnostics.map (fun item => byteRange item.span))
      [(0, source.utf8ByteSize)] s!"missing assignment span {source}"

private def expressionSemicolons (block : Block) : List Bool :=
  block.value.filterMap fun statement => match statement.value with
    | .expression _ terminated => some terminated
    | _ => none

private def testTailPolicies : IO Unit := do
  let allowed ← runBlock_variant "root tail" "{first; last}"
  assertEqual (expressionSemicolons allowed.value) [true, false]
    "root tail source shape"
  assertEqual allowed.state.diagnostics [] "root tail allowance"

  let earlier ← runBlock_variant "earlier tail" "{first second}"
  assertEqual (earlier.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((1, 6), .constraintViolation .expressionRequiresSemicolon)
  ] "earlier expression diagnostic"

  let nested ← runBlock_variant "nested tail" "{{nested} root}"
  assertEqual (nested.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((2, 8), .constraintViolation .expressionRequiresSemicolon)
  ] "nested expression diagnostic"

private def testForHeader : IO Unit := do
  let source :=
    "for (let i: word = 0, seed; i < n; i += 1, flag ~=) { continue; }"
  let run ← runStatement "for header" source
  assertEqual run.state.diagnostics [] "for-header diagnostics"
  match run.value.value with
  | .forLoop header initializer condition post body =>
      assertEqual initializer.length 2 "for initializer count"
      assertEqual post.length 2 "for post count"
      assertEqual (byteRange run.value.span) (0, source.utf8ByteSize) "for span"
      match initializer, post, body.value with
      | [{ value := .letDecl name .., .. },
          { value := .expression seed, .. }],
        [{ value := .assignValue _ op _, .. },
          { value := .assignBitNot .., .. }],
        [{ value := .continueStmt, .. }] =>
          assertEqual name.value "i" "for let item"
          assertEqual (expressionName? seed) (some "seed") "for expression item"
          assertEqual op.value .add "for post assignment"
          assertEqual (header.contains condition.span) true "for condition in header"
      | _, _, _ => throw (IO.userError "for header item shapes changed")
  | value => throw (IO.userError s!"for statement changed: {reprStr value}")

private def testControlStatements : IO Unit := do
  let run ← runBlock_variant "control statements" (String.intercalate " " [
    "{", "while (ready) { break; }",
    "if (ready) { return; } else { continue; }", "{ let x; }", "}"
  ])
  assertEqual run.state.diagnostics [] "control diagnostics"
  match run.value.value with
  | [
      { value := .whileLoop condition whileBody, .. },
      { value := .ifThen _ thenBody (some elseBody), .. },
      { value := .block nestedBody, .. }
    ] =>
      assertEqual (expressionName? condition) (some "ready") "while condition"
      match whileBody.value, thenBody.value, elseBody.value, nestedBody with
      | [{ value := .breakStmt, .. }],
          [{ value := .returnStmt none, .. }],
          [{ value := .continueStmt, .. }],
          [{ value := .letDecl name none none, .. }] =>
          assertEqual name.value "x" "nested block let"
      | whileStatements, thenStatements, elseStatements, blockStatements =>
          let message :=
            s!"control bodies changed: {reprStr whileStatements}; " ++
              s!"{reprStr thenStatements}; {reprStr elseStatements}; " ++
              s!"{reprStr blockStatements}"
          throw (IO.userError message)
  | statements => throw (IO.userError
      s!"control statement shapes changed: {reprStr statements}")

private def testMatchStatements : IO Unit := do
  let malformedContent := "match () {}"
  let malformedFile : SourceFile := {
    id := statementSource
    content := malformedContent
  }
  let malformedLexed ← match Lexer.lex malformedFile with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"empty match lexer invariant failed: {reprStr error}")
  let malformedInput := Parser.State.initial malformedFile malformedLexed

  match Parser.matchStatement Parser.statement Parser.expression
      Parser.pattern malformedInput with
  | .reject failure rejected =>
      assertEqual (byteRange failure.span) (7, 8)
        "empty match rejection range"
      assertEqual failure.toDiagnostic.kind
        (.unexpected (some (.symbol .rightParen))
          { head := .expression, tail := [] } .expression)
        "empty match rejection kind"
      assertEqual rejected.cursor 2 "empty match rejection cursor"
      assertEqual rejected.tokens malformedInput.tokens
        "empty match rejection tokens"
      assertEqual rejected.window malformedInput.window
        "empty match rejection window"
  | .ok value _ => throw (IO.userError
      s!"empty match unexpectedly parsed: {reprStr value}")
  | .invariant error => throw (IO.userError
      s!"empty match exposed an invariant: {reprStr error}")

  let emptyValues : DelimitedList Expr := {
    span := malformedInput.currentSpan
    elements := []
  }
  match Parser.MatchInternals.requireScrutinees emptyValues malformedInput with
  | .reject failure rejected =>
      assertEqual failure.span malformedInput.currentSpan
        "empty scrutinee helper rejection range"
      assertEqual failure.toDiagnostic.kind
        (.unexpected (some (.keyword .matchKw))
          { head := .expression, tail := [] } .expression)
        "empty scrutinee helper rejection kind"
      assertEqual rejected.cursor malformedInput.cursor
        "empty scrutinee helper rejection cursor"
      assertEqual rejected.tokens malformedInput.tokens
        "empty scrutinee helper rejection tokens"
      assertEqual rejected.window malformedInput.window
        "empty scrutinee helper rejection window"
  | .ok value _ => throw (IO.userError
      s!"empty scrutinee helper unexpectedly succeeded: {reprStr value}")
  | .invariant error => throw (IO.userError
      s!"empty scrutinee helper exposed an invariant: {reprStr error}")

  let valid ← runStatement "valid match"
    "match (x, y,) { case (a, b) { return; } default { return; } }"
  assertEqual valid.state.diagnostics [] "valid match diagnostics"
  match valid.value.value with
  | .matchWith scrutinees arms =>
      assertEqual scrutinees.elements.toList.length 2 "match scrutinees"
      assertEqual arms.value.cases.length 1 "match cases"
      assertEqual arms.value.defaultBody.isSome true "match default"
  | value => throw (IO.userError s!"valid match changed: {reprStr value}")

  let empty ← runStatement "empty match" "match (x) {}"
  assertEqual (empty.state.diagnostics.map (fun item => item.kind)) [
    .constraintViolation .matchRequiresArm
  ] "match arm requirement"

  let mismatch ← runStatement "match arity"
    "match (x, y) { case value { return; } }"
  match mismatch.value.value, mismatch.state.diagnostics with
  | .matchWith _ { value := { cases := [case], .. }, .. },
      [{ span, kind := .constraintViolation (.matchArityMismatch 2 1) }] =>
      assertEqual span case.span "match arity diagnostic span"
  | value, diagnostics => throw (IO.userError
      s!"match arity changed: {reprStr value}; {reprStr diagnostics}")

private def testAssemblyAndLambda : IO Unit := do
  let assembly ← runStatement "assembly integration"
    "assembly { let x := 1 x := add(x, 1) if x { leave } }"
  assertEqual assembly.state.diagnostics [] "assembly diagnostics"
  match assembly.value.value with
  | .assembly [
      { value := .letDecl .., .. },
      { value := .assign .., .. },
      { value := .ifThen _ [{ value := .leave, .. }], .. }
    ] => pure ()
  | value => throw (IO.userError s!"assembly integration changed: {reprStr value}")

  let lambda ← runStatement "lambda body"
    "let f = lam(x, comptime y: word) -> word { return y; };"
  assertEqual lambda.state.diagnostics [] "lambda diagnostics"
  match lambda.value.value with
  | .letDecl _ none (some initializer) =>
      match initializer.value with
      | .lambda _ parameters (some returnType) body =>
          assertEqual parameters.elements.length 2 "lambda parameter count"
          assertEqual (byteRange returnType.span) (36, 40) "lambda return span"
          assertEqual body.value.length 1 "lambda body statement count"
      | value => throw (IO.userError s!"lambda expression changed: {reprStr value}")
  | value => throw (IO.userError s!"lambda integration changed: {reprStr value}")

private def testTopLevelFunction : IO Unit := do
  let content := String.intercalate "\n" [
    "// function", "function id(x: word) returns (word) {", "  x", "}",
    "// alias", "type Result = word;"
  ]
  let file : SourceFile := { id := statementSource, content }
  let output ← match Parser.parse file with
    | .ok value => pure value
    | .error error => throw (IO.userError
        s!"top-level function invariant: {reprStr error}")
  assertEqual output.parseDiagnostics [] "top-level function diagnostics"
  assertEqual output.lexicalDiagnostics [] "top-level function lexing"
  assertEqual output.parsed.comments.length 2 "top-level comments"
  match output.parsed.items with
  | [functionItem, aliasItem] =>
      assertEqual (functionItem.leadingComments.map (fun item => item.text))
        [" function"] "function leading comment"
      assertEqual (aliasItem.leadingComments.map (fun item => item.text))
        [" alias"] "following-item leading comment"
      assertEqual (byteRange functionItem.span) (12, 55) "function item span"
      assertEqual (byteRange aliasItem.span) (65, 84) "following item span"
      match functionItem.value with
      | .function declaration =>
          assertEqual declaration.value.signature.name.value "id" "function name"
          assertEqual (byteRange declaration.value.signature.span) (12, 47)
            "function signature span"
          assertEqual (byteRange declaration.value.body.span) (48, 55)
            "function body span"
          match declaration.value.body.value with
          | [{ value := .expression expression false, .. }] =>
              assertEqual (expressionName? expression) (some "x")
                "root tail expression"
          | body => throw (IO.userError s!"function body changed: {reprStr body}")
      | value => throw (IO.userError s!"function item changed: {reprStr value}")
  | items => throw (IO.userError s!"top-level items changed: {reprStr items}")

/-- Run Core statement and top-level function parser regressions. -/
def testSyntaxParserStatements : IO Unit := do
  testLetAndReturn
  testAssignments
  testTailPolicies
  testForHeader
  testControlStatements
  testMatchStatements
  testAssemblyAndLambda
  testTopLevelFunction

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermCanonicalProperties
/-! External consumers for unconditional canonical Core parser contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.canonicalStatementClosure
example := @TermInternals.coreRecursiveWithFuel_canonical_contract
example := @TermInternals.canonicalStatementFuelContract
example := @TermInternals.coreExpressionWithFuel_canonical_contract
example := @TermInternals.corePatternWithFuel_canonical_contract
example := @TermInternals.coreStatementWithFuel_canonical_contract
example := @expression_canonical_contract
example := @pattern_canonical_contract
example := @statement_canonical_contract
example := @block_canonical_validFor
example := @block_canonical_preservesTokenWindow
example := @block_canonical_cursorMonotoneOnSuccess
example := @block_canonical_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermExpressionProperties
/-! External consumers for recursive canonical Core expression contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.CoreStatementFuelContract
example := @TermInternals.CoreStatementFuelContract.validFor
example := @TermInternals.CoreStatementFuelContract.preservesTokenWindow
example := @TermInternals.CoreStatementFuelContract.spanValid
example := @TermInternals.coreExpressionWithFuel_contract
example := @TermInternals.coreExpressionWithFuel_validFor
example := @TermInternals.coreExpressionWithFuel_preservesTokenWindow
example := @TermInternals.coreExpressionWithFuel_preservesTokensOnSuccess
example := @TermInternals.coreExpressionWithFuel_cursor_lt_onSuccess
example := @TermInternals.coreExpressionWithFuel_cursorMonotoneOnSuccess
example := @TermInternals.coreExpressionWithFuel_startsAtCurrentTokenOnSuccess
example := @expression_contract_of_coreStatement

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermPatternFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermPatternFuelTotalityProperties

open Solcore.Syntax.Parser.TermInternals

example := @corePatternWithFuel_fuelElementTotalityContract

end Solcore.Test.SyntaxParserTermPatternFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermRecursiveFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermRecursiveFuelTotalityProperties

open Solcore.Syntax.Parser

example := @TermInternals.coreExpressionTotalityFuel
example := @TermInternals.corePatternTotalityFuel
example := @TermInternals.coreStatementTotalityFuel
example := @TermInternals.RecursiveFuelTotalityContract
example := @TermInternals.coreStatementWithFuel_cursor_lt_onSuccess
example := @TermInternals.coreRecursiveWithFuel_fuelTotalityContract

end Solcore.Test.SyntaxParserTermRecursiveFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermRecursiveProperties
/-! External consumers for simultaneous canonical term contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.RecursiveStatementValid
example := @TermInternals.RecursiveStatementClosure
example := @TermInternals.PatternParserContract
example := @TermInternals.PatternParserContract.preservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract
example := @TermInternals.RecursiveFuelContract.expressionPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.expressionCursorMonotoneOnSuccess
example := @TermInternals.RecursiveFuelContract.patternPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.statementPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.statementValidFor
example := @TermInternals.coreRecursiveWithFuel_contract
example := @TermInternals.corePatternWithFuel_contract_of_recursive

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermStatementFallbackFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermStatementFallbackFuelTotalityProperties

open Solcore.Syntax.Parser

example :=
  @StatementSimpleInternals.assignmentTail_ordinary_of_expressionFuel
example :=
  @StatementSimpleInternals.optionalAssignmentTail_ordinary_of_expressionFuel
example := @assignmentOrExpressionStatement_ordinary_of_expressionFuel
example := @assignmentOrExpressionStatement_ne_invariant_of_expressionFuel
example := @TermInternals.FuelStatementTotalityContract
example := @TermInternals.FuelStatementTotalityContract.ordinary
example := @TermInternals.FuelStatementTotalityContract.weaken
example := @TermInternals.FuelStatementTotalityContract.ne_invariant
example := @assignmentOrExpressionStatement_fuelTotalityContract

end Solcore.Test.SyntaxParserTermStatementFallbackFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermStatementFallbackTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermStatementFallbackTotalityProperties

open Solcore.Syntax.Parser

example := @StatementSimpleInternals.valueAssignOperator_invariantFreeOnValid
example := @StatementSimpleInternals.assignmentTail_invariantFreeOnValid
example := @StatementSimpleInternals.optionalAssignmentTail_invariantFreeOnValid
example := @StatementSimpleInternals.optionalSemicolon_invariantFreeOnValid
example := @assignmentOrExpressionStatement_invariantFreeOnValid
example := @assignmentOrExpressionStatement_ne_invariant
example :=
  @assignmentOrExpressionStatement_invariantFreeOnValid_of_elementTotality
example := @assignmentOrExpressionStatement_ne_invariant_of_elementTotality
example := @assignmentOrExpressionStatement_totalityContract

end Solcore.Test.SyntaxParserTermStatementFallbackTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermStatementProperties
/-! External consumers for the canonical statement recovery boundary. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.recognizedStatementOrFallback
example := @TermInternals.recognizedStatementOrFallback_validFor
example := @TermInternals.recognizedStatementOrFallback_preservesTokenWindow
example := @TermInternals.recognizedStatementOrFallback_preservesTokensOnSuccess
example :=
  @TermInternals.recognizedStatementOrFallback_preservesTokensOnSuccess_of_success
example := @TermInternals.recognizedStatementOrFallback_cursorMonotoneOnSuccess
example :=
  @TermInternals.recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess
example := @TermInternals.StatementParserContract
example := @TermInternals.StatementParserContract.preservesTokensOnSuccess
example := @TermInternals.recognizedStatementOrFallback_contract
example := @TermInternals.statementLayer
example := @TermInternals.StatementLayerInputs
example := @TermInternals.statementLayer_contract

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTermStatementTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTermStatementTotalityProperties

open Solcore.Syntax.Parser.TermInternals

example := @recognizedStatementOrFallback_invariantFreeOnValid
example := @recognizedStatementOrFallback_ne_invariant
example := @StatementTotalityContract
example := @StatementTotalityContract.ne_invariant
example := @recognizedStatementOrFallback_totalityContract

end Solcore.Test.SyntaxParserTermStatementTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTerms
/-! Direct executable regressions for canonical expressions and patterns. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private def termSource : SourceId := {
  origin := .main
  path := "parser-terms.sol"
}

private def initialState (label content : String) : IO Parser.State := do
  let file : SourceFile := { id := termSource, content }
  match Lexer.lex file with
  | .error error => throw (IO.userError
      s!"{label}: lexer invariant failed: {reprStr error}")
  | .ok lexed =>
      assertEqual lexed.diagnostics [] s!"{label} lexical diagnostics"
      pure (Parser.State.initial file lexed)

private structure ExpressionRun where
  value : Expr
  state : Parser.State

private structure PatternRun where
  value : Pattern
  state : Parser.State

private def runExpression (label content : String)
    (complete : Bool := true) : IO ExpressionRun := do
  let state ← initialState label content
  match Parser.expression state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: expression left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: expression rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: expression invariant: {reprStr error}")

private def runPattern (label content : String)
    (complete : Bool := true) : IO PatternRun := do
  let state ← initialState label content
  match Parser.pattern state with
  | .ok value next =>
      if complete && !next.atEnd then
        throw (IO.userError s!"{label}: pattern left tokens")
      pure { value, state := next }
  | .reject failure _ => throw (IO.userError
      s!"{label}: pattern rejected: {reprStr failure}")
  | .invariant error => throw (IO.userError
      s!"{label}: pattern invariant: {reprStr error}")

private inductive ExpressionShape where
  | literal (value : CoreLiteralValue)
  | identifier (name : String)
  | dotConstructor (name : String)
      (arguments : Option (List ExpressionShape))
  | unary (operator : UnaryOp) (operand : ExpressionShape)
  | binary (left : ExpressionShape) (operator : BinaryOp)
      (right : ExpressionShape)
  | index (base index : ExpressionShape)
  | call (callee : ExpressionShape) (arguments : List ExpressionShape)
  | field (base : ExpressionShape) (name : String)
  | conditional (condition thenBranch elseBranch : ExpressionShape)
  | group (inner : ExpressionShape)
  | tuple (elements : List ExpressionShape)
  | array (elements : List ExpressionShape)
  | error
  | other
  deriving Repr, BEq, Inhabited

private partial def expressionShape (expression : Expr) : ExpressionShape :=
  match expression.value with
  | .literal literal => .literal literal.value
  | .identifier name => .identifier name.value
  | .dotConstructor _ name arguments => .dotConstructor name.value
      (arguments.map fun values => values.elements.map expressionShape)
  | .unary operator operand => .unary operator.value (expressionShape operand)
  | .binary left operator right =>
      .binary (expressionShape left) operator.value (expressionShape right)
  | .index base _ index => .index (expressionShape base) (expressionShape index)
  | .call callee arguments => .call (expressionShape callee)
      (arguments.elements.map expressionShape)
  | .field base _ name => .field (expressionShape base) name.value
  | .conditional condition _ thenBranch _ elseBranch =>
      .conditional (expressionShape condition) (expressionShape thenBranch)
        (expressionShape elseBranch)
  | .group inner => .group (expressionShape inner)
  | .tuple values => .tuple (values.elements.map expressionShape)
  | .array values => .array (values.elements.map expressionShape)
  | .error => .error
  | _ => .other

private inductive PatternShape where
  | wildcard
  | literal (value : CoreLiteralValue)
  | binder (name : String)
  | constructor (leadingDot : Bool) (qualifiers : List String)
      (name : String) (arguments : Option (List PatternShape))
  | comptime (expression : ExpressionShape)
  | group (inner : PatternShape)
  | tuple (elements : List PatternShape)
  | error
  deriving Repr, BEq, Inhabited

private partial def patternShape (pattern : Pattern) : PatternShape :=
  match pattern.value with
  | .wildcard _ => .wildcard
  | .literal literal => .literal literal.value
  | .binder name => .binder name.value
  | .constructor dot qualifiers name arguments => .constructor dot.isSome
      (qualifiers.map (fun item => item.value)) name.value
      (arguments.map fun values => values.elements.toList.map patternShape)
  | .comptime _ expression => .comptime (expressionShape expression)
  | .group inner => .group (patternShape inner)
  | .tuple values => .tuple (values.elements.map patternShape)
  | .error => .error

private def ident (name : String) : ExpressionShape := .identifier name
private def bin (left : ExpressionShape) (op : BinaryOp)
    (right : ExpressionShape) : ExpressionShape := .binary left op right

private def testAtomsAndTuples : IO Unit := do
  for (source, expected) in [
      ("(x)", .group (ident "x")),
      ("(x,)", .group (ident "x")),
      ("()", .tuple []),
      ("(x, y,)", .tuple [ident "x", ident "y"]),
      (".C", .dotConstructor "C" none),
      (".C()", .dotConstructor "C" (some [])),
      ("[x, y]", .array [ident "x", ident "y"])
    ] do
    let run ← runExpression s!"atom {source}" source
    assertEqual (expressionShape run.value) expected s!"atom shape {source}"
    assertEqual (byteRange run.value.span) (0, source.utf8ByteSize)
      s!"atom span {source}"

private def testSourcePreservingWitnesses : IO Unit := do
  let proxy ← runExpression "proxy expression" "@pkg.Box<word>"
  assertEqual proxy.state.diagnostics [] "proxy expression diagnostics"
  assertEqual (byteRange proxy.value.span) (0, 14) "proxy expression span"
  match proxy.value.value with
  | .proxy marker type =>
      assertEqual (byteRange marker) (0, 1) "proxy marker span"
      assertEqual (byteRange type.span) (1, 14) "proxied type span"
      match type.value with
      | .named name (some arguments) =>
          assertEqual
            (name.value.components.toList.map (fun item => item.value))
            ["pkg", "Box"] "proxied qualified name"
          assertEqual (byteRange name.span) (1, 8) "proxied name span"
          assertEqual (byteRange arguments.span) (8, 14)
            "proxied type arguments span"
          match arguments.elements.toList with
          | [{ span, value := .named argumentName none }] =>
              assertEqual (byteRange span) (9, 13)
                "proxied argument span"
              assertEqual
                (argumentName.value.components.toList.map
                  (fun item => item.value))
                ["word"] "proxied argument name"
          | values => throw (IO.userError
              s!"proxied type arguments changed: {reprStr values}")
      | value => throw (IO.userError
          s!"proxied type changed: {reprStr value}")
  | value => throw (IO.userError
      s!"proxy expression was not preserved: {reprStr value}")

  let lambdaSource :=
    "lam(x, comptime y, comptime z: word) { return z; }"
  let lambda ← runExpression "lambda parameter distinctions" lambdaSource
  assertEqual (byteRange lambda.value.span) (0, lambdaSource.utf8ByteSize)
    "lambda expression span"
  assertEqual (lambda.state.diagnostics.map fun diagnostic =>
      (byteRange diagnostic.span, diagnostic.kind)) [
    ((7, 17), .constraintViolation .comptimeParameterRequiresType)
  ] "untyped comptime lambda diagnostic"
  match lambda.value.value with
  | .lambda keyword parameters none body =>
      assertEqual (byteRange keyword) (0, 3) "lambda keyword span"
      assertEqual (byteRange parameters.span) (3, 36)
        "lambda parameter-list span"
      match parameters.elements with
      | [
          { span := inferredSpan, value := .inferred inferredName },
          { span := errorSpan, value := .error },
          { span := typedSpan,
            value := .typed (some comptimeSpan) typedName typedType }
        ] =>
          assertEqual (byteRange inferredSpan) (4, 5)
            "inferred lambda parameter span"
          assertEqual inferredName.value "x" "inferred lambda parameter"
          assertEqual (byteRange errorSpan) (7, 17)
            "untyped comptime error placeholder span"
          assertEqual (byteRange typedSpan) (19, 35)
            "typed comptime parameter span"
          assertEqual (byteRange comptimeSpan) (19, 27)
            "typed comptime marker span"
          assertEqual typedName.value "z" "typed comptime parameter"
          match typedType.value with
          | .named typeName none =>
              assertEqual
                (typeName.value.components.toList.map
                  (fun item => item.value))
                ["word"] "typed comptime parameter type"
          | value => throw (IO.userError
              s!"typed comptime parameter type changed: {reprStr value}")
      | values => throw (IO.userError
          s!"lambda parameter distinctions changed: {reprStr values}")
      match body.value with
      | [{ value := .returnStmt (some returned), .. }] =>
          assertEqual (expressionShape returned) (ident "z")
            "lambda body preserved after parameter error"
      | statements => throw (IO.userError
          s!"lambda body changed after parameter error: {reprStr statements}")
  | value => throw (IO.userError
      s!"lambda expression changed: {reprStr value}")

private def testTrailingCommaRejection : IO Unit := do
  for (source, close) in [("[x,]", Symbol.rightBracket),
      ("f(x,)", .rightParen), (".C(x,)", .rightParen)] do
    let state ← initialState s!"trailing comma {source}" source
    match Parser.expression state with
    | .reject failure _ =>
        assertEqual failure.found (some (.symbol close))
          s!"trailing comma closing token {source}"
        assertEqual failure.expected { head := .expression, tail := [] }
          s!"trailing comma expectation {source}"
    | .ok { value := .error, .. } next =>
        if next.atEnd then
          throw (IO.userError s!"trailing comma fully consumed in {source}")
        match next.diagnostics with
        | { kind := .unexpected (some (.symbol found)) _ .expression, .. } :: _ =>
            assertEqual found close s!"recovered trailing comma {source}"
        | diagnostics => throw (IO.userError
            s!"trailing comma recovery changed in {source}: {reprStr diagnostics}")
    | result => throw (IO.userError
        s!"trailing comma accepted in {source}: {reprStr result}")

private def testPostfixAndUnary : IO Unit := do
  let postfixRun ← runExpression "postfix fold" "base[i](x).field[j]"
  assertEqual (expressionShape postfixRun.value)
    (.index (.field (.call (.index (ident "base") (ident "i"))
      [ident "x"]) "field") (ident "j")) "postfix left fold"
  assertEqual (byteRange postfixRun.value.span) (0, 19) "postfix full span"
  match postfixRun.value.value with
  | .index field outerBrackets _ =>
      assertEqual (byteRange outerBrackets) (16, 19) "outer index span"
      match field.value with
      | .field call dot name =>
          assertEqual (byteRange field.span) (0, 16) "field span"
          assertEqual (byteRange dot) (10, 11) "field dot span"
          assertEqual (byteRange name.span) (11, 16) "field name span"
          assertEqual (byteRange call.span) (0, 10) "call span"
      | _ => throw (IO.userError "postfix field shape changed")
  | _ => throw (IO.userError "postfix outer index changed")

  let unary ← runExpression "unary fold" "!~!x"
  assertEqual (expressionShape unary.value)
    (.unary .logicalNot (.unary .bitNot
      (.unary .logicalNot (ident "x")))) "unary right fold"
  assertEqual (byteRange unary.value.span) (0, 4) "unary span"

private def testPrecedenceAndAssociativity : IO Unit := do
  let source := "a || b && c == d < e | f ^ g & h + i * j"
  let run ← runExpression "all precedence" source
  assertEqual (expressionShape run.value)
    (bin (ident "a") .logicalOr
      (bin (ident "b") .logicalAnd
        (bin (ident "c") .equal
          (bin (ident "d") .less
            (bin (ident "e") .bitOr
              (bin (ident "f") .bitXor
                (bin (ident "g") .bitAnd
                  (bin (ident "h") .add
                    (bin (ident "i") .multiply (ident "j"))))))))))
    "all precedence levels"
  let left ← runExpression "left associativity" "a - b - c"
  assertEqual (expressionShape left.value)
    (bin (bin (ident "a") .subtract (ident "b"))
      .subtract (ident "c")) "left associativity"
  for (source, operator) in [("a < b < c", BinaryOp.less),
      ("a == b == c", .equal)] do
    let prefixRun ← runExpression s!"nonassociative {source}" source false
    assertEqual (expressionShape prefixRun.value)
      (bin (ident "a") operator (ident "b")) s!"nonassociative prefix {source}"
    assertEqual prefixRun.state.remainingCount 2 s!"nonassociative remainder {source}"

private def testConditionals : IO Unit := do
  let right ← runExpression "right conditional" "a ? b : c ? d : e"
  assertEqual (expressionShape right.value)
    (.conditional (ident "a") (ident "b")
      (.conditional (ident "c") (ident "d") (ident "e")))
    "right-associative conditional"
  let nested ← runExpression "nested then" "a ? b ? c : d : e"
  assertEqual (expressionShape nested.value)
    (.conditional (ident "a")
      (.conditional (ident "b") (ident "c") (ident "d")) (ident "e"))
    "nested then conditional"

private def testExpressionRecovery : IO Unit := do
  let run ← runExpression "atom recovery" "+ -," false
  assertEqual (expressionShape run.value) .error "atom recovery node"
  assertEqual (byteRange run.value.span) (0, 3) "atom recovery span"
  assertEqual run.state.peekKind? (some (.symbol .comma)) "atom recovery boundary"
  assertEqual (run.state.diagnostics.map fun item =>
      (byteRange item.span, item.kind)) [
    ((0, 1), .unexpected (some (.symbol .plus))
      { head := .expression, tail := [] } .expression),
    ((0, 3), .recovered .expressionAtom)
  ] "atom recovery diagnostics"

private def testPatternForms : IO Unit := do
  for (source, expected) in [
      ("_", PatternShape.wildcard),
      ("42", .literal (.decimal "42")),
      ("true", .binder "true"),
      ("λvalue", .binder "λvalue"),
      ("Value", .constructor false [] "Value" none),
      (".C", .constructor true [] "C" none),
      (".C(x)", .constructor true [] "C" (some [.binder "x"])),
      ("(x)", .group (.binder "x")),
      ("()", .tuple []),
      ("(x, _,)", .tuple [.binder "x", .wildcard])
    ] do
    let run ← runPattern s!"pattern {source}" source
    assertEqual (patternShape run.value) expected s!"pattern shape {source}"

  let qualified ← runPattern "qualified constructor"
    "pkg.Option.Some(x, _)"
  assertEqual (patternShape qualified.value)
    (.constructor false ["pkg", "Option"] "Some"
      (some [.binder "x", .wildcard])) "qualified constructor shape"
  assertEqual (byteRange qualified.value.span) (0, 21) "constructor span"
  match qualified.value.value with
  | .constructor _ _ _ (some arguments) =>
      assertEqual (byteRange arguments.span) (15, 21) "constructor args span"
  | _ => throw (IO.userError "qualified constructor arguments changed")

  let comptime ← runPattern "comptime pattern" "comptime x + 1"
  assertEqual (patternShape comptime.value)
    (.comptime (bin (ident "x") .add (.literal (.decimal "1"))))
    "comptime expression pattern"
  assertEqual (byteRange comptime.value.span) (0, 14) "comptime pattern span"
  let comptimeStart ← initialState "comptime pattern start" "comptime x"
  assertEqual (Parser.startsPattern comptimeStart) true
    "comptime begins a pattern"

private def testPatternRecovery : IO Unit := do
  let run ← runPattern "pattern recovery" "+ - =>" false
  assertEqual (patternShape run.value) .error "pattern recovery node"
  assertEqual (byteRange run.value.span) (0, 3) "pattern recovery span"
  assertEqual run.state.peekKind? (some (.symbol .fatArrow))
    "pattern recovery boundary"
  assertEqual (run.state.diagnostics.map fun item => item.kind) [
    .unexpected (some (.symbol .plus))
      { head := .pattern, tail := [] } .pattern,
    .recovered .pattern
  ] "pattern recovery diagnostics"

/-- Run direct expression and pattern parser regressions. -/
def testSyntaxParserTerms : IO Unit := do
  testAtomsAndTuples
  testSourcePreservingWitnesses
  testTrailingCommaRejection
  testPostfixAndUnary
  testPrecedenceAndAssociativity
  testConditionals
  testExpressionRecovery
  testPatternForms
  testPatternRecovery

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxReturnStatementRejectionTraceProperties
/-! Independent return-rejection consumers preserve the first failure,
semicolon guard priority, repeated expression events, and source-window reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxReturnStatementRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar

variable {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder →
    List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

example := @OptionalReturnValueTraceRejects.ordinary
example := @ReturnStatementTraceRejects.ordinary
example := @OptionalReturnValueTraceRejects.result_unique
example := @ReturnStatementTraceRejects.result_unique
example := @OptionalReturnValueTraceRejects.disjoint_success
example := @ReturnStatementTraceRejects.disjoint_success

/-- A current semicolon prevents any optional-value rejection regardless of
the outcomes described by the abstract expression grammar. -/
theorem semicolon_prevents_value_rejection
    {input : Remainder} {span : SourceSpan}
    (current : TokenAt input.tokens input.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    ¬ ∃ rejected diagnostic trace,
      OptionalReturnValueTraceRejects expressionRejects source endByte input rejected diagnostic trace := by
  rintro ⟨_, _, _, rejection⟩
  cases rejection with
  | expressionRejected absent _ => exact absent ⟨span, current⟩

/-- Return forwards the inner expression's own report and preceding events;
it does not replace that report with a later semicolon expectation. -/
theorem expression_rejection_is_first_failure
    {input afterMarker rejected : Remainder} {markerSpan : SourceSpan}
    {diagnostic first second : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (rejectedValue : expressionRejects source endByte afterMarker rejected diagnostic
      [first, second, first]) :
    ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input rejected diagnostic [first, second, first] :=
  .valueRejected markerSpan marker (.expressionRejected absent rejectedValue)

/-- A successful expression followed by the window end keeps its repeated
events and reports the required semicolon at the exact supplied byte boundary. -/
theorem missing_semicolon_keeps_expression_events
    {input afterMarker afterValue : Remainder} {markerSpan : SourceSpan}
    {value : Expr} {event : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (parsedValue : expressionTrace source endByte afterMarker value afterValue [event, event])
    (atEnd : afterValue.endIndex ≤ afterValue.cursor) :
    ReturnStatementTraceRejects expressionTrace expressionRejects source endByte
      input afterValue {
        span := { source, startByte := endByte, endByte },
        kind := .unexpected none { head := .symbol .semicolon, tail := [] } .statement
      } [event, event] := by
  refine .semicolonRejected markerSpan marker (.present notEmpty parsedValue) ?_
    (.reported (.windowEnd atEnd))
  rintro ⟨span, inside, _⟩
  exact Nat.not_lt_of_ge atEnd inside

/-- An omitted return expression cannot later reach semicolon rejection:
its omission witness already fixes a present semicolon at the same remainder. -/
theorem absent_value_excludes_semicolon_rejection
    {input afterValue : Remainder} {trace : List ParseDiagnostic}
    (parsed : OptionalReturnValueTraceParses expressionTrace source endByte
      input none afterValue trace) :
    ¬ TokenKindAbsentAt afterValue.tokens afterValue.endIndex afterValue.cursor (.symbol .semicolon) := by
  intro absent
  cases parsed with
  | absent span current => exact absent ⟨span, current⟩

end Solcore.Test.SyntaxReturnStatementRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserReturnStatementRejectionTraceProperties
/-! Return execution consumers expose their abstract expression contracts.
Every incoming event remains before the specified rejecting value's events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserReturnStatementRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic →
    List ParseDiagnostic → Prop}

example := @StatementSimpleInternals.optionalReturnValue_reject_trace_sound
example := @StatementSimpleInternals.optionalReturnValue_trace_reject_complete
example := @StatementSimpleInternals.optionalReturnValue_trace_reject_iff
example := @returnStatement_reject_trace_sound
example := @returnStatement_trace_reject_complete
example := @returnStatement_trace_reject_iff
example := @returnStatement_trace_reject_failure_iff

/-- The semicolon guard bypasses even an expression parser that would reject
at that input. The complete state and all existing diagnostics stay unchanged. -/
theorem semicolon_bypasses_expression_failure
    {input : State} {span : SourceSpan}
    (current : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    StatementSimpleInternals.optionalReturnValue expression input = .ok none input :=
  StatementSimpleInternals.optionalReturnValue_eq_ok_none_of_tokenAt expression current

/-- Earlier expression events and their duplicates survive before the exact
window-end semicolon failure; the report is not part of the appended trace. -/
theorem missing_semicolon_retains_events_before_full_failure
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {afterMarker afterValue : Remainder} {markerSpan : SourceSpan}
    {value : Expr} {event : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (parsedValue : expressionTrace input.file.id input.window.endByte
      afterMarker value afterValue [event, event])
    (atEnd : afterValue.endIndex ≤ afterValue.cursor) :
    ∃ rejected, returnStatement expression input = .reject {
        span := { source := input.file.id, startByte := input.window.endByte, endByte := input.window.endByte },
        found := none, expected := { head := .symbol .semicolon, tail := [] }, context := .statement
      } rejected ∧ rejected.declarativeRemainder = afterValue ∧
      rejected.diagnostics = input.diagnostics ++ [event, event] :=
  (returnStatement_trace_reject_failure_iff successSound rejectSound successComplete rejectComplete
    contextFrame).mp
    (SyntaxReturnStatementRejectionTraceProperties.missing_semicolon_keeps_expression_events
      marker notEmpty parsedValue atEnd)

/-- The expression's first failure remains separate from its own event list;
return processing introduces no semicolon failure after it. -/
theorem expression_report_is_not_replaced
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression)
    {input : State} {afterMarker remainder : Remainder} {markerSpan : SourceSpan}
    {diagnostic first second : ParseDiagnostic}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (notEmpty : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon))
    (rejectedValue : expressionRejects input.file.id input.window.endByte afterMarker remainder
      diagnostic [first, second, first]) :
    ∃ failure rejected, returnStatement expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ [first, second, first] :=
  returnStatement_trace_reject_complete successComplete rejectComplete contextFrame
    (.valueRejected markerSpan marker (.expressionRejected notEmpty rejectedValue))

end Solcore.Test.SyntaxParserReturnStatementRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxReturnStatementTraceExactnessProperties
/-! Conditional return exactness, outcome existence, and isolated block
composition, with every abstract expression assumption visible to the caller. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxReturnStatementTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

variable {expression : Parser Expr}
  {expressionTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {expressionRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}

theorem return_rejection_excludes_every_success
    {source : SourceId} {endByte : Nat}
    (expressions : ExpressionTraceExactOutcomeSpec expressionTrace expressionRejects source endByte)
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects expressionTrace expressionRejects
      source endByte input rejected diagnostic trace) :
    ¬ ∃ statement output events,
      ReturnStatementTraceParses expressionTrace source endByte input statement output events :=
  (returnStatementTraceExactOutcomeSpec expressions).successRejectDisjoint rejection

/-- Independent expression existence and execution completeness suffice for
an actual ordinary return result; exactness and soundness are not assumed. -/
theorem return_execution_has_ordinary_outcome
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) (input : State)
    (expressions : ExpressionTraceOutcomeExists expressionTrace expressionRejects
      input.file.id input.window.endByte) :
    (∃ statement output trace, returnStatement expression input = .ok statement output ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace, returnStatement expression input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases returnStatementTrace_exists_outcome expressions input.declarativeRemainder with successful | rejected
  · rcases successful with ⟨statement, after, trace, parsed⟩
    rcases returnStatement_trace_success_complete successComplete parsed with
      ⟨output, result, _, diagnostics⟩
    exact Or.inl ⟨statement, output, trace, result, diagnostics⟩
  · rcases rejected with ⟨after, diagnostic, trace, rejection⟩
    rcases returnStatement_trace_reject_complete successComplete rejectComplete contextFrame rejection with
      ⟨failure, rejected, result, _, _, diagnostics⟩
    exact Or.inr ⟨failure, rejected, trace, result, diagnostics⟩

/-- Abstract expression contracts discharge every statement assumption for
isolated blocks restricted to returns, including a recovered inner rejection. -/
theorem isolated_return_block_trace_iff
    (successSound : ExpressionTraceSuccessSound expression expressionTrace)
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (successComplete : ExpressionTraceSuccessComplete expression expressionTrace)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    (contextFrame : ExpressionSuccessContext expression) (policy : TailExpressionPolicy)
    {input : State} {body : Block} {after : Remainder} {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses (CoreBlockTraceParses (ReturnStatementTraceParses expressionTrace) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses expressionTrace)
        (ReturnStatementTraceRejects expressionTrace expressionRejects) policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, isolateBlock (coreBlock (returnStatement expression) policy) input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  isolatedCoreBlock_trace_success_iff (returnStatement_trace_success_sound successSound)
    (returnStatement_reject_trace_sound successSound rejectSound contextFrame)
    (returnStatement_trace_success_complete successComplete)
    (returnStatement_trace_reject_complete successComplete rejectComplete contextFrame)
    (returnStatement_success_context contextFrame) policy

end Solcore.Test.SyntaxReturnStatementTraceExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxStatementValidity
/-! External consumers for recursive canonical statement validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @ForItem.ValidFor
example := @Statement.ValidFor
example := @MatchCase.ValidFor
example := @MatchArms.ValidFor
example := @Statement.ValidFor.span_valid

example (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (span : SourceSpan) (value : Option Expr)
    (spanValid : span.ValidFor file)
    (valueValid : ∀ expression ∈ value, expressionValid file expression) :
    Statement.ValidFor expressionValid patternValid yulValid file {
      span
      value := .returnStmt value
    } :=
  .returnStmt spanValid valueValid

example (expressionValid : SourceFile → Expr → Prop)
    (patternValid : SourceFile → Pattern → Prop)
    (yulValid : SourceFile → YulStmt → Prop)
    (file : SourceFile) (span : SourceSpan) (body : List Statement)
    (spanValid : span.ValidFor file)
    (bodyValid : ∀ statement ∈ body,
      Statement.ValidFor expressionValid patternValid yulValid file statement) :
    Statement.ValidFor expressionValid patternValid yulValid file {
      span
      value := .block body
    } :=
  .block spanValid bodyValid

end Tests
end
