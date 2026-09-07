import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.ReturnStatementSuccessTraceProperties
import Solcore.Syntax.Parser.ReturnStatementRejectionTraceCompletenessProperties
import Solcore.Syntax.Parser.CoreBlockIsolationTraceProperties

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
