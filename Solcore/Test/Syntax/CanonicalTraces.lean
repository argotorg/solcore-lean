import Solcore.Test.Syntax.Statements
import Solcore.Syntax.Parser.DelimitedTrailingTraceContextProperties
import Solcore.Syntax.Parser.IdentifierExpressionTraceProperties
import Solcore.Syntax.Parser.DelimitedTrailingRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Test.Syntax.ExpressionAtoms
import Solcore.Syntax.Parser.FunctionReturnsTraceProperties
import Solcore.Syntax.Parser.FunctionReturnsRejectionTraceProperties
import Solcore.Test.Syntax.Types
import Solcore.Test.Syntax.Recovery
import Solcore.Syntax.Parser.FunctionTypeSuccessTraceProperties
import Solcore.Syntax.Parser.FunctionTypeRejectionTraceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsTraceProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsRejectionTraceProperties
import Solcore.Syntax.Parser.ParenthesizedTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ParenthesizedRejectionTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ProxyExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.Type
import Solcore.Syntax.Lexer
import Solcore.Syntax.Parser.ProxyTypeSuccessTraceProperties
import Solcore.Syntax.Parser.ProxyTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeQualifiedNameTraceOutcomeProperties
import Solcore.Syntax.Parser.QualifiedNameRejectionTraceStateProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties
import Solcore.Syntax.Parser.TupleTypeSuccessTraceProperties
import Solcore.Syntax.Parser.TupleTypeRejectionTraceProperties
import Solcore.Syntax.Parser.CanonicalParserTotalityProperties
import Solcore.Syntax.DeclarativeIdentifierCascadeProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.DeclarativeArrayLiteralTraceProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeReturnStatementTraceExactnessProperties
import Solcore.Syntax.DeclarativeRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ComptimeTypeSuccessTraceProperties
import Solcore.Syntax.Parser.TypeExprTraceSoundnessProperties
import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeDotConstructorTraceOutcomeProperties
import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProperties
import Solcore.Syntax.DeclarativeFunctionReturnsRejectionTraceProperties
import Solcore.Syntax.DeclarativeFunctionTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsTraceProperties
import Solcore.Syntax.DeclarativeNamedTypeArgumentsRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.NamedTypeArgumentsTracePrimitiveProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceOutcomeProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceProtectionProperties
import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeProxyExpressionRejectionTraceProperties
import Solcore.Syntax.Parser.ProxyExpressionRejectionTraceProperties
import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeTupleTypeRejectionTraceProperties
import Solcore.Syntax.DeclarativeTypeDispatchTraceProperties
import Solcore.Syntax.Parser.TypeDispatchSelectionTraceProperties

/-!
# Canonical and protected trace tests

Worked traces of canonical inputs for each delimited, type and expression form, and the protected
trace properties that keep those traces apart from their neighbours.
-/

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalControlBlockTraceExamples
/-! Canonical sources connect actual lexing to the existing independent
control-block consumers. Only the two lexical fixtures use kernel decision;
all statement/block outcomes reuse the proved trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalControlBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private theorem lex_ok_of_toOption {file : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex file).toOption = some lexed) : Lexer.lex file = .ok lexed := by
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

def successFile : SourceFile := {
  id := { origin := .main, path := "control-block-trace.sol" }
  content := "{ break; break; } tail"
}
def successSpan (first last : Nat) : SourceSpan := {
  source := successFile.id, startByte := first, endByte := last
}
def successLexed : LexedFile := {
  source := successFile.id, comments := [], diagnostics := []
  tokens := [
    { span := successSpan 0 1, value := .symbol .leftBrace },
    { span := successSpan 2 7, value := .keyword .breakKw },
    { span := successSpan 7 8, value := .symbol .semicolon },
    { span := successSpan 9 14, value := .keyword .breakKw },
    { span := successSpan 14 15, value := .symbol .semicolon },
    { span := successSpan 16 17, value := .symbol .rightBrace },
    { span := successSpan 18 22, value := .identifier "tail" }]
}
def successBody : Block := {
  span := successSpan 0 17
  value := [{ span := successSpan 2 8, value := .breakStmt },
    { span := successSpan 9 15, value := .breakStmt }]
}

set_option maxRecDepth 8192 in
theorem success_lexes : Lexer.lex successFile = .ok successLexed := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The real source lexer supplies the exact input for both raw and isolated
break-only blocks. Both preserve arbitrary prior events and the trailing token. -/
theorem canonical_break_pair (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ lexed raw isolated,
      Lexer.lex successFile = .ok lexed ∧
      coreBlock breakStatement policy
          { State.initial successFile lexed with diagnosticsRev := prior.reverse } =
        .ok successBody raw ∧
      isolateBlock (coreBlock breakStatement policy)
          { State.initial successFile lexed with diagnosticsRev := prior.reverse } =
        .ok successBody isolated ∧
      raw.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      isolated.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      raw.diagnostics = prior ∧ isolated.diagnostics = prior := by
  have rawResult : ∃ output, coreBlock breakStatement policy
        { State.initial successFile successLexed with diagnosticsRev := prior.reverse } =
      .ok successBody output ∧
      output.declarativeRemainder = { tokens := successLexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      output.diagnostics = prior := SyntaxControlLeafBlockTraceExamples.break_pair_raw policy prior
  have isolatedResult : ∃ output, isolateBlock (coreBlock breakStatement policy)
        { State.initial successFile successLexed with diagnosticsRev := prior.reverse } =
      .ok successBody output ∧
      output.declarativeRemainder = { tokens := successLexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      output.diagnostics = prior := SyntaxControlLeafBlockTraceExamples.break_pair_isolated policy prior
  rcases rawResult with ⟨raw, rawParsed, rawAfter, rawEvents⟩
  rcases isolatedResult with ⟨isolated, isolatedParsed, isolatedAfter, isolatedEvents⟩
  exact ⟨successLexed, raw, isolated, success_lexes, rawParsed, isolatedParsed,
    rawAfter, isolatedAfter, rawEvents, isolatedEvents⟩

def rejectionFile : SourceFile := {
  id := { origin := .main, path := "control-block-reject.sol" }
  content := "{ break; break + } tail"
}
def rejectionSpan (first last : Nat) : SourceSpan := {
  source := rejectionFile.id, startByte := first, endByte := last
}
def rejectionLexed : LexedFile := {
  source := rejectionFile.id, comments := [], diagnostics := []
  tokens := [
    { span := rejectionSpan 0 1, value := .symbol .leftBrace },
    { span := rejectionSpan 2 7, value := .keyword .breakKw },
    { span := rejectionSpan 7 8, value := .symbol .semicolon },
    { span := rejectionSpan 9 14, value := .keyword .breakKw },
    { span := rejectionSpan 15 16, value := .symbol .plus },
    { span := rejectionSpan 17 18, value := .symbol .rightBrace },
    { span := rejectionSpan 19 23, value := .identifier "tail" }]
}
def semicolonFailure : Failure := {
  span := rejectionSpan 15 16, found := some (.symbol .plus)
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}
def continueFailure : Failure := {
  span := rejectionSpan 2 7, found := some (.keyword .breakKw)
  expected := { head := .keyword .continueKw, tail := [] }, context := .statement
}

set_option maxRecDepth 8192 in
theorem rejection_lexes : Lexer.lex rejectionFile = .ok rejectionLexed := by
  apply lex_ok_of_toOption
  decide +kernel

/-- The same canonical source rejects later for break but at its first
keyword for continue. Both full failures remain uncommitted on raw rejection. -/
theorem canonical_control_failure_priority (policy : TailExpressionPolicy)
    (prior : List ParseDiagnostic) :
    ∃ lexed rejectedBreak rejectedContinue,
      Lexer.lex rejectionFile = .ok lexed ∧
      coreBlock breakStatement policy
          { State.initial rejectionFile lexed with diagnosticsRev := prior.reverse } =
        .reject semicolonFailure rejectedBreak ∧
      coreBlock continueStatement policy
          { State.initial rejectionFile lexed with diagnosticsRev := prior.reverse } =
        .reject continueFailure rejectedContinue ∧
      rejectedBreak.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 7, cursor := 4 } ∧
      rejectedContinue.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 7, cursor := 1 } ∧
      rejectedBreak.diagnostics = prior ∧ rejectedContinue.diagnostics = prior := by
  have breakResult : ∃ output, coreBlock breakStatement policy
        { State.initial rejectionFile rejectionLexed with diagnosticsRev := prior.reverse } =
      .reject semicolonFailure output ∧
      output.declarativeRemainder = { tokens := rejectionLexed.tokens.toArray, endIndex := 7, cursor := 4 } ∧
      output.diagnostics = prior := SyntaxControlLeafBlockRejectionExamples.break_later_semicolon_failure policy prior
  have continueResult : ∃ output, coreBlock continueStatement policy
        { State.initial rejectionFile rejectionLexed with diagnosticsRev := prior.reverse } =
      .reject continueFailure output ∧
      output.declarativeRemainder = { tokens := rejectionLexed.tokens.toArray, endIndex := 7, cursor := 1 } ∧
      output.diagnostics = prior := SyntaxControlLeafBlockRejectionExamples.continue_keyword_failure_has_priority policy prior
  rcases breakResult with ⟨breakOutput, breaks, breakAfter, breakEvents⟩
  rcases continueResult with ⟨continueOutput, continues, continueAfter, continueEvents⟩
  exact ⟨rejectionLexed, breakOutput, continueOutput, rejection_lexes, breaks, continues,
    breakAfter, continueAfter, breakEvents, continueEvents⟩

/-- Canonical lexing followed by balanced recovery commits the semicolon
report once, returns an empty body, and restores the parent before `tail`. -/
theorem canonical_break_recovery (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex rejectionFile = .ok lexed ∧
      isolateBlock (coreBlock breakStatement policy)
          { State.initial rejectionFile lexed with diagnosticsRev := prior.reverse } =
        .ok { span := rejectionSpan 0 18, value := [] } output ∧
      output.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = rejectionFile ∧ output.window = { endIndex := 7, endByte := 23 } ∧
      output.peek? = some { span := rejectionSpan 19 23, value := .identifier "tail" } := by
  have recovered : ∃ output,
      isolateBlock (coreBlock breakStatement policy)
          { State.initial rejectionFile rejectionLexed with diagnosticsRev := prior.reverse } =
        .ok { span := rejectionSpan 0 18, value := [] } output ∧
      output.declarativeRemainder = { tokens := rejectionLexed.tokens.toArray, endIndex := 7, cursor := 6 } ∧
      output.diagnostics = prior ++ [semicolonFailure.toDiagnostic] ∧
      output.file = rejectionFile ∧ output.window = { endIndex := 7, endByte := 23 } ∧
      output.peek? = some { span := rejectionSpan 19 23, value := .identifier "tail" } :=
    SyntaxControlLeafBlockRejectionExamples.break_captured_failure_restores_parent policy prior
  rcases recovered with ⟨output, result⟩
  exact ⟨rejectionLexed, output, rejection_lexes, result⟩

end Solcore.Test.SyntaxCanonicalControlBlockTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples
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
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalDelimitedTrailingRejectionTraceExamples
/-! After a comma, a non-closing token invokes the checked-name child. Without
a comma, the same token reports the ordered delimiter pair instead. Both paths
retain earlier name events without committing their final rejection report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalDelimitedTrailingRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

private def childText : String := "<a-b,+> tail"
private def childTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def childFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}
private def delimiterText : String := "<a-b +> tail"
private def delimiterTokens : List Token := [sym 0 1 .less, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def delimiterFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .greater] }, context := .expression
}

private theorem child_rejected : TrailingDelimitedListTraceRejects .less .greater false .expression
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder childTokens 0) (remainder childTokens 3) childFailure.toDiagnostic [hyphen nameA] := by
  have child : IdentifierExpressionTraceRejects source 12 (remainder childTokens 3)
      (remainder childTokens 3) childFailure.toDiagnostic [] :=
    ⟨by constructor <;> simp [TokenKindAbsentAt, TokenAt, remainder, childTokens, sym],
      .absent (by simp [IdentifierAbsentAt, TokenAt, remainder, childTokens, sym]),
      .reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩), rfl⟩
  exact .tailRejected (span 0 1) (afterOpening := remainder childTokens 1)
    (afterFirst := remainder childTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩ .disabled
    (name_trace (input := remainder childTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.elementRejected (span 4 5) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, childTokens, sym]) child)

private theorem delimiter_rejected : TrailingDelimitedListTraceRejects .less .greater false .expression
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder delimiterTokens 0) (remainder delimiterTokens 2) delimiterFailure.toDiagnostic [hyphen nameA] :=
  .tailRejected (span 0 1) (afterOpening := remainder delimiterTokens 1)
    (afterFirst := remainder delimiterTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩ .disabled
    (name_trace (input := remainder delimiterTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.delimiterMissing
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, sym])
      (.reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩)))

private theorem rejection_exec (content : String) (inputTokens : List Token) (prior : List ParseDiagnostic)
    (failure : Failure) (after : Remainder)
    (rejection : TrailingDelimitedListTraceRejects .less .greater false .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source (file content).content.utf8ByteSize
      (remainder inputTokens 0) after failure.toDiagnostic [hyphen nameA]) :
    ∃ output, delimited .less .greater false identifierExpression .expression .expression
        (initial content inputTokens prior) = .reject failure output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.tokens = inputTokens.toArray ∧ output.window = (initial content inputTokens prior).window := by
  rcases (delimited_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      .less .greater false .expression .expression (input := initial content inputTokens prior)).mp rejection with
    ⟨output, result, afterEq, diagnostics⟩
  have frame := delimited_preservesTokenWindow .less .greater false identifierExpression .expression .expression
    identifierExpression_preservesTokenWindow (initial content inputTokens prior)
  rw [result] at frame
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

set_option maxRecDepth 16384 in
theorem rejected_child_lexes : Lexer.lex (file childText) = .ok (carrier childTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem missing_delimiter_lexes : Lexer.lex (file delimiterText) = .ok (carrier delimiterTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_child_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file childText) = .ok lexed ∧
      delimited .less .greater false identifierExpression .expression .expression
        { State.initial (file childText) lexed with diagnosticsRev := prior.reverse } = .reject childFailure output ∧
      output.declarativeRemainder = remainder childTokens 3 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 6, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[5]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec childText childTokens prior _ _ child_rejected with
    ⟨output, result, after, events, tokenEq, window⟩
  refine ⟨carrier childTokens, output, rejected_child_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokenEq]
  rfl

theorem canonical_delimiter_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file delimiterText) = .ok lexed ∧
      delimited .less .greater false identifierExpression .expression .expression
        { State.initial (file delimiterText) lexed with diagnosticsRev := prior.reverse } = .reject delimiterFailure output ∧
      output.declarativeRemainder = remainder delimiterTokens 2 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 5, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[4]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec delimiterText delimiterTokens prior _ _ delimiter_rejected with
    ⟨output, result, after, events, tokenEq, window⟩
  refine ⟨carrier delimiterTokens, output, missing_delimiter_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokenEq]
  rfl

end Solcore.Test.SyntaxCanonicalDelimitedTrailingRejectionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalDotConstructorTraceExamples
/-! Canonical source-to-dot-constructor traces reuse the independently proved
consumer outcomes. The rejection carrier matches its existing explicit fixture.
Only lexer equations use kernel decision; parser outcomes use trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalDotConstructorTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "dot-rejection-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameE : Identifier := { span := span 9 12, value := "e-f" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def nameExpr (name : Identifier) : Expr := { span := name.span, value := .identifier name }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def initial (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file text) (carrier tokens) with diagnosticsRev := prior.reverse
}
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

private def successText : String := ".a-b(c-d,e-f) tail"
private def successTokens : List Token := [sym 0 1 .dot, nameToken nameA, sym 4 5 .leftParen,
  nameToken nameC, sym 8 9 .comma, nameToken nameE, sym 12 13 .rightParen,
  { span := span 14 18, value := .identifier "tail" }]
private def successValue : Expr := {
  span := span 0 13
  value := .dotConstructor (span 0 1) nameA
    (some { span := span 4 13, elements := [nameExpr nameC, nameExpr nameE] })
}

private theorem success_from_tokens (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial successText successTokens prior) =
        .ok successValue output ∧ output.declarativeRemainder = remainder successTokens 7 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, hyphen nameE] := by
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse,
    successValue, nameExpr, hyphen, SourceSpan.cover, span] using
    SyntaxDotConstructorSuccessTraceProperties.checked_constructor_and_arguments_keep_event_order
      (input := initial successText successTokens prior)
      (dotSpan := span 0 1) (openingSpan := span 4 5) (commaSpan := span 8 9) (closingSpan := span 12 13)
      (name := nameA) (first := nameC) (second := nameE)
      (afterDot := remainder successTokens 1) (afterName := remainder successTokens 2)
      (afterOpening := remainder successTokens 3) (afterFirst := remainder successTokens 4)
      (afterComma := remainder successTokens 5) (afterSecond := remainder successTokens 6)
      (after := remainder successTokens 7)
      ⟨⟨by change 0 < 8; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameC; decide)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩
      (by unfold IdentifierHyphenSpelling nameE; decide) ⟨⟨by decide, rfl⟩, rfl⟩

private def rejectionText : String := ".a-b(c-d,+) tail"
private def rejectionTokens : List Token := [sym 0 1 .dot, nameToken nameA, sym 4 5 .leftParen,
  nameToken nameC, sym 8 9 .comma, sym 9 10 .plus, sym 10 11 .rightParen,
  { span := span 12 16, value := .identifier "tail" }]
private def plusFailure : Failure := {
  span := span 9 10, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem rejection_from_tokens (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial rejectionText rejectionTokens prior) =
        .reject plusFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] :=
  SyntaxDotConstructorRejectionTraceProperties.name_and_argument_events_precede_uncommitted_failure prior

private theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem success_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 16384 in
theorem rejection_lexes : Lexer.lex (file rejectionText) = .ok (carrier rejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- Canonical lexing connects directly to the actual parser's root state.
The outer expression, dot, name, and argument-list spans are all retained;
constructor-name and two argument-name events follow arbitrary prior events. -/
theorem canonical_dot_constructor_success (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      dotConstructor identifierExpression
        { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } = .ok successValue output ∧
      output.declarativeRemainder = remainder successTokens 7 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC, hyphen nameE] ∧
      output.file = file successText ∧ output.window = { endIndex := 8, endByte := 18 } ∧
      output.peek? = some { span := span 14 18, value := .identifier "tail" } := by
  rcases success_from_tokens prior with ⟨output, result, after, events⟩
  have frame := dotConstructor_success_context identifierExpression_success_context result
  refine ⟨carrier successTokens, output, success_lexes, result, after, events, frame.1, frame.2, ?_⟩
  have tokens := congrArg Remainder.tokens after
  have endpoint := congrArg Remainder.endIndex after
  have cursor := congrArg Remainder.cursor after
  change output.tokens = successTokens.toArray at tokens
  change output.window.endIndex = 8 at endpoint
  change output.cursor = 7 at cursor
  simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
  rfl

/-- The comma invokes the actual checked-name child and its full identifier
failure escapes unchanged. Only the constructor and first argument events are
committed; the plus, closing parenthesis, and later tail remain unconsumed. -/
theorem canonical_dot_constructor_rejection (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectionText) = .ok lexed ∧
      dotConstructor identifierExpression
        { State.initial (file rejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject plusFailure output ∧ output.declarativeRemainder = remainder rejectionTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.window = { endIndex := 8, endByte := 16 } ∧ output.peek? = some (sym 9 10 .plus) ∧
      output.tokens[7]? = some { span := span 12 16, value := .identifier "tail" } := by
  rcases rejection_from_tokens prior with ⟨output, result, after, events⟩
  have frame := dotConstructor_preservesTokenWindow identifierExpression
    identifierExpression_preservesTokenWindow (initial rejectionText rejectionTokens prior)
  rw [result] at frame
  refine ⟨carrier rejectionTokens, output, rejection_lexes, result, after, events, frame.2, ?_, ?_⟩
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = rejectionTokens.toArray at tokens
    change output.window.endIndex = 8 at endpoint
    change output.cursor = 5 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl
  · rw [frame.1]
    rfl

end Solcore.Test.SyntaxCanonicalDotConstructorTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalFunctionReturnsTraceExamples
/-! Canonical optional function returns execute real typeExpr leaves. The
empty list bypasses any supplied child; successful and rejected checked names
retain exact parent spans, full states, windows, and following source tokens. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalFunctionReturnsTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-function-returns-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 7, value := .identifier "returns" }
private def name : Identifier := { span := span 8 11, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def ty : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def emptyText : String := "returns() tail"
private def emptyTokens : List Token := [marker, sym 7 8 .leftParen, sym 8 9 .rightParen, tailToken 10]
private def successText : String := "returns(a-b,) tail"
private def successTokens : List Token := [marker, sym 7 8 .leftParen, nameToken,
  sym 11 12 .comma, sym 12 13 .rightParen, tailToken 14]
private def rejectedText : String := "returns(a-b +) tail"
private def rejectedTokens : List Token := [marker, sym 7 8 .leftParen, nameToken,
  sym 12 13 .plus, sym 13 14 .rightParen, tailToken 15]

private theorem checked_child (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 2 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .dot))
    (noArgs : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .less)) :
    typeExpr (state content tokens prior 2 []) = .ok ty (state content tokens prior 3 [event]) :=
  checked_name_type token (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
    noDot noArgs (by decide) (by decide)

private theorem empty_exec (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    parseFunctionReturns nested (state emptyText emptyTokens prior 0 []) =
      .ok (some { span := span 7 9, elements := [] }) (state emptyText emptyTokens prior 3 []) := by
  let s := state emptyText emptyTokens prior
  have reduced := parseFunctionReturns_eq_of_present nested
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 4; decide, rfl⟩, rfl⟩
  have values := empty_list_bypasses_any_child nested .leftParen .rightParen .typeExpr .typeExpr
    (input := s 1 []) (afterOpening := (s 2 []).declarativeRemainder)
    (after := (s 3 []).declarativeRemainder) (openingSpan := span 7 8) (closingSpan := span 8 9)
    ⟨⟨by change 1 < 4; decide, rfl⟩, rfl⟩ ⟨⟨by change 2 < 4; decide, rfl⟩, rfl⟩
  rw [reduced]
  change (match delimited .leftParen .rightParen true nested .typeExpr .typeExpr (s 1 []) with
    | .ok values output => Reply.ok (some values) output
    | .reject failure rejected => Reply.reject failure rejected
    | .invariant error => Reply.invariant error) = _
  rw [values]
  rfl

private theorem success_exec (prior : List ParseDiagnostic) :
    parseFunctionReturns typeExpr (state successText successTokens prior 0 []) =
      .ok (some { span := span 7 13, elements := [ty] }) (state successText successTokens prior 5 [event]) := by
  let s := state successText successTokens prior
  have reduced := parseFunctionReturns_eq_of_present typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have child := checked_child successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have opening := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 7 8 .leftParen) .rightParen
    .typeExpr .typeExpr 4 [ty] (input := s 3 [event])
    (afterComma := (s 4 [event]).declarativeRemainder) (after := (s 5 [event]).declarativeRemainder)
    (commaSpan := span 11 12) (closingSpan := span 12 13)
    ⟨⟨by change 3 < 6; decide, rfl⟩, rfl⟩ ⟨⟨by change 4 < 6; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 1 []) = .ok (sym 7 8 .leftParen) (s 2 []) at opening
  have guard : isSymbol (s 2 []) .rightParen = false := rfl
  have values : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) =
      .ok { span := span 7 13, elements := [ty] } (s 5 [event]) := by
    dsimp only [s] at opening guard ⊢
    simp only [delimited, delimitedWithPolicy, opening, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
    exact tail
  rw [reduced]
  change (match delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) with
    | .ok values output => Reply.ok (some values) output
    | .reject failure rejected => Reply.reject failure rejected
    | .invariant error => Reply.invariant error) = _
  rw [values]

private def failure : Failure := {
  span := span 12 13, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseFunctionReturns typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 3 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have markerResult := contextual_eq_ok_of_exactTokenParses .returns .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have child := checked_child rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have opening := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 1 []) = .ok (sym 7 8 .leftParen) (s 2 []) at opening
  have guard : isSymbol (s 2 []) .rightParen = false := rfl
  have noComma : isSymbol (s 3 [event]) .comma = false := rfl
  have noClose : isSymbol (s 3 [event]) .rightParen = false := rfl
  have report : rejectAt (α := DelimitedList TypeExpr) (s 3 [event])
      { head := .symbol .comma, tail := [.symbol .rightParen] } .typeExpr = .reject failure (s 3 [event]) := rfl
  apply parseFunctionReturns_reject_iff_list.mpr
  refine ⟨_, markerResult, ?_⟩
  change delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 1 []) = _
  dsimp only [s] at opening guard noComma noClose report ⊢
  simp only [delimited, delimitedWithPolicy, opening, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 7 8 .leftParen)
    (4 + 1) [ty] (s 3 [event]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, noComma, noClose, Bool.false_eq_true, if_false, report]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem canonical_lexing :
    Lexer.lex (file emptyText) = .ok (carrier emptyTokens) ∧
    Lexer.lex (file successText) = .ok (carrier successTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  repeat' constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_empty_returns (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parseFunctionReturns nested { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } =
        .ok (some { span := span 7 9, elements := [] }) output ∧
      output = state emptyText emptyTokens prior 3 [] ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 4, endByte := 14 } ∧ output.peek? = some (tailToken 10) := by
  refine ⟨_, _, canonical_lexing.1, empty_exec nested prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_reverse, List.reverse_nil, List.nil_append]

theorem canonical_singleton_trailing_returns (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseFunctionReturns typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok (some { span := span 7 13, elements := [ty] }) output ∧
      output = state successText successTokens prior 5 [event] ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 18 } ∧ output.peek? = some (tailToken 14) := by
  refine ⟨_, _, canonical_lexing.2.1, success_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_missing_separator (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseFunctionReturns typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 3 [event] ∧
      output.diagnostics = prior ++ [event] ∧ output.window = { endIndex := 6, endByte := 19 } ∧
      output.peek? = some (sym 12 13 .plus) ∧ output.tokens[5]? = some (tailToken 15) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalFunctionReturnsTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalFunctionTypeTraceExamples
/-! Real type children emit parameter events before return events. Canonical
success and return-list rejection retain every AST span, full state, and prior
event; neither case assumes general recursive diagnostic-trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalFunctionTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals
open Solcore.Test.SyntaxCheckedTypeListTraceSupport

private def source : SourceId := { origin := .main, path := "canonical-function-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 8, value := .keyword .functionKw }
private def returnsMarker : Token := { span := span 15 22, value := .identifier "returns" }
private def nameA : Identifier := { span := span 9 12, value := "a-b" }
private def nameC : Identifier := { span := span 23 26, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def ty (name : Identifier) : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def prefixTokens : List Token := [marker, sym 8 9 .leftParen, nameToken nameA,
  sym 12 13 .comma, sym 13 14 .rightParen, returnsMarker, sym 22 23 .leftParen, nameToken nameC]
private def successText : String := "function(a-b,) returns(c-d,) tail"
private def successTokens : List Token := prefixTokens ++ [sym 26 27 .comma, sym 27 28 .rightParen, tailToken 29]
private def rejectedText : String := "function(a-b,) returns(c-d +) tail"
private def rejectedTokens : List Token := prefixTokens ++ [sym 27 28 .plus, sym 28 29 .rightParen, tailToken 30]
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def parameters : DelimitedList TypeExpr := { span := span 8 14, elements := [ty nameA] }
private def returns : DelimitedList TypeExpr := { span := span 22 28, elements := [ty nameC] }
private def value : TypeExpr := {
  span := span 0 28, value := .function (span 0 8) parameters (some returns)
}

private theorem parameter_exec (content : String) (suffix : List Token) (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (state content (prefixTokens ++ suffix) prior 1 []) =
      .ok parameters (state content (prefixTokens ++ suffix) prior 5 [event nameA]) := by
  apply singleton_trailing_checked_type_list (name := nameA) (trace := [event nameA])
    (openingSpan := span 8 9) (commaSpan := span 12 13) (closingSpan := span 13 14)
  · exact ⟨by change 1 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 2 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 3 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact ⟨by change 4 < (prefixTokens ++ suffix).length; simp [prefixTokens], rfl⟩
  · exact .hyphen (by unfold IdentifierHyphenSpelling nameA; decide)
  · decide
  · decide

private theorem success_exec (prior : List ParseDiagnostic) :
    parseFunctionType typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 10 [event nameA, event nameC]) := by
  let s := state successText successTokens prior
  have keywordResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 11; decide, rfl⟩, rfl⟩
  have parameterResult := parameter_exec successText [sym 26 27 .comma, sym 27 28 .rightParen, tailToken 29] prior
  have listResult : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (s 6 [event nameA]) = .ok returns (s 10 [event nameA, event nameC]) := by
    apply singleton_trailing_checked_type_list (name := nameC) (trace := [event nameC])
      (openingSpan := span 22 23) (commaSpan := span 26 27) (closingSpan := span 27 28)
    · exact ⟨by change 6 < 11; decide, rfl⟩
    · exact ⟨by change 7 < 11; decide, rfl⟩
    · exact ⟨by change 8 < 11; decide, rfl⟩
    · exact ⟨by change 9 < 11; decide, rfl⟩
    · exact .hyphen (by unfold IdentifierHyphenSpelling nameC; decide)
    · decide
    · decide
  have reduced := parseFunctionReturns_eq_of_present typeExpr
    (input := s 5 [event nameA]) (after := (s 6 [event nameA]).declarativeRemainder) (span := span 15 22)
    ⟨⟨by change 5 < 11; decide, rfl⟩, rfl⟩
  have returnResult : parseFunctionReturns typeExpr (s 5 [event nameA]) =
      .ok (some returns) (s 10 [event nameA, event nameC]) := by
    rw [reduced]
    change (match delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 6 [event nameA]) with
      | .ok values output => Reply.ok (some values) output
      | .reject failure rejected => Reply.reject failure rejected
      | .invariant error => Reply.invariant error) = _
    rw [listResult]
  exact parseFunctionType_success_iff_components.mpr
    ⟨_, _, _, _, _, keywordResult, parameterResult, returnResult, rfl⟩

private def failure : Failure := {
  span := span 27 28, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseFunctionType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 8 [event nameA, event nameC]) := by
  let s := state rejectedText rejectedTokens prior
  have keywordResult := keyword_eq_ok_of_exactTokenParses .functionKw .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 11; decide, rfl⟩, rfl⟩
  have parameterResult := parameter_exec rejectedText [sym 27 28 .plus, sym 28 29 .rightParen, tailToken 30] prior
  have returnMarkerResult := contextual_eq_ok_of_exactTokenParses .returns .typeExpr
    (input := s 5 [event nameA]) (after := (s 6 [event nameA]).declarativeRemainder) (span := span 15 22)
    ⟨⟨by change 5 < 11; decide, rfl⟩, rfl⟩
  have listResult : delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr
      (s 6 [event nameA]) = .reject failure (s 8 [event nameA, event nameC]) := by
    apply checked_type_list_missing_separator (name := nameC) (trace := [event nameC])
    · exact ⟨by change 6 < 11; decide, rfl⟩
    · exact ⟨by change 7 < 11; decide, rfl⟩
    · exact ⟨by change 8 < 11; decide, rfl⟩
    · exact .hyphen (by unfold IdentifierHyphenSpelling nameC; decide)
    · decide
    · decide
  have returnsResult := parseFunctionReturns_reject_iff_list.mpr ⟨_, returnMarkerResult, listResult⟩
  exact parseFunctionType_reject_iff_components.mpr
    (.inr (.inr ⟨_, _, _, _, keywordResult, parameterResult, returnsResult⟩))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2400000 in
theorem canonical_lexing :
    Lexer.lex (file successText) = .ok (carrier successTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_parameter_then_return_events (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseFunctionType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 10 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 11, endByte := 33 } ∧ output.peek? = some (tailToken 29) := by
  refine ⟨_, _, canonical_lexing.1, success_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_return_failure_keeps_parameter_events (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseFunctionType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 8 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 11, endByte := 34 } ∧ output.peek? = some (sym 27 28 .plus) ∧
      output.tokens[10]? = some (tailToken 30) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalFunctionTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalMappingTypeTraceExamples
/-! Canonical mapping types execute real checked-name type children. Both
success and closing rejection retain key/value events in order, exact spans,
complete states, and the still-unconsumed following source. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalMappingTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

private def source : SourceId := { origin := .main, path := "canonical-mapping-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 7, value := .identifier "mapping" }
private def keyName : Identifier := { span := span 8 11, value := "a-b" }
private def valueName : Identifier := { span := span 15 18, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def ty (name : Identifier) : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def prefixTokens : List Token := [marker, sym 7 8 .leftParen, nameToken keyName,
  sym 12 14 .fatArrow, nameToken valueName]
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}

private theorem child_pair (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (keyToken : TokenAt tokens.toArray tokens.length 2 (nameToken keyName))
    (arrowToken : TokenAt tokens.toArray tokens.length 3 (sym 12 14 .fatArrow))
    (valueToken : TokenAt tokens.toArray tokens.length 4 (nameToken valueName))
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 5 (.symbol .dot))
    (noArguments : TokenKindAbsentAt tokens.toArray tokens.length 5 (.symbol .less)) :
    typeExpr (state content tokens prior 2 []) = .ok (ty keyName) (state content tokens prior 3 [event keyName]) ∧
    typeExpr (state content tokens prior 4 [event keyName]) =
      .ok (ty valueName) (state content tokens prior 5 [event keyName, event valueName]) := by
  have afterKeyAbsent (symbol : Symbol) (different : symbol ≠ .fatArrow) :
      TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol symbol) := by
    rintro ⟨otherSpan, other⟩
    have same := arrowToken.token_unique other
    cases same
    exact different rfl
  constructor
  · exact checked_name_type (input := state content tokens prior 2 []) keyToken
      (.hyphen (by unfold IdentifierHyphenSpelling keyName; decide))
      (afterKeyAbsent .dot (by decide)) (afterKeyAbsent .less (by decide)) (by decide) (by decide)
  · exact checked_name_type (input := state content tokens prior 4 [event keyName]) valueToken
      (.hyphen (by unfold IdentifierHyphenSpelling valueName; decide)) noDot noArguments (by decide) (by decide)

private def successText : String := "mapping(a-b => c-d) tail"
private def successTokens : List Token := prefixTokens ++ [sym 18 19 .rightParen,
  { span := span 20 24, value := .identifier "tail" }]
private def resultValue : TypeExpr := mappingTypeTraceValue (span 0 7) (span 7 8) (span 18 19)
  (ty keyName) (ty valueName)

private theorem success_exec (prior : List ParseDiagnostic) :
    parseMappingType typeExpr (state successText successTokens prior 0 []) =
      .ok resultValue (state successText successTokens prior 6 [event keyName, event valueName]) := by
  let s := state successText successTokens prior
  have children := child_pair successText successTokens prior
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, prefixTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, prefixTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7) ⟨⟨by change 0 < 7; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8) ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩
  have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr
    (input := s 3 [event keyName]) (after := (s 4 [event keyName]).declarativeRemainder)
    (span := span 12 14) ⟨⟨by change 3 < 7; decide, rfl⟩, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .typeExpr
    (input := s 5 [event keyName, event valueName]) (after := (s 6 [event keyName, event valueName]).declarativeRemainder)
    (span := span 18 19) ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩
  exact parseMappingType_success_iff_components.mpr
    ⟨marker, s 1 [], sym 7 8 .leftParen, s 2 [], ty keyName, s 3 [event keyName],
      sym 12 14 .fatArrow, s 4 [event keyName], ty valueName, s 5 [event keyName, event valueName],
      sym 18 19 .rightParen, markerResult, openingResult, children.1, arrowResult, children.2, closingResult, rfl⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem mapping_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_mapping_success (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseMappingType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok resultValue output ∧ output = state successText successTokens prior 6 [event keyName, event valueName] ∧
      output.diagnostics = prior ++ [event keyName, event valueName] ∧
      output.window = { endIndex := 7, endByte := 24 } ∧
      output.peek? = some { span := span 20 24, value := .identifier "tail" } := by
  refine ⟨carrier successTokens, _, mapping_lexes, success_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

private def rejectedText : String := "mapping(a-b => c-d +) tail"
private def rejectedTokens : List Token := prefixTokens ++ [sym 19 20 .plus, sym 20 21 .rightParen,
  { span := span 22 26, value := .identifier "tail" }]
private def failure : Failure := {
  span := span 19 20, found := some (.symbol .plus)
  expected := { head := .symbol .rightParen, tail := [] }, context := .typeExpr
}

private theorem rejection_exec (prior : List ParseDiagnostic) :
    parseMappingType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 5 [event keyName, event valueName]) := by
  let s := state rejectedText rejectedTokens prior
  have children := child_pair rejectedText rejectedTokens prior
    ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, prefixTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, prefixTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 7) ⟨⟨by change 0 < 8; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 7 8) ⟨⟨by change 1 < 8; decide, rfl⟩, rfl⟩
  have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr
    (input := s 3 [event keyName]) (after := (s 4 [event keyName]).declarativeRemainder)
    (span := span 12 14) ⟨⟨by change 3 < 8; decide, rfl⟩, rfl⟩
  have missing : TokenKindAbsentAt (s 5 [event keyName, event valueName]).tokens
      (s 5 [event keyName, event valueName]).window.endIndex 5 (.symbol .rightParen) := by
    simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, rejectedTokens, prefixTokens, sym]
  have reported : RejectAtReports (s 5 [event keyName, event valueName]).file.id
      (s 5 [event keyName, event valueName]).window.endByte { head := .symbol .rightParen, tail := [] }
      .typeExpr (s 5 [event keyName, event valueName]).declarativeRemainder failure.toDiagnostic :=
    .reported (.token (current := sym 19 20 .plus) ⟨by change 5 < 8; decide, rfl⟩)
  rcases (symbol_reject_reports_iff .rightParen .typeExpr).mp ⟨missing, reported⟩ with ⟨actual, closingResult, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  have keyResult := children.1
  have valueResult := children.2
  change contextual .mapping .typeExpr (s 0 []) = .ok marker (s 1 []) at markerResult
  change symbol .leftParen .typeExpr (s 1 []) = .ok (sym 7 8 .leftParen) (s 2 []) at openingResult
  change symbol .fatArrow .typeExpr (s 3 [event keyName]) =
    .ok (sym 12 14 .fatArrow) (s 4 [event keyName]) at arrowResult
  dsimp only [s] at markerResult openingResult arrowResult closingResult
  simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_mapping_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_mapping_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseMappingType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 5 [event keyName, event valueName] ∧
      output.diagnostics = prior ++ [event keyName, event valueName] ∧
      output.window = { endIndex := 8, endByte := 26 } ∧ output.peek? = some (sym 19 20 .plus) ∧
      output.tokens[7]? = some { span := span 22 26, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, _, rejected_mapping_lexes, rejection_exec prior, rfl, ?_, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalMappingTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalNamedTypeArgumentsTraceExamples
/-! Real typeExpr children in canonical optional argument lists. These concrete
executions do not assume or establish general recursive type trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalNamedTypeArgumentsTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

private def qualified : QualifiedName := {
  span := SourceSpan.cover nameA.span nameA.span
  value := { components := { head := nameA, tail := [] } }
}
private def named : TypeExpr := makeNamedType qualified none
private def checkedState (input : State) : State := {
  input with cursor := input.cursor + 1, diagnosticsRev := hyphen nameA :: input.diagnosticsRev
}

private theorem checked_type_exec (input : State)
    (found : input.peek? = some (nameToken nameA))
    (noDot : isSymbol (checkedState input) .dot = false)
    (noArgs : isSymbol (checkedState input) .less = false) :
    typeExpr input = .ok named (checkedState input) := by
  have checked : identifier .typeExpr input = .ok nameA (checkedState input) := by
    simp only [identifier, rawIdentifier, found]
    rfl
  have path : qualifiedName .typeExpr .typeExpr input = .ok qualified (checkedState input) := by
    simp only [qualifiedName, checked, QualifiedNameInternals.qualifiedNameTail, noDot,
      Bool.false_eq_true, if_false, QualifiedNameInternals.finishQualifiedName]
    rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) input =
      parseNamedType (typeExprWithFuel fuel) input := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  rw [typeExpr, selected]
  simp only [parseNamedType, bind, path, parseNamedTypeArguments, getState, noArgs,
    Bool.false_eq_true, if_false, pure]
  rfl

private def successText : String := "<a-b,> tail"
private def successTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .greater, { span := span 7 11, value := .identifier "tail" }]
private def arguments : NonemptyDelimitedList TypeExpr := {
  span := span 0 6, elements := { head := named, tail := [] }
}
private def successOutput (prior : List ParseDiagnostic) : State := {
  initial successText successTokens prior with cursor := 4, diagnosticsRev := hyphen nameA :: prior.reverse
}

private theorem success_exec (prior : List ParseDiagnostic) :
    parseNamedTypeArguments typeExpr (initial successText successTokens prior) =
      .ok (some arguments) (successOutput prior) := by
  let input := initial successText successTokens prior
  let afterOpening : State := { input with cursor := 1 }
  have marker : ExactTokenParses (.symbol .less) input.declarativeRemainder
      (span 0 1) afterOpening.declarativeRemainder := ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr input = .ok (sym 0 1 .less) afterOpening at markerResult
  have child := checked_type_exec afterOpening rfl rfl rfl
  have tail := SyntaxDelimitedTrailingSuccessTraceProperties.trailing_close_bypasses_any_child
    typeExpr (sym 0 1 .less) .greater .typeExpr .typeExpr afterOpening.remainingCount [named]
    (input := checkedState afterOpening) (afterComma := remainder successTokens 3)
    (after := remainder successTokens 4) (commaSpan := span 4 5) (closingSpan := span 5 6)
    ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩
  have raw : delimited .less .greater false typeExpr .typeExpr .typeExpr input =
      .ok { span := arguments.span, elements := arguments.elements.toList } (successOutput prior) := by
    unfold delimited delimitedWithPolicy
    rw [markerResult]
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    rw [child]
    have progress : (checkedState afterOpening).cursor > afterOpening.cursor := by change 2 > 1; decide
    simp only [progress, if_true]
    exact tail
  rw [parseNamedTypeArguments_eq_of_present typeExpr marker.1, raw]
  simp only [requireNonempty_eq_ok_of_toList]

set_option maxRecDepth 16384 in
theorem real_argument_list_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_real_type_argument (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseNamedTypeArguments typeExpr
        { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } = .ok (some arguments) output ∧
      output = successOutput prior ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 5, endByte := 11 } ∧
      output.peek? = some { span := span 7 11, value := .identifier "tail" } := by
  refine ⟨carrier successTokens, successOutput prior, real_argument_list_lexes, success_exec prior,
    rfl, ?_, rfl, rfl⟩
  simp only [successOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedText : String := "<a-b,+> tail"
private def rejectedTokens : List Token := [sym 0 1 .less, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .plus, sym 6 7 .greater, { span := span 8 12, value := .identifier "tail" }]
private def rejectedOutput (prior : List ParseDiagnostic) : State := {
  initial rejectedText rejectedTokens prior with cursor := 3, diagnosticsRev := hyphen nameA :: prior.reverse
}
private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem rejection_exec (prior : List ParseDiagnostic) :
    parseNamedTypeArguments typeExpr (initial rejectedText rejectedTokens prior) =
      .reject failure (rejectedOutput prior) := by
  let input := initial rejectedText rejectedTokens prior
  let afterOpening : State := { input with cursor := 1 }
  have marker : ExactTokenParses (.symbol .less) input.declarativeRemainder
      (span 0 1) afterOpening.declarativeRemainder := ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr input = .ok (sym 0 1 .less) afterOpening at markerResult
  have child := checked_type_exec afterOpening rfl rfl rfl
  have found : (rejectedOutput prior).peek? = some (sym 5 6 .plus) := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  have rejected : typeExpr (rejectedOutput prior) = .reject failure (rejectedOutput prior) := by
    rw [typeExpr, selected]
    rfl
  have comma : ExactTokenParses (.symbol .comma) (checkedState afterOpening).declarativeRemainder
      (span 4 5) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .typeExpr comma
  change symbol .comma .typeExpr (checkedState afterOpening) =
    .ok (sym 4 5 .comma) (rejectedOutput prior) at commaResult
  apply parseNamedTypeArguments_reject_iff_list.mpr
  refine ⟨rfl, ?_⟩
  change delimited .less .greater false typeExpr .typeExpr .typeExpr input =
    .reject failure (rejectedOutput prior)
  unfold delimited delimitedWithPolicy
  rw [markerResult]
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  rw [child]
  have progress : (checkedState afterOpening).cursor > afterOpening.cursor := by change 2 > 1; decide
  simp only [progress, if_true]
  change afterDelimitedElement typeExpr .greater true .typeExpr .typeExpr (sym 0 1 .less)
    (afterOpening.remainingCount + 1) [named] (checkedState afterOpening) = .reject failure (rejectedOutput prior)
  have commaPresent : isSymbol (checkedState afterOpening) .comma = true := rfl
  have noClosing : isSymbol (rejectedOutput prior) .greater = false := rfl
  simp only [afterDelimitedElement, commaPresent, if_true, commaResult, Bool.true_and,
    noClosing, Bool.false_eq_true, if_false, rejected]

set_option maxRecDepth 16384 in
theorem rejected_real_argument_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_real_type_argument_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseNamedTypeArguments typeExpr
        { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } = .reject failure output ∧
      output = rejectedOutput prior ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.window = { endIndex := 6, endByte := 12 } ∧ output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[5]? = some { span := span 8 12, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, rejectedOutput prior, rejected_real_argument_lexes, rejection_exec prior,
    rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalNamedTypeArgumentsTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalNamedTypeTraceExamples
/-! Bare mapping reports its complete type span only after optional arguments
succeed. A real type child failure inside selected arguments prevents that
finishing event altogether. Lexer decisions alone use kernel evaluation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalNamedTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxNamedTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-named-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def name : Identifier := { span := span 0 7, value := "mapping" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def qualified : QualifiedName := tracedQualifiedName name []
private def value : TypeExpr := namedTypeTraceValue qualified none
private def report : ParseDiagnostic := {
  span := value.span, kind := .constraintViolation .mappingRequiresCanonicalForm
}
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}

private theorem mapping_name_exec {input : State}
    (token : TokenAt input.tokens input.window.endIndex input.cursor nameToken)
    (noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot)) :
    qualifiedName .typeExpr .typeExpr input = .ok qualified { input with cursor := input.cursor + 1 } := by
  have head : IdentifierTraceParses input.declarativeRemainder name
      { input.declarativeRemainder with cursor := input.cursor + 1 } [] :=
    .parsed ⟨token, rfl, rfl, rfl⟩ (.clean (by unfold IdentifierHyphenSpelling name; decide))
  exact qualifiedName_eq_ok_of_trace .typeExpr .typeExpr (.parsed head (.done noDot))

private def bareText : String := "mapping tail"
private def bareTokens : List Token := [nameToken, { span := span 8 12, value := .identifier "tail" }]
private def bareOutput (prior : List ParseDiagnostic) : State := {
  initial bareText bareTokens prior with cursor := 1, diagnosticsRev := report :: prior.reverse
}

set_option maxRecDepth 16384 in
theorem bare_mapping_lexes : Lexer.lex (file bareText) = .ok (carrier bareTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

/-- No nested parser is invoked for the bare spelling. Its one constraint
event follows every incoming report, and every other state field is exact. -/
theorem canonical_bare_mapping (nested : Parser TypeExpr) (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file bareText) = .ok lexed ∧
      parseNamedType nested { State.initial (file bareText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = bareOutput prior ∧ output.diagnostics = prior ++ [report] ∧
      output.window = { endIndex := 2, endByte := 12 } ∧
      output.peek? = some { span := span 8 12, value := .identifier "tail" } := by
  let input := initial bareText bareTokens prior
  have nameResult := mapping_name_exec (input := input) ⟨by change 0 < 2; decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, bareTokens])
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex 1 (.symbol .less) := by
    simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, bareTokens]
  have finished : NamedTypeFinishingTrace qualified none [report] := .canonicalRequired ⟨rfl, rfl⟩
  have result := no_arguments_bypass_any_child nested nameResult noArgs finished
  refine ⟨carrier bareTokens, bareOutput prior, bare_mapping_lexes, result, rfl, ?_, rfl, rfl⟩
  simp only [bareOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedText : String := "mapping<+> tail"
private def rejectedTokens : List Token := [nameToken, { span := span 7 8, value := .symbol .less },
  { span := span 8 9, value := .symbol .plus }, { span := span 9 10, value := .symbol .greater },
  { span := span 11 15, value := .identifier "tail" }]
private def rejectedOutput (prior : List ParseDiagnostic) : State := {
  initial rejectedText rejectedTokens prior with cursor := 2
}
private def failure : Failure := {
  span := span 8 9, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseNamedType typeExpr (initial rejectedText rejectedTokens prior) = .reject failure (rejectedOutput prior) := by
  let input := initial rejectedText rejectedTokens prior
  let afterName : State := { input with cursor := 1 }
  have nameResult := mapping_name_exec (input := input) ⟨by change 0 < 5; decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, input, initial, State.initial, carrier, rejectedTokens])
  have marker : ExactTokenParses (.symbol .less) afterName.declarativeRemainder
      (span 7 8) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr marker
  change symbol .less .typeExpr afterName =
    .ok { span := span 7 8, value := .symbol .less } (rejectedOutput prior) at markerResult
  have found : (rejectedOutput prior).peek? = some { span := span 8 9, value := .symbol .plus } := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  have child : typeExpr (rejectedOutput prior) = .reject failure (rejectedOutput prior) := by
    rw [typeExpr, selected]
    rfl
  have raw : delimited .less .greater false typeExpr .typeExpr .typeExpr afterName =
      .reject failure (rejectedOutput prior) := by
    simp only [delimited, delimitedWithPolicy, markerResult, Bool.false_and, Bool.false_eq_true,
      if_false, child]
  exact argument_failure_bypasses_finishing typeExpr nameResult
    (parseNamedTypeArguments_reject_iff_list.mpr ⟨rfl, raw⟩)

set_option maxRecDepth 16384 in
theorem rejected_mapping_arguments_lex : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

/-- The type rejection is still uncommitted, and the mapping constraint is
not emitted before arguments finish. Thus the entire diagnostic list is prior. -/
theorem canonical_mapping_argument_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseNamedType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = rejectedOutput prior ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 5, endByte := 15 } ∧
      output.peek? = some { span := span 8 9, value := .symbol .plus } ∧
      output.tokens[4]? = some { span := span 11 15, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, rejectedOutput prior, rejected_mapping_arguments_lex, rejected_exec prior,
    rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, initial, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalNamedTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples
/-! Canonical checked-name parentheses distinguish a singleton trailing-comma
group from a two-element tuple. Independent token derivations execute through
trace completeness; only canonical lexing uses kernel decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

def source : SourceId := { origin := .main, path := "canonical-parenthesized-trace.sol" }
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

private theorem success_exec (text : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (value : Expr) (after : Remainder) (events : List ParseDiagnostic)
    (parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source
      (file text).content.utf8ByteSize (remainder tokens 0) value after events) :
    ∃ output, parenthesized identifierExpression (initial text tokens prior) = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ events ∧
      output.file = file text ∧ output.window = (initial text tokens prior).window := by
  rcases parenthesized_trace_success_complete identifierExpression_trace_success_complete
      identifierExpression_success_context (input := initial text tokens prior) parsed with
    ⟨output, result, afterEq, diagnostics⟩
  have frame := parenthesized_success_context identifierExpression_success_context result
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

def groupText : String := "(a-b,) tail"
def groupTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  sym 5 6 .rightParen, { span := span 7 11, value := .identifier "tail" }]
def groupValue : Expr := { span := span 0 6, value := .group (nameExpr nameA) }

private theorem group_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 11
    (remainder groupTokens 0) groupValue (remainder groupTokens 4) [hyphen nameA] :=
  .tuple (span 0 1) (span 5 6) (afterOpening := remainder groupTokens 1)
    (afterFirst := remainder groupTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupTokens, nameToken])
    (name_trace (input := remainder groupTokens 1) nameA 11 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.trailing (span 4 5) (span 5 6) (afterComma := remainder groupTokens 3)
      ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩)

def tupleText : String := "(a-b,c-d) tail"
def tupleTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  nameToken nameC, sym 8 9 .rightParen, { span := span 10 14, value := .identifier "tail" }]
def tupleValue : Expr := {
  span := span 0 9, value := .tuple { span := span 0 9, elements := [nameExpr nameA, nameExpr nameC] }
}

private theorem tuple_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 14
    (remainder tupleTokens 0) tupleValue (remainder tupleTokens 5) [hyphen nameA, hyphen nameC] :=
  .tuple (span 0 1) (span 8 9) (afterOpening := remainder tupleTokens 1)
    (afterFirst := remainder tupleTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, nameToken])
    (name_trace (input := remainder tupleTokens 1) nameA 14 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (.final (span 4 5) (span 8 9) (afterComma := remainder tupleTokens 3)
      (afterElement := remainder tupleTokens 4) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, nameToken])
      (name_trace (input := remainder tupleTokens 3) nameC 14 ⟨by decide, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩)

def emptyText : String := "() tail"
def emptyTokens : List Token := [sym 0 1 .leftParen, sym 1 2 .rightParen,
  { span := span 3 7, value := .identifier "tail" }]
def emptyValue : Expr := { span := span 0 2, value := .tuple { span := span 0 2, elements := [] } }

private theorem empty_parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses source 7
    (remainder emptyTokens 0) emptyValue (remainder emptyTokens 2) [] :=
  .empty (span 0 1) (span 1 2) (afterOpening := remainder emptyTokens 1)
    ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩

theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 16384 in
theorem group_lexes : Lexer.lex (file groupText) = .ok (carrier groupTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem tuple_lexes : Lexer.lex (file tupleText) = .ok (carrier tupleTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem empty_lexes : Lexer.lex (file emptyText) = .ok (carrier emptyTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- A written trailing comma does not turn one element into a tuple: the
actual parser returns the complete group AST and exactly one name event. -/
theorem canonical_singleton_trailing_is_group (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file groupText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file groupText) lexed with diagnosticsRev := prior.reverse } = .ok groupValue output ∧
      output.declarativeRemainder = remainder groupTokens 4 ∧ output.diagnostics = prior ++ [hyphen nameA] ∧
      output.file = file groupText ∧ output.window = { endIndex := 5, endByte := 11 } ∧
      output.peek? = some { span := span 7 11, value := .identifier "tail" } := by
  rcases success_exec groupText groupTokens prior _ _ _ group_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier groupTokens, output, group_lexes, result, after, events, fileEq, window,
    peek_of_remainder after ⟨by decide, rfl⟩⟩

/-- Two written elements produce a tuple in source order, keeping the outer
and list spans, both checked-name events, the whole parent window, and `tail`. -/
theorem canonical_two_elements_is_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file tupleText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file tupleText) lexed with diagnosticsRev := prior.reverse } = .ok tupleValue output ∧
      output.declarativeRemainder = remainder tupleTokens 5 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.file = file tupleText ∧ output.window = { endIndex := 6, endByte := 14 } ∧
      output.peek? = some { span := span 10 14, value := .identifier "tail" } := by
  rcases success_exec tupleText tupleTokens prior _ _ _ tuple_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier tupleTokens, output, tuple_lexes, result, after, events, fileEq, window,
    peek_of_remainder after ⟨by decide, rfl⟩⟩

theorem canonical_empty_is_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } = .ok emptyValue output ∧
      output.declarativeRemainder = remainder emptyTokens 2 ∧ output.diagnostics = prior ∧
      output.file = file emptyText ∧ output.window = { endIndex := 3, endByte := 7 } ∧
      output.peek? = some { span := span 3 7, value := .identifier "tail" } := by
  rcases success_exec emptyText emptyTokens prior _ _ _ empty_parsed with
    ⟨output, result, after, events, fileEq, window⟩
  exact ⟨carrier emptyTokens, output, empty_lexes, result, after, by simpa only [List.append_nil] using events,
    fileEq, window, peek_of_remainder after ⟨by decide, rfl⟩⟩

end Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalParenthesizedRejectionTraceExamples
/-! Canonical closing failures after successful checked-name children. The
bespoke parenthesized parser expects only right parenthesis at these points,
not the generic delimiter pair. Earlier events survive; the report is uncommitted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalParenthesizedRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Test.SyntaxCanonicalParenthesizedTraceExamples

def closingFailure (first last : Nat) : Failure := {
  span := span first last, found := some (.symbol .plus)
  expected := { head := .symbol .rightParen, tail := [] }, context := .expression
}

def groupRejectionText : String := "(a-b +) tail"
def groupRejectionTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .rightParen, { span := span 8 12, value := .identifier "tail" }]

private theorem group_rejected :
    ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder groupRejectionTokens 0) (remainder groupRejectionTokens 2)
      (closingFailure 5 6).toDiagnostic [hyphen nameA] :=
  .closingMissing (span 0 1) (afterOpening := remainder groupRejectionTokens 1)
    (afterElement := remainder groupRejectionTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, nameToken])
    (name_trace (input := remainder groupRejectionTokens 1) nameA 12 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, remainder, groupRejectionTokens, sym])
    (.reported (.token (current := sym 5 6 .plus) ⟨by decide, rfl⟩))

def tupleRejectionText : String := "(a-b,c-d +) tail"
def tupleRejectionTokens : List Token := [sym 0 1 .leftParen, nameToken nameA, sym 4 5 .comma,
  nameToken nameC, sym 9 10 .plus, sym 10 11 .rightParen,
  { span := span 12 16, value := .identifier "tail" }]

private theorem tuple_rejected :
    ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16
      (remainder tupleRejectionTokens 0) (remainder tupleRejectionTokens 4)
      (closingFailure 9 10).toDiagnostic [hyphen nameA, hyphen nameC] := by
  have tail : ParenthesizedTupleTailTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source 16 (remainder tupleRejectionTokens 2) (remainder tupleRejectionTokens 4)
      (closingFailure 9 10).toDiagnostic [hyphen nameC] :=
    .closingMissing (span 4 5) (afterComma := remainder tupleRejectionTokens 3)
      (afterElement := remainder tupleRejectionTokens 4) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, nameToken])
      (name_trace (input := remainder tupleRejectionTokens 3) nameC 16 ⟨by decide, rfl⟩
        (by unfold IdentifierHyphenSpelling nameC; decide)) (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, sym])
      (.reported (.token (current := sym 9 10 .plus) ⟨by decide, rfl⟩))
  exact .tailRejected (span 0 1) (span 4 5) (afterOpening := remainder tupleRejectionTokens 1)
    (afterFirst := remainder tupleRejectionTokens 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, remainder, tupleRejectionTokens, nameToken])
    (name_trace (input := remainder tupleRejectionTokens 1) nameA 16 ⟨by decide, rfl⟩
      (by unfold IdentifierHyphenSpelling nameA; decide)) (by decide) ⟨by decide, rfl⟩ tail

private theorem rejection_exec (text : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (failure : Failure) (after : Remainder) (events : List ParseDiagnostic)
    (rejected : ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source (file text).content.utf8ByteSize (remainder tokens 0) after failure.toDiagnostic events) :
    ∃ output, parenthesized identifierExpression (initial text tokens prior) = .reject failure output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ events ∧
      output.tokens = tokens.toArray ∧ output.window = (initial text tokens prior).window := by
  rcases (parenthesized_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      (input := initial text tokens prior)).mp rejected with ⟨output, result, afterEq, diagnostics⟩
  have frame := parenthesized_preservesTokenWindow identifierExpression
    identifierExpression_preservesTokenWindow (initial text tokens prior)
  rw [result] at frame
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using diagnostics

set_option maxRecDepth 16384 in
theorem group_rejection_lexes : Lexer.lex (file groupRejectionText) = .ok (carrier groupRejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel
set_option maxRecDepth 16384 in
theorem tuple_rejection_lexes : Lexer.lex (file tupleRejectionText) = .ok (carrier tupleRejectionTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

/-- After the first successful child, only right parenthesis is expected.
Exactly one checked-name event follows every prior event; the plus remains current. -/
theorem canonical_group_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file groupRejectionText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file groupRejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject (closingFailure 5 6) output ∧
      output.declarativeRemainder = remainder groupRejectionTokens 2 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.window = { endIndex := 5, endByte := 12 } ∧
      output.peek? = some (sym 5 6 .plus) ∧
      output.tokens[4]? = some { span := span 8 12, value := .identifier "tail" } := by
  rcases rejection_exec groupRejectionText groupRejectionTokens prior _ _ _ group_rejected with
    ⟨output, result, after, events, tokens, window⟩
  refine ⟨carrier groupRejectionTokens, output, group_rejection_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokens]
  rfl

/-- After a successful second child, the closing path still expects only
right parenthesis. Two ordered name events survive and the failure is not committed. -/
theorem canonical_tuple_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file tupleRejectionText) = .ok lexed ∧
      parenthesized identifierExpression
        { State.initial (file tupleRejectionText) lexed with diagnosticsRev := prior.reverse } =
        .reject (closingFailure 9 10) output ∧
      output.declarativeRemainder = remainder tupleRejectionTokens 4 ∧
      output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] ∧
      output.window = { endIndex := 7, endByte := 16 } ∧ output.peek? = some (sym 9 10 .plus) ∧
      output.tokens[6]? = some { span := span 12 16, value := .identifier "tail" } := by
  rcases rejection_exec tupleRejectionText tupleRejectionTokens prior _ _ _ tuple_rejected with
    ⟨output, result, after, events, tokens, window⟩
  refine ⟨carrier tupleRejectionTokens, output, tuple_rejection_lexes, result, after, events, window,
    peek_of_remainder after ⟨by decide, rfl⟩, ?_⟩
  rw [tokens]
  rfl

end Solcore.Test.SyntaxCanonicalParenthesizedRejectionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalProxyExpressionTraceExamples
/-! A concrete checked-name type supplies a real proxy consumer without
assuming general type trace contracts. Parser components are reduced only after
their exact token/branch evidence; canonical lexing alone uses kernel decision. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalProxyExpressionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "canonical-proxy-trace.sol" }
private def file : SourceFile := { id := source, content := "@a-b tail" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def diagnostic : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def qualified : QualifiedName := {
  span := SourceSpan.cover name.span name.span
  value := { components := { head := name, tail := [] } }
}
private def type : TypeExpr := makeNamedType qualified none
private def value : Expr := { span := span 0 4, value := .proxy (span 0 1) type }
private def lexed : LexedFile := {
  source, comments := [], diagnostics := []
  tokens := [{ span := span 0 1, value := .symbol .at },
    { span := name.span, value := .identifier name.value },
    { span := span 5 9, value := .identifier "tail" }]
}
private def input (prior : List ParseDiagnostic) : State := {
  State.initial file lexed with diagnosticsRev := prior.reverse
}
private def afterMarker (prior : List ParseDiagnostic) : State := { input prior with cursor := 1 }
private def output (prior : List ParseDiagnostic) : State := {
  input prior with cursor := 2, diagnosticsRev := diagnostic :: prior.reverse
}

private theorem type_exec (prior : List ParseDiagnostic) :
    typeExpr (afterMarker prior) = .ok type (output prior) := by
  have found : (afterMarker prior).peek? = some { span := name.span, value := .identifier name.value } := rfl
  have checked : identifier .typeExpr (afterMarker prior) = .ok name (output prior) := by
    simp only [identifier, rawIdentifier, found]
    rfl
  have noDot : isSymbol (output prior) .dot = false := rfl
  have noArgs : isSymbol (output prior) .less = false := rfl
  have path : qualifiedName .typeExpr .typeExpr (afterMarker prior) = .ok qualified (output prior) := by
    simp only [qualifiedName, checked, QualifiedNameInternals.qualifiedNameTail, noDot,
      Bool.false_eq_true, if_false, QualifiedNameInternals.finishQualifiedName]
    rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (afterMarker prior) =
      parseNamedType (typeExprWithFuel fuel) (afterMarker prior) := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  rw [typeExpr, selected]
  simp only [parseNamedType, bind, path, parseNamedTypeArguments, getState, noArgs,
    Bool.false_eq_true, if_false, pure]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem checked_name_proxy_lexes : Lexer.lex file = .ok lexed := by
  have checked : (Lexer.lex file).toOption = some lexed := by decide +kernel
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

theorem canonical_checked_type_proxy (prior : List ParseDiagnostic) :
    ∃ tokens next, Lexer.lex file = .ok tokens ∧
      proxyExpression { State.initial file tokens with diagnosticsRev := prior.reverse } = .ok value next ∧
      next.file = file ∧ next.tokens = lexed.tokens.toArray ∧
      next.window = { endIndex := 3, endByte := 9 } ∧ next.cursor = 2 ∧
      next.diagnostics = prior ++ [diagnostic] ∧
      next.peek? = some { span := span 5 9, value := .identifier "tail" } := by
  have marker : ExactTokenParses (.symbol .at) (input prior).declarativeRemainder
      (span 0 1) (afterMarker prior).declarativeRemainder := ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
  have executed : proxyExpression (input prior) = .ok value (output prior) :=
    proxyExpression_success_iff_components.mpr
      ⟨_, afterMarker prior, type, markerResult, type_exec prior, rfl⟩
  refine ⟨lexed, output prior, checked_name_proxy_lexes, executed, rfl, rfl, rfl, rfl, ?_, rfl⟩
  simp only [output, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedFile : SourceFile := { id := source, content := "@+ tail" }
private def rejectedLexed : LexedFile := {
  source, comments := [], diagnostics := []
  tokens := [{ span := span 0 1, value := .symbol .at },
    { span := span 1 2, value := .symbol .plus },
    { span := span 3 7, value := .identifier "tail" }]
}
private def rejectedInput (prior : List ParseDiagnostic) : State := {
  State.initial rejectedFile rejectedLexed with diagnosticsRev := prior.reverse
}
private def rejectedOutput (prior : List ParseDiagnostic) : State := { rejectedInput prior with cursor := 1 }
private def typeFailure : Failure := {
  span := span 1 2, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem type_rejection_exec (prior : List ParseDiagnostic) :
    typeExpr (rejectedOutput prior) = .reject typeFailure (rejectedOutput prior) := by
  have found : (rejectedOutput prior).peek? = some { span := span 1 2, value := .symbol .plus } := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier,
      State.peekKind?, found, Option.map_some]
    rfl
  rw [typeExpr, selected]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_proxy_lexes : Lexer.lex rejectedFile = .ok rejectedLexed := by
  have checked : (Lexer.lex rejectedFile).toOption = some rejectedLexed := by decide +kernel
  cases result : Lexer.lex rejectedFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

/-- The type child, not the proxy marker, reports failure. No report is
committed: every prior event, the current plus, and the following tail survive. -/
theorem canonical_type_rejected_proxy (prior : List ParseDiagnostic) :
    ∃ tokens next, Lexer.lex rejectedFile = .ok tokens ∧
      proxyExpression { State.initial rejectedFile tokens with diagnosticsRev := prior.reverse } =
        .reject typeFailure next ∧
      next = { rejectedInput prior with cursor := 1 } ∧ next.diagnostics = prior ∧
      next.window = { endIndex := 3, endByte := 7 } ∧
      next.peek? = some { span := span 1 2, value := .symbol .plus } ∧
      next.tokens[2]? = some { span := span 3 7, value := .identifier "tail" } := by
  have marker : ExactTokenParses (.symbol .at) (rejectedInput prior).declarativeRemainder
      (span 0 1) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have markerResult := symbol_eq_ok_of_exactTokenParses .at .expression marker
  change symbol .at .expression (rejectedInput prior) =
    .ok { span := span 0 1, value := .symbol .at } (rejectedOutput prior) at markerResult
  have executed : proxyExpression (rejectedInput prior) = .reject typeFailure (rejectedOutput prior) := by
    simp only [proxyExpression, bind, markerResult, type_rejection_exec]
  refine ⟨rejectedLexed, rejectedOutput prior, rejected_proxy_lexes, executed, rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, rejectedInput, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalProxyExpressionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalProxyTypeTraceExamples
/-! Canonical proxy types use the actual recursive type child, not expression
proxy syntax. Concrete component execution preserves complete states and does
not assume a general recursive type trace contract. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalProxyTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

private def source : SourceId := { origin := .main, path := "canonical-proxy-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def inner : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def value : TypeExpr := { span := span 0 4, value := .proxy (span 0 1) inner }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}
private def successText : String := "@a-b tail"
private def successTokens : List Token := [{ span := span 0 1, value := .symbol .at },
  { span := name.span, value := .identifier name.value }, { span := span 5 9, value := .identifier "tail" }]
private def successOutput (prior : List ParseDiagnostic) : State := {
  initial successText successTokens prior with cursor := 2, diagnosticsRev := event :: prior.reverse
}

set_option maxRecDepth 16384 in
theorem proxy_type_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_proxy_type (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseProxyType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = successOutput prior ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 3, endByte := 9 } ∧
      output.peek? = some { span := span 5 9, value := .identifier "tail" } := by
  let input := initial successText successTokens prior
  let afterMarker : State := { input with cursor := 1 }
  have marker : ExactTokenParses (.symbol .at) input.declarativeRemainder (span 0 1) afterMarker.declarativeRemainder :=
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have typed := checked_name_type (input := afterMarker) (name := name) (trace := [event])
    ⟨by change 1 < 3; decide, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
    (by simp [TokenKindAbsentAt, TokenAt, afterMarker, input, initial, State.initial, carrier, successTokens])
    (by simp [TokenKindAbsentAt, TokenAt, afterMarker, input, initial, State.initial, carrier, successTokens])
    (by decide) (by decide)
  have result := parseProxyType_success_iff_components.mpr
    ⟨_, afterMarker, inner, symbol_eq_ok_of_exactTokenParses .at .typeExpr marker, typed, rfl⟩
  refine ⟨carrier successTokens, successOutput prior, proxy_type_lexes, result, rfl, ?_, rfl, rfl⟩
  simp only [successOutput, State.diagnostics, List.reverse_cons, List.reverse_reverse]

private def rejectedText : String := "@+ tail"
private def rejectedTokens : List Token := [{ span := span 0 1, value := .symbol .at },
  { span := span 1 2, value := .symbol .plus }, { span := span 3 7, value := .identifier "tail" }]
private def rejectedOutput (prior : List ParseDiagnostic) : State := {
  initial rejectedText rejectedTokens prior with cursor := 1
}
private def failure : Failure := {
  span := span 1 2, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

set_option maxRecDepth 16384 in
theorem rejected_proxy_type_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_proxy_type_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseProxyType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = rejectedOutput prior ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 3, endByte := 7 } ∧
      output.peek? = some { span := span 1 2, value := .symbol .plus } ∧
      output.tokens[2]? = some { span := span 3 7, value := .identifier "tail" } := by
  let input := initial rejectedText rejectedTokens prior
  have marker : ExactTokenParses (.symbol .at) input.declarativeRemainder
      (span 0 1) (rejectedOutput prior).declarativeRemainder := ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have found : (rejectedOutput prior).peek? = some { span := span 1 2, value := .symbol .plus } := rfl
  have selected (fuel : Nat) : typeExprWithFuel (fuel + 1) (rejectedOutput prior) =
      rejectAt (rejectedOutput prior) { head := .typeExpr, tail := [] } .typeExpr := by
    simp only [typeExprWithFuel, isKeyword, isContextual, isSymbol, isIdentifier, State.peekKind?, found, Option.map_some]
    rfl
  have child : typeExpr (rejectedOutput prior) = .reject failure (rejectedOutput prior) := by
    rw [typeExpr, selected]
    rfl
  have result := parseProxyType_reject_iff_components.mpr (.inr
    ⟨_, rejectedOutput prior, symbol_eq_ok_of_exactTokenParses .at .typeExpr marker, child⟩)
  refine ⟨carrier rejectedTokens, rejectedOutput prior, rejected_proxy_type_lexes, result, rfl, ?_, rfl, rfl, rfl⟩
  simp only [rejectedOutput, initial, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalProxyTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalQualifiedNameRejectionTraceExamples
/-! A canonical rejected maximal dotted name retains both preceding checked
components. The selected final dot is consumed, the plus stays current, and the
identifier report is still uncommitted in every parse context and phase. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalQualifiedNameRejectionTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "qualified-name-rejection-trace.sol" }
private def file : SourceFile := { id := source, content := "a-b.c-d.+ tail" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 0 3, value := "a-b" }
private def nameC : Identifier := { span := span 4 7, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tokens : List Token := [nameToken nameA, { span := span 3 4, value := .symbol .dot },
  nameToken nameC, { span := span 7 8, value := .symbol .dot },
  { span := span 8 9, value := .symbol .plus }, { span := span 10 14, value := .identifier "tail" }]
private def lexed : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def remaining (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def failure (context : ParseContext) : Failure := {
  span := span 8 9, found := some (.symbol .plus), expected := { head := .identifier, tail := [] }, context
}
private def events : List ParseDiagnostic := [hyphen nameA, hyphen nameC]

private theorem rejected_trace (context : ParseContext) :
    QualifiedNameTraceRejects context source 14 (remaining 0) (remaining 4) (failure context).toDiagnostic events := by
  have last : DottedIdentifierTailTraceRejects context source 14 (remaining 3) (remaining 4)
      (failure context).toDiagnostic [] :=
    .componentRejected (span 7 8) ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [IdentifierAbsentAt, TokenAt, remaining, tokens])
      (.reported (.token (current := { span := span 8 9, value := .symbol .plus }) ⟨by decide, rfl⟩))
  have rest : DottedIdentifierTailTraceRejects context source 14 (remaining 1) (remaining 4)
      (failure context).toDiagnostic [hyphen nameC] :=
    .laterRejected (span 3 4) (afterDot := remaining 2) (afterComponent := remaining 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))) last
  have head : IdentifierTraceParses (remaining 0) nameA (remaining 1) [hyphen nameA] :=
    .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
  exact .tailRejected head rest

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_names_lex : Lexer.lex file = .ok lexed := by
  have checked : (Lexer.lex file).toOption = some lexed := by decide +kernel
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

theorem canonical_names_rejected (context : ParseContext) (phase : ParserPhase)
    (prior : List ParseDiagnostic) :
    ∃ actualLexed output, Lexer.lex file = .ok actualLexed ∧
      qualifiedName context phase { State.initial file actualLexed with diagnosticsRev := prior.reverse } =
        .reject (failure context) output ∧ output.declarativeRemainder = remaining 4 ∧
      output.diagnostics = prior ++ events ∧ output.file = file ∧
      output.window = { endIndex := 6, endByte := 14 } ∧
      output.peek? = some { span := span 8 9, value := .symbol .plus } ∧
      output.tokens[5]? = some { span := span 10 14, value := .identifier "tail" } := by
  let input : State := { State.initial file lexed with diagnosticsRev := prior.reverse }
  have rejection : QualifiedNameTraceRejects context input.file.id input.window.endByte input.declarativeRemainder
      (remaining 4) (failure context).toDiagnostic events := rejected_trace context
  have result := qualifiedName_eq_reject_of_trace context phase rejection
  refine ⟨lexed, _, rejected_names_lex, result, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [State.diagnostics, input, List.reverse_append, List.reverse_reverse]

/-- Initial rejection consumes nothing, even with a malformed carrier or
window. Context-specific expected/found/span data and every prior event remain. -/
theorem first_rejection_preserves_every_state_field (context : ParseContext) (phase : ParserPhase)
    {input : State} {failure : Failure} (absent : IdentifierAbsentAt input.declarativeRemainder)
    (reported : RejectAtReports input.file.id input.window.endByte { head := .identifier, tail := [] }
      context input.declarativeRemainder failure.toDiagnostic) :
    qualifiedName context phase input = .reject failure input :=
  qualifiedName_eq_reject_of_trace context phase (.firstRejected absent reported)

theorem preceding_name_events_survive_filtering (context : ParseContext)
    (normalizationFile : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ events) =
      filterParseDiagnostics normalizationFile lexical prior ++ events := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics normalizationFile lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical ((rejected_trace context).cascadeFilters _ _))

end Solcore.Test.SyntaxCanonicalQualifiedNameRejectionTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalTupleTypeTraceExamples
/-! Canonical tuple types use real typeExpr children. Empty, singleton-trailing,
and two-element lists stay tuples, and a missing separator preserves earlier
checked-name events without committing the ordered comma/right-paren report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalTupleTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties
open Solcore.Syntax.Parser.DelimitedTraceInternals

private def source : SourceId := { origin := .main, path := "canonical-tuple-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def ty (name : Identifier) : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tailToken (first : Nat) : Token := { span := span first (first + 4), value := .identifier "tail" }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}

private def emptyText : String := "() tail"
private def emptyTokens : List Token := [sym 0 1 .leftParen, sym 1 2 .rightParen, tailToken 3]
private def singleText : String := "(a-b,) tail"
private def singleTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 4 5 .comma, sym 5 6 .rightParen, tailToken 7]
private def pairText : String := "(a-b,c-d,) tail"
private def pairTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 4 5 .comma, nameToken nameC, sym 8 9 .comma, sym 9 10 .rightParen, tailToken 11]
private def rejectedText : String := "(a-b +) tail"
private def rejectedTokens : List Token := [sym 0 1 .leftParen, nameToken nameA,
  sym 5 6 .plus, sym 6 7 .rightParen, tailToken 8]

private theorem first_child (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 1 (nameToken nameA))
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .dot))
    (noArgs : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .less)) :
    typeExpr (state content tokens prior 1 []) =
      .ok (ty nameA) (state content tokens prior 2 [event nameA]) :=
  checked_name_type token (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
    noDot noArgs (by decide) (by decide)

private theorem empty_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state emptyText emptyTokens prior 0 []) =
      .ok { span := span 0 2, value := .tuple [] } (state emptyText emptyTokens prior 2 []) := by
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 2, elements := [] }, ?_, rfl⟩
  exact empty_list_bypasses_any_child typeExpr .leftParen .rightParen .typeExpr .typeExpr
    (afterOpening := (state emptyText emptyTokens prior 1 []).declarativeRemainder)
    (after := (state emptyText emptyTokens prior 2 []).declarativeRemainder)
    (openingSpan := span 0 1) (closingSpan := span 1 2)
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩ ⟨⟨by change 1 < 3; decide, rfl⟩, rfl⟩

private theorem single_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state singleText singleTokens prior 0 []) =
      .ok { span := span 0 6, value := .tuple [ty nameA] }
        (state singleText singleTokens prior 4 [event nameA]) := by
  let s := state singleText singleTokens prior
  have child := first_child singleText singleTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, singleTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, singleTokens, sym])
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 0 1 .leftParen) .rightParen
    .typeExpr .typeExpr 4 [ty nameA] (input := s 2 [event nameA])
    (afterComma := (s 3 [event nameA]).declarativeRemainder)
    (after := (s 4 [event nameA]).declarativeRemainder) (commaSpan := span 4 5) (closingSpan := span 5 6)
    ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ ⟨⟨by change 3 < 5; decide, rfl⟩, rfl⟩
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 6, elements := [ty nameA] }, ?_, rfl⟩
  change delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr (s 0 []) = _
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  have guard : isSymbol (s 1 []) .rightParen = false := rfl
  dsimp only [s] at marker guard
  dsimp only [s]
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, guard, Bool.false_eq_true,
    if_false, child]
  exact tail

private theorem pair_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state pairText pairTokens prior 0 []) =
      .ok { span := span 0 10, value := .tuple [ty nameA, ty nameC] }
        (state pairText pairTokens prior 6 [event nameA, event nameC]) := by
  let s := state pairText pairTokens prior
  have first := first_child pairText pairTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, pairTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, pairTokens, sym])
  have second : typeExpr (s 3 [event nameA]) = .ok (ty nameC) (s 4 [event nameA, event nameC]) :=
    checked_name_type (name := nameC) ⟨by change 3 < 7; decide, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))
      (by simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, pairTokens, sym])
      (by simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, pairTokens, sym])
      (by decide) (by decide)
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 7; decide, rfl⟩, rfl⟩
  have comma := symbol_eq_ok_of_exactTokenParses .comma .typeExpr
    (input := s 2 [event nameA]) (after := (s 3 [event nameA]).declarativeRemainder) (span := span 4 5)
    ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩
  have tail := trailing_close_bypasses_any_child typeExpr (sym 0 1 .leftParen) .rightParen
    .typeExpr .typeExpr 5 [ty nameC, ty nameA] (input := s 4 [event nameA, event nameC])
    (afterComma := (s 5 [event nameA, event nameC]).declarativeRemainder)
    (after := (s 6 [event nameA, event nameC]).declarativeRemainder)
    (commaSpan := span 8 9) (closingSpan := span 9 10)
    ⟨⟨by change 4 < 7; decide, rfl⟩, rfl⟩ ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  change symbol .comma .typeExpr (s 2 [event nameA]) = .ok (sym 4 5 .comma) (s 3 [event nameA]) at comma
  have noCloseFirst : isSymbol (s 1 []) .rightParen = false := rfl
  have hasComma : isSymbol (s 2 [event nameA]) .comma = true := rfl
  have noCloseSecond : isSymbol (s 3 [event nameA]) .rightParen = false := rfl
  dsimp only [s] at marker comma second noCloseFirst hasComma noCloseSecond
  apply parseTupleType_success_iff_list.mpr
  refine ⟨{ span := span 0 10, elements := [ty nameA, ty nameC] }, ?_, rfl⟩
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noCloseFirst,
    Bool.false_eq_true, if_false, first]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 0 1 .leftParen)
    (6 + 1) [ty nameA] (s 2 [event nameA]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, hasComma, if_true, comma, Bool.true_and,
    noCloseSecond, Bool.false_eq_true, if_false, second]
  exact tail

private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .typeExpr
}

private theorem rejected_exec (prior : List ParseDiagnostic) :
    parseTupleType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 2 [event nameA]) := by
  let s := state rejectedText rejectedTokens prior
  have child := first_child rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  change symbol .leftParen .typeExpr (s 0 []) = .ok (sym 0 1 .leftParen) (s 1 []) at marker
  have guard : isSymbol (s 1 []) .rightParen = false := rfl
  have noComma : isSymbol (s 2 [event nameA]) .comma = false := rfl
  have noClose : isSymbol (s 2 [event nameA]) .rightParen = false := rfl
  have report : rejectAt (α := DelimitedList TypeExpr) (s 2 [event nameA])
      { head := .symbol .comma, tail := [.symbol .rightParen] }
      .typeExpr = .reject failure (s 2 [event nameA]) := rfl
  dsimp only [s] at marker guard noComma noClose report
  apply parseTupleType_reject_iff_list.mpr
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, guard, Bool.false_eq_true, if_false, child]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr (sym 0 1 .leftParen)
    (4 + 1) [ty nameA] (s 2 [event nameA]) = _
  dsimp only [s]
  simp only [afterDelimitedElement, noComma, noClose, Bool.false_eq_true, if_false, report]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem canonical_lexing :
    Lexer.lex (file emptyText) = .ok (carrier emptyTokens) ∧
    Lexer.lex (file singleText) = .ok (carrier singleTokens) ∧
    Lexer.lex (file pairText) = .ok (carrier pairTokens) ∧
    Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  repeat' constructor
  all_goals apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  all_goals decide +kernel

theorem canonical_empty_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file emptyText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file emptyText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 2, value := .tuple [] } output ∧
      output = state emptyText emptyTokens prior 2 [] ∧ output.diagnostics = prior ∧
      output.window = { endIndex := 3, endByte := 7 } ∧ output.peek? = some (tailToken 3) := by
  refine ⟨_, _, canonical_lexing.1, empty_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_reverse, List.reverse_nil, List.nil_append]

theorem canonical_singleton_trailing_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file singleText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file singleText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 6, value := .tuple [ty nameA] } output ∧
      output = state singleText singleTokens prior 4 [event nameA] ∧ output.diagnostics = prior ++ [event nameA] ∧
      output.window = { endIndex := 5, endByte := 11 } ∧ output.peek? = some (tailToken 7) := by
  refine ⟨_, _, canonical_lexing.2.1, single_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_two_element_tuple (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file pairText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file pairText) lexed with diagnosticsRev := prior.reverse } =
        .ok { span := span 0 10, value := .tuple [ty nameA, ty nameC] } output ∧
      output = state pairText pairTokens prior 6 [event nameA, event nameC] ∧
      output.diagnostics = prior ++ [event nameA, event nameC] ∧
      output.window = { endIndex := 7, endByte := 15 } ∧ output.peek? = some (tailToken 11) := by
  refine ⟨_, _, canonical_lexing.2.2.1, pair_exec prior, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem canonical_missing_separator (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseTupleType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 2 [event nameA] ∧
      output.diagnostics = prior ++ [event nameA] ∧ output.window = { endIndex := 5, endByte := 12 } ∧
      output.peek? = some (sym 5 6 .plus) ∧ output.tokens[4]? = some (tailToken 8) ∧
      failure.expected.toList = [.symbol .comma, .symbol .rightParen] := by
  refine ⟨_, _, canonical_lexing.2.2.2, rejected_exec prior, rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalTupleTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParserCanonicalParserTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserCanonicalParserTotalityProperties

open Solcore.Syntax.Parser

example := @FileInternals.productionPlainTopItemTotalityContract
example := @FileInternals.productionPlainTopItem_ordinary
example := @FileInternals.productionPlainTopItem_invariantFreeOnValid
example := @FileInternals.productionPlainTopItem_ne_invariant
example := @FileInternals.productionTopItem_ordinary
example := @FileInternals.productionTopItem_invariantFreeOnValid
example := @FileInternals.productionTopItem_ne_invariant
example := @FileInternals.productionParseItemsItem_ordinary
example := @FileInternals.productionParseItemsItem_invariantFreeOnValid
example := @FileInternals.productionParseItemsItem_ne_invariant
example := @FileInternals.productionParseItemsItemInvariantFree
example := @FileInternals.productionSourceFile_exists_ok
example := @FileInternals.productionSourceFile_ordinary
example := @FileInternals.productionSourceFile_invariantFreeOnValid
example := @FileInternals.productionSourceFile_ne_invariant
example := @productionParseLexed_exists_ok
example := @productionParseLexed_ne_error
example := @productionParse_exists_ok
example := @productionParse_ne_error

end Solcore.Test.SyntaxParserCanonicalParserTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserProtectedDiagnosticTraceProperties
/-! Protected spelling events remain exact after mixed-prefix normalization. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserProtectedDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

example := @ParseDiagnosticCascadeFilters.append
example := @parseDiagnosticCascadeFilters_of_protected
example := @IdentifierDiagnosticTrace.not_candidate
example := @IdentifierDiagnosticTrace.cascadeFilters

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {name : Identifier} {trace : List ParseDiagnostic}
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    filterParseDiagnostics file lexical trace = trace :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (diagnostics.cascadeFilters file.content (lexical.map (·.span)))

/-- Earlier mixed reports are normalized, then the spelling suffix is retained
unchanged; neither prefix metadata nor suffix order is silently discarded. -/
theorem identifier_suffix_survives
    (file : SourceFile) (lexical : List LexicalDiagnostic)
    {name : Identifier} {prior kept trace : List ParseDiagnostic}
    (leading : ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) prior kept)
    (diagnostics : IdentifierDiagnosticTrace name trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = kept ++ trace :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (leading.append (diagnostics.cascadeFilters file.content (lexical.map (·.span))))

example (file : SourceFile) (lexical : List LexicalDiagnostic)
    {leftName rightName : Identifier} {left right : List ParseDiagnostic}
    (leftTrace : IdentifierDiagnosticTrace leftName left)
    (rightTrace : IdentifierDiagnosticTrace rightName right) :
    filterParseDiagnostics file lexical (left ++ right) = left ++ right :=
  filterParseDiagnostics_eq_of_cascadeFilters file lexical
    ((leftTrace.cascadeFilters file.content (lexical.map (·.span))).append
      (rightTrace.cascadeFilters file.content (lexical.map (·.span))))

end Solcore.Test.SyntaxParserProtectedDiagnosticTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedArrayReturnTraceProperties
/-! Checked-name arrays discharge exactness and protected-event assumptions
through returns and raw/isolated blocks. These are restricted independent trace
instances, not outcome-existence or general recursive expression claims. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedArrayReturnTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private abbrev arrayTrace := ArrayLiteralTraceParses IdentifierExpressionTraceParses
private abbrev arrayRejects := ArrayLiteralTraceRejects IdentifierExpressionTraceParses
  IdentifierExpressionTraceRejects
private abbrev returnTrace := ReturnStatementTraceParses arrayTrace
private abbrev returnRejects := ReturnStatementTraceRejects arrayTrace arrayRejects

theorem array_return_statement_exact (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec returnTrace returnRejects source endByte :=
  returnStatementTraceExactOutcomeSpec
    (arrayLiteralTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte))

theorem array_return_block_exact (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses returnTrace policy)
      (CoreBlockTraceRejects returnTrace returnRejects policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy (array_return_statement_exact source endByte)

theorem isolated_array_return_block_exact
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses returnTrace policy)
        (CoreBlockTraceRejects returnTrace returnRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects returnTrace returnRejects policy))
      source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (array_return_statement_exact source)

private theorem return_protected
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : returnTrace source endByte input statement output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun values => values.cascadeFilters (fun name => name.cascadeFilters text lexical))

theorem successful_array_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses returnTrace policy source endByte input body output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun returned => return_protected returned _ _))

/-- Earlier array-name events survive raw rejection, but its separate final
report is not asserted to survive normalization if a caller later commits it. -/
theorem rejected_array_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects returnTrace returnRejects policy source endByte
      input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact rejection.cascadeFilters (fun returned => return_protected returned _ _)
    (fun rejectedReturn => rejectedReturn.cascadeFilters
      (fun values => values.cascadeFilters (fun name => name.cascadeFilters _ _))
      (fun rejectedArray => ArrayLiteralTraceRejects.cascadeFilters
        (fun name => name.cascadeFilters _ _) (fun rejectedName => rejectedName.cascadeFilters _ _) rejectedArray))

end Solcore.Test.SyntaxProtectedArrayReturnTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties
/-! Raw comptime prefix failures bypass every child. Closing failure returns
the exact completed-child state, and protected event suffixes retain every
occurrence without including the separate uncommitted rejection report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_marker_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.comptime.spelling))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .contextual .comptime, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure input := by
  rcases (contextual_reject_reports_iff .comptime .typeExpr).mp ⟨absent, reported⟩ with
    ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, result]

theorem missing_opening_bypasses_every_child (nested : Parser TypeExpr)
    {input afterMarker : State} {marker : Token} {failure : Failure}
    (markerResult : contextual .comptime .typeExpr input = .ok marker afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.window.endIndex afterMarker.cursor (.symbol .less))
    (reported : RejectAtReports afterMarker.file.id afterMarker.window.endByte
      { head := .symbol .less, tail := [] } .typeExpr afterMarker.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure afterMarker := by
  rcases (symbol_reject_reports_iff .less .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, markerResult, result]

theorem missing_closing_keeps_complete_child_state (nested : Parser TypeExpr)
    {input afterMarker afterOpening afterInner : State}
    {marker opening : Token} {inner : TypeExpr} {failure : Failure}
    (markerResult : contextual .comptime .typeExpr input = .ok marker afterMarker)
    (openingResult : symbol .less .typeExpr afterMarker = .ok opening afterOpening)
    (childResult : nested afterOpening = .ok inner afterInner)
    (absent : TokenKindAbsentAt afterInner.tokens afterInner.window.endIndex afterInner.cursor (.symbol .greater))
    (reported : RejectAtReports afterInner.file.id afterInner.window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr afterInner.declarativeRemainder failure.toDiagnostic) :
    parseComptimeType nested input = .reject failure afterInner := by
  rcases (symbol_reject_reports_iff .greater .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseComptimeType, bind, markerResult, openingResult, childResult, result]

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ComptimeTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ComptimeTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectProtected))

end Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalComptimeTypeTraceExamples
/-! Canonical comptime types execute the real typeExpr child. Success and
closing rejection preserve its checked spelling event after every prior event,
with exact outer/angle spans, complete states, and untouched following tokens.
These concrete cases do not assume general recursive type trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalComptimeTypeTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-comptime-type-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 0 8, value := .identifier "comptime" }
private def name : Identifier := { span := span 9 12, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def inner : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

private theorem child_exec (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 2 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .dot))
    (noArguments : TokenKindAbsentAt tokens.toArray tokens.length 3 (.symbol .less)) :
    typeExpr (state content tokens prior 2 []) = .ok inner (state content tokens prior 3 [event]) :=
  checked_name_type (input := state content tokens prior 2 []) token
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide)) noDot noArguments (by decide) (by decide)

private def successText : String := "comptime<a-b> tail"
private def successTokens : List Token := [marker, sym 8 9 .less, nameToken, sym 12 13 .greater,
  { span := span 14 18, value := .identifier "tail" }]
private def value : TypeExpr := {
  span := span 0 13, value := .comptime (span 0 8) (span 8 13) inner
}

private theorem success_exec (prior : List ParseDiagnostic) :
    parseComptimeType typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 4 [event]) := by
  let s := state successText successTokens prior
  have child := child_exec successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 8 9)
    ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .greater .typeExpr
    (input := s 3 [event]) (after := (s 4 [event]).declarativeRemainder) (span := span 12 13)
    ⟨⟨by change 3 < 5; decide, rfl⟩, rfl⟩
  exact parseComptimeType_success_iff_components.mpr
    ⟨marker, s 1 [], sym 8 9 .less, s 2 [], inner, s 3 [event], sym 12 13 .greater,
      markerResult, openingResult, child, closingResult, rfl⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem comptime_type_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_comptime_type (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      parseComptimeType typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 4 [event] ∧
      output.declarativeRemainder = remainder successTokens 4 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 5, endByte := 18 } ∧
      output.peek? = some { span := span 14 18, value := .identifier "tail" } := by
  refine ⟨carrier successTokens, _, comptime_type_lexes, success_exec prior, rfl, rfl, ?_, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

private def rejectedText : String := "comptime<a-b +> tail"
private def rejectedTokens : List Token := [marker, sym 8 9 .less, nameToken,
  sym 13 14 .plus, sym 14 15 .greater, { span := span 16 20, value := .identifier "tail" }]
private def failure : Failure := {
  span := span 13 14, found := some (.symbol .plus)
  expected := { head := .symbol .greater, tail := [] }, context := .typeExpr
}

private theorem rejection_exec (prior : List ParseDiagnostic) :
    parseComptimeType typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 3 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have child := child_exec rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 8)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 8 9)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have missing : TokenKindAbsentAt (s 3 [event]).tokens (s 3 [event]).window.endIndex
      (s 3 [event]).cursor (.symbol .greater) := by
    simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, rejectedTokens, sym]
  have reported : RejectAtReports (s 3 [event]).file.id (s 3 [event]).window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr (s 3 [event]).declarativeRemainder failure.toDiagnostic :=
    .reported (.token (current := sym 13 14 .plus) ⟨by change 3 < 6; decide, rfl⟩)
  exact missing_closing_keeps_complete_child_state typeExpr markerResult openingResult child missing reported

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_comptime_type_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_comptime_closing_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      parseComptimeType typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 3 [event] ∧
      output.declarativeRemainder = remainder rejectedTokens 3 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 20 } ∧ output.peek? = some (sym 13 14 .plus) ∧
      output.tokens[5]? = some { span := span 16 20, value := .identifier "tail" } := by
  refine ⟨carrier rejectedTokens, _, rejected_comptime_type_lexes, rejection_exec prior, rfl, rfl, ?_, rfl, rfl, rfl⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxCanonicalComptimeTypeTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxCanonicalTypeExprTraceExamples
/-! Canonical, multiply nested public type-expression executions. Component
proofs connect proxy, comptime, and the checked name leaf, then the recursive
soundness contracts supply the fuel-free trace. Existing events, complete
states, exact spans, uncommitted failures, and following tokens are retained.
Only the finite lexer examples use kernel evaluation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCanonicalTypeExprTraceExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxProtectedComptimeTypeTraceProperties

private def source : SourceId := { origin := .main, path := "canonical-type-expr-trace.sol" }
private def file (content : String) : SourceFile := { id := source, content }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def marker : Token := { span := span 1 9, value := .identifier "comptime" }
private def name : Identifier := { span := span 10 13, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def inner : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def state (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with cursor, diagnosticsRev := fresh.reverse ++ prior.reverse
}
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}

private theorem child_exec (fuel : Nat) (content : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (token : TokenAt tokens.toArray tokens.length 3 nameToken)
    (noDot : TokenKindAbsentAt tokens.toArray tokens.length 4 (.symbol .dot))
    (noArguments : TokenKindAbsentAt tokens.toArray tokens.length 4 (.symbol .less)) :
    typeExprWithFuel (fuel + 1) (state content tokens prior 3 []) =
      .ok inner (state content tokens prior 4 [event]) :=
  checked_name_type_with_positive_fuel fuel (input := state content tokens prior 3 []) token
    (.hyphen (by unfold IdentifierHyphenSpelling name; decide)) noDot noArguments (by decide) (by decide)

private def successText : String := "@comptime<a-b> tail"
private def successTokens : List Token := [sym 0 1 .at, marker, sym 9 10 .less, nameToken,
  sym 13 14 .greater, { span := span 15 19, value := .identifier "tail" }]
private def comptimeValue : TypeExpr := {
  span := span 1 14, value := .comptime (span 1 9) (span 9 14) inner
}
private def value : TypeExpr := { span := span 0 14, value := .proxy (span 0 1) comptimeValue }

private theorem success_with_fuel (fuel : Nat) (prior : List ParseDiagnostic) :
    typeExprWithFuel (fuel + 3) (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 5 [event]) := by
  let s := state successText successTokens prior
  have child := child_exec fuel successText successTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, successTokens, sym])
  have proxyResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 1 9)
    ⟨⟨by change 1 < 6; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 2 []) (after := (s 3 []).declarativeRemainder) (span := span 9 10)
    ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .greater .typeExpr
    (input := s 4 [event]) (after := (s 5 [event]).declarativeRemainder) (span := span 13 14)
    ⟨⟨by change 4 < 6; decide, rfl⟩, rfl⟩
  have comptimeResult : typeExprWithFuel (fuel + 2) (s 1 []) = .ok comptimeValue (s 5 [event]) := by
    rw [typeExprWithFuel_eq_raw_of_selection (fuel + 1)
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (s 1 []) = .comptime from rfl))]
    exact parseComptimeType_success_iff_components.mpr
      ⟨marker, s 2 [], sym 9 10 .less, s 3 [], inner, s 4 [event], sym 13 14 .greater,
        markerResult, openingResult, child, closingResult, rfl⟩
  rw [typeExprWithFuel_eq_raw_of_selection (fuel + 2)
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (s 0 []) = .proxy from rfl))]
  exact parseProxyType_success_iff_components.mpr
    ⟨sym 0 1 .at, s 1 [], comptimeValue, proxyResult, comptimeResult, rfl⟩

private theorem success_exec (prior : List ParseDiagnostic) :
    typeExpr (state successText successTokens prior 0 []) =
      .ok value (state successText successTokens prior 5 [event]) :=
  success_with_fuel 4 prior

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem nested_type_lexes : Lexer.lex (file successText) = .ok (carrier successTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_nested_type (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file successText) = .ok lexed ∧
      typeExpr { State.initial (file successText) lexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output = state successText successTokens prior 5 [event] ∧
      output.declarativeRemainder = remainder successTokens 5 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 6, endByte := 19 } ∧
      output.peek? = some { span := span 15 19, value := .identifier "tail" } ∧
      TypeExprTraceParses source 19 (remainder successTokens 0) value (remainder successTokens 5) [event] := by
  rcases typeExpr_trace_success_sound (success_exec prior) with ⟨trace, parsed, events⟩
  have exactEvents : (state successText successTokens prior 5 [event]).diagnostics =
      (state successText successTokens prior 0 []).diagnostics ++ [event] := by
    simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_nil, List.nil_append]
  have same := List.append_cancel_left (events.symm.trans exactEvents)
  refine ⟨carrier successTokens, _, nested_type_lexes, success_exec prior, rfl, rfl, ?_, rfl, rfl, ?_⟩
  · simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]
  · have endByte : (state successText successTokens prior 0 []).window.endByte = 19 := rfl
    have sourceEq : (state successText successTokens prior 0 []).file.id = source := rfl
    have inputEq : (state successText successTokens prior 0 []).declarativeRemainder =
        remainder successTokens 0 := rfl
    have outputEq : (state successText successTokens prior 5 [event]).declarativeRemainder =
        remainder successTokens 5 := rfl
    simpa only [same, endByte, sourceEq, inputEq, outputEq] using parsed

private def rejectedText : String := "@comptime<a-b +> tail"
private def rejectedTokens : List Token := [sym 0 1 .at, marker, sym 9 10 .less, nameToken,
  sym 14 15 .plus, sym 15 16 .greater, { span := span 17 21, value := .identifier "tail" }]
private def failure : Failure := {
  span := span 14 15, found := some (.symbol .plus)
  expected := { head := .symbol .greater, tail := [] }, context := .typeExpr
}

private theorem rejection_with_fuel (fuel : Nat) (prior : List ParseDiagnostic) :
    typeExprWithFuel (fuel + 3) (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 4 [event]) := by
  let s := state rejectedText rejectedTokens prior
  have child := child_exec fuel rejectedText rejectedTokens prior ⟨by decide, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
    (by simp [TokenKindAbsentAt, TokenAt, rejectedTokens, sym])
  have proxyResult := symbol_eq_ok_of_exactTokenParses .at .typeExpr
    (input := s 0 []) (after := (s 1 []).declarativeRemainder) (span := span 0 1)
    ⟨⟨by change 0 < 7; decide, rfl⟩, rfl⟩
  have markerResult := contextual_eq_ok_of_exactTokenParses .comptime .typeExpr
    (input := s 1 []) (after := (s 2 []).declarativeRemainder) (span := span 1 9)
    ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩
  have openingResult := symbol_eq_ok_of_exactTokenParses .less .typeExpr
    (input := s 2 []) (after := (s 3 []).declarativeRemainder) (span := span 9 10)
    ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩
  have missing : TokenKindAbsentAt (s 4 [event]).tokens (s 4 [event]).window.endIndex
      (s 4 [event]).cursor (.symbol .greater) := by
    simp [TokenKindAbsentAt, TokenAt, s, state, State.initial, carrier, rejectedTokens, sym]
  have reported : RejectAtReports (s 4 [event]).file.id (s 4 [event]).window.endByte
      { head := .symbol .greater, tail := [] } .typeExpr (s 4 [event]).declarativeRemainder failure.toDiagnostic :=
    .reported (.token (current := sym 14 15 .plus) ⟨by change 4 < 7; decide, rfl⟩)
  have comptimeResult : typeExprWithFuel (fuel + 2) (s 1 []) = .reject failure (s 4 [event]) := by
    rw [typeExprWithFuel_eq_raw_of_selection (fuel + 1)
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (s 1 []) = .comptime from rfl))]
    exact missing_closing_keeps_complete_child_state (typeExprWithFuel (fuel + 1))
      markerResult openingResult child missing reported
  rw [typeExprWithFuel_eq_raw_of_selection (fuel + 2)
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (s 0 []) = .proxy from rfl))]
  exact parseProxyType_reject_iff_components.mpr (.inr ⟨sym 0 1 .at, s 1 [], proxyResult, comptimeResult⟩)

private theorem rejection_exec (prior : List ParseDiagnostic) :
    typeExpr (state rejectedText rejectedTokens prior 0 []) =
      .reject failure (state rejectedText rejectedTokens prior 4 [event]) :=
  rejection_with_fuel 5 prior

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
theorem rejected_nested_type_lexes : Lexer.lex (file rejectedText) = .ok (carrier rejectedTokens) := by
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

theorem canonical_nested_type_failure (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file rejectedText) = .ok lexed ∧
      typeExpr { State.initial (file rejectedText) lexed with diagnosticsRev := prior.reverse } =
        .reject failure output ∧ output = state rejectedText rejectedTokens prior 4 [event] ∧
      output.declarativeRemainder = remainder rejectedTokens 4 ∧ output.diagnostics = prior ++ [event] ∧
      output.window = { endIndex := 7, endByte := 21 } ∧ output.peek? = some (sym 14 15 .plus) ∧
      output.tokens[6]? = some { span := span 17 21, value := .identifier "tail" } ∧
      TypeExprTraceRejects source 21 (remainder rejectedTokens 0) (remainder rejectedTokens 4)
        failure.toDiagnostic [event] := by
  rcases typeExpr_reject_trace_sound (rejection_exec prior) with ⟨trace, rejected, events⟩
  have exactEvents : (state rejectedText rejectedTokens prior 4 [event]).diagnostics =
      (state rejectedText rejectedTokens prior 0 []).diagnostics ++ [event] := by
    simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_nil, List.nil_append]
  have same := List.append_cancel_left (events.symm.trans exactEvents)
  refine ⟨carrier rejectedTokens, _, rejected_nested_type_lexes, rejection_exec prior,
    rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]
  · have endByte : (state rejectedText rejectedTokens prior 0 []).window.endByte = 21 := rfl
    have sourceEq : (state rejectedText rejectedTokens prior 0 []).file.id = source := rfl
    have inputEq : (state rejectedText rejectedTokens prior 0 []).declarativeRemainder =
        remainder rejectedTokens 0 := rfl
    have outputEq : (state rejectedText rejectedTokens prior 4 [event]).declarativeRemainder =
        remainder rejectedTokens 4 := rfl
    simpa only [same, endByte, sourceEq, inputEq, outputEq] using rejected

end Solcore.Test.SyntaxCanonicalTypeExprTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedDelimitedTraceProperties
/-! Complete checked-name suffixes survive actual normalization through
no-trailing lists. A later rejection does not erase successful earlier names,
and its separate uncommitted report is deliberately outside this guarantee. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDelimitedTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

theorem successful_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {source : SourceId} {endByte : Nat}
    {input output : Remainder} {values : DelimitedList Expr} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty IdentifierExpressionTraceParses
      source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun value => value.cascadeFilters _ _))

theorem rejected_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun value => value.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedDelimitedTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedDelimitedTrailingTraceProperties
/-! Complete ordered checked-name suffixes, including repeated events, survive
actual normalization on both trailing-enabled outcomes. The final uncommitted
rejection report is separate and is not claimed to be protected. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDelimitedTrailingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem successful_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {source : SourceId} {endByte : Nat}
    {input output : Remainder} {values : DelimitedList Expr} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty IdentifierExpressionTraceParses
      source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (parsed.cascadeFilters (fun value => value.cascadeFilters _ _)))

theorem rejected_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters (fun value => value.cascadeFilters _ _)
        (fun rejectedName => rejectedName.cascadeFilters _ _)))

end Solcore.Test.SyntaxProtectedDelimitedTrailingTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedDotConstructorTraceProperties
/-! Concrete child exactness and full diagnostic normalization compose at the
leading-dot constructor boundary without assuming recursive expression laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDotConstructorTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

theorem checked_name_constructor_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses IdentifierExpressionTraceParses)
      (DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  dotConstructorTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem checked_name_optional_arguments_exact (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (OptionalDotConstructorArgumentsTraceParses IdentifierExpressionTraceParses)
      (OptionalDotConstructorArgumentsTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  optionalDotConstructorArgumentsTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem literal_constructor_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses LiteralExpressionTraceParses)
      (DotConstructorTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  dotConstructorTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

/-- Normalizing earlier diagnostics cannot remove or reorder the constructor
name and successful argument events preceding a rejected checked-name child.
The final unexpected-token report is separate and is not protected here. -/
theorem rejected_name_constructor_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun name => name.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedDotConstructorTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedFunctionReturnsTraceProperties
/-! Optional returns preserve the complete state on absence. Protected child
events survive normalization in order; the terminal report stays uncommitted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedFunctionReturnsTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals

theorem absent_keeps_entire_state (nested : Parser TypeExpr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.returns.spelling)) :
    parseFunctionReturns nested input = .ok none input :=
  parseFunctionReturns_eq_none_of_absent nested absent

theorem success_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {values : Option (DelimitedList TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : FunctionReturnsTraceParses typeTrace source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input output report trace}, typeRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionReturnsTraceRejects typeTrace typeRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

end Solcore.Test.SyntaxProtectedFunctionReturnsTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedFunctionTypeTraceProperties
/-! Raw function types preserve absent-return states and parameter end spans.
Protected parameter/return suffixes retain duplicates and order, excluding the
separate terminal report on rejection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedFunctionTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeFunctionInternals

theorem missing_keyword_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.keyword .functionKw))
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .keyword .functionKw, tail := [] } .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseFunctionType nested input = .reject failure input := by
  rcases (keyword_reject_reports_iff .functionKw .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact parseFunctionType_reject_iff_components.mpr (.inl result)

theorem absent_returns_keeps_parameter_span_and_state (nested : Parser TypeExpr)
    {input afterKeyword afterParameters : State} {marker : Token} {parameters : DelimitedList TypeExpr}
    (keywordResult : keyword .functionKw .typeExpr input = .ok marker afterKeyword)
    (parameterResult : delimited .leftParen .rightParen true nested .typeExpr .typeExpr afterKeyword =
      .ok parameters afterParameters)
    (absent : TokenKindAbsentAt afterParameters.tokens afterParameters.window.endIndex afterParameters.cursor
      (.identifier ContextualKeyword.returns.spelling)) :
    parseFunctionType nested input = .ok {
      span := SourceSpan.cover marker.span parameters.span
      value := .function marker.span parameters none
    } afterParameters :=
  parseFunctionType_success_iff_components.mpr
    ⟨_, _, _, _, _, keywordResult, parameterResult, parseFunctionReturns_eq_none_of_absent nested absent, rfl⟩

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : FunctionTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : FunctionTypeTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

end Solcore.Test.SyntaxProtectedFunctionTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedNamedTypeArgumentsTraceProperties
/-! Optional absence bypasses every recursive child. Protected child events
retain their full multiplicity on either selected outcome; the separate final
failure report is deliberately outside this normalization guarantee. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedNamedTypeArgumentsTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem absent_arguments_bypass_every_child (nested : Parser TypeExpr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .less)) :
    parseNamedTypeArguments nested input = .ok none input ∧
      ∀ failure rejected, parseNamedTypeArguments nested input ≠ .reject failure rejected := by
  have result := parseNamedTypeArguments_eq_none_of_absent nested absent
  exact ⟨result, by intro failure rejected; rw [result]; intro impossible; cases impossible⟩

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_arguments_keep_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {values : Option (NonemptyDelimitedList TypeExpr)} {trace : List ParseDiagnostic}
    (parsed : NamedTypeArgumentsTraceParses elementTrace source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_arguments_keep_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeArgumentsTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxProtectedNamedTypeArgumentsTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedParenthesizedTraceProperties
/-! Concrete child exactness and protected normalization for parenthesized
expressions. Raw rejection does not commit or protect its final report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedParenthesizedTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem checked_name_parenthesized_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses)
      (ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  parenthesizedTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem literal_parenthesized_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses LiteralExpressionTraceParses)
      (ParenthesizedExpressionTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  parenthesizedTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

theorem successful_parenthesized_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr}
    {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses
      source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun name => name.cascadeFilters _ _))

theorem rejected_parenthesized_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun name => name.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedParenthesizedTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedProxyTraceProperties
/-! Proxy normalization inherits exactly the type's protected trace. Marker
failure bypasses the type with unchanged full State and an uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedProxyTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

theorem missing_marker_preserves_every_state_field
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .at))
    (reported : RejectAtReports input.file.id input.window.endByte
      { head := .symbol .at, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    proxyExpression input = .reject failure input := by
  rcases (symbol_reject_reports_iff .at .expression).mp ⟨absent, reported⟩ with
    ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact proxyExpression_reject_iff_components.mpr (.inl result)

theorem successful_proxy_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr}
    {trace : List ParseDiagnostic}
    (childProtected : ∀ {input type output trace}, typeTrace source endByte input type output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (parsed : ProxyExpressionTraceParses typeTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected)

theorem rejected_proxy_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (childProtected : ∀ {input rejected report trace}, typeRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejection : ProxyExpressionTraceRejects typeRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (rejection.cascadeFilters childProtected)

end Solcore.Test.SyntaxProtectedProxyTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedProxyTypeTraceProperties
/-! Raw proxy-type failures do not commit reports, and all protected nested
events survive normalization without deduplication or source-validity premises. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedProxyTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_marker_keeps_entire_state (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .at))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .symbol .at, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseProxyType nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .at .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact parseProxyType_reject_iff_components.mpr (.inl result)

theorem success_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : ProxyTypeTraceParses typeTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input output report trace}, typeRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ProxyTypeTraceRejects typeRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (rejection.cascadeFilters childProtected))

end Solcore.Test.SyntaxProtectedProxyTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedStatementTraceProperties
/-! Actual diagnostic normalization keeps complete checked-name event suffixes
through return-only blocks. Earlier diagnostics may still be filtered normally. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedStatementTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private theorem return_protected
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses IdentifierExpressionTraceParses
      source endByte input statement output trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun value => value.cascadeFilters text lexical)

/-- Lexical errors may remove prior cascade candidates, but never any fresh
name event from the complete raw return-block trace, even repeated payloads. -/
theorem successful_name_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      policy source endByte input body output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun statement => return_protected statement _ _))

/-- The same holds when a later return rejects. Its uncommitted final report
is separate; this theorem intentionally does not include or protect that report. -/
theorem rejected_name_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      policy source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact rejection.cascadeFilters (fun statement => return_protected statement _ _)
    (fun rejectedReturn => rejectedReturn.cascadeFilters
      (fun value => value.cascadeFilters _ _) (fun rejectedName => rejectedName.cascadeFilters _ _))

/-- One extra raw block-statement wrapper still preserves all events; the
inner block's ordered tail constraints are protected along with checked names. -/
theorem nested_name_return_statement_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses
      (BlockStatementTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses))
      source endByte input statement output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun inner => inner.cascadeFilters
      (fun returned => return_protected returned _ _)))

end Solcore.Test.SyntaxProtectedStatementTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedTupleTypeTraceProperties
/-! Protected tuple child events remain ordered after every incoming diagnostic.
The separate rejection report is not added to this normalization suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedTupleTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_opening_keeps_entire_state (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .symbol .leftParen, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseTupleType nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .leftParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  apply parseTupleType_reject_iff_list.mpr
  simp only [delimited, delimitedWithPolicy, result]

theorem success_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TupleTypeTraceParses typeTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    {source : SourceId} {endByte : Nat}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, typeTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input output report trace}, typeRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TupleTypeTraceRejects typeTrace typeRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (TupleTypeTraceRejects.cascadeFilters successProtected rejectProtected rejection))

end Solcore.Test.SyntaxProtectedTupleTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxProtectedTypeDispatchTraceProperties
/-! Conditional protection lifts through every selected raw form without
reordering or deduplicating the event suffix. Final reports are uncommitted;
the final branch contributes an empty suffix for every nested trace relation. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedTypeDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejection_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (successProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectProtected : ∀ {input rejected report trace}, elementRejects source endByte input rejected report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters successProtected rejectProtected))

theorem final_report_contributes_no_event
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (selection : TypeDispatchSelects input .final)
    (rejection : TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace) :
    rejected = input ∧ trace = [] ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior := by
  rcases (TypeDispatchTraceRejects.final_iff selection).mp rejection with ⟨rfl, _, rfl⟩
  exact ⟨rfl, rfl, by simp only [List.append_nil]⟩

end Solcore.Test.SyntaxProtectedTypeDispatchTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeDispatchTraceProperties
/-! Boundary consumers of the real positive-fuel dispatcher. Token-carrier
fixtures deliberately need no source-validity law; the active window, not the
backing array, controls contextual pairs. Only finite lexing is evaluated. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeDispatchTraceInternals

private def source : SourceId := { origin := .main, path := "type-dispatch-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def token (kind : TokenKind) : Token := { span := span 0 1, value := kind }
private def state (kinds : List TokenKind) (endIndex : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }
  tokens := (kinds.map token).toArray
  cursor := 0
  window := { endIndex, endByte := 99 }
  diagnosticsRev := prior.reverse
}

private theorem runs_selected (fuel : Nat) {input : State} {branch : TypeDispatchBranch}
    (selected : selectedBranch input = branch) :
    typeExprWithFuel (fuel + 1) input = rawParser (typeExprWithFuel fuel) branch input :=
  typeExprWithFuel_eq_raw_of_selection fuel (selectedBranch_eq_iff.mp selected)

theorem function_keyword_and_identifier_are_distinct (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.keyword .functionKw] 1 prior) = .function ∧
    selectedBranch (state [.identifier "function"] 1 prior) = .named ∧
    typeExprWithFuel (fuel + 1) (state [.keyword .functionKw] 1 prior) =
      parseFunctionType (typeExprWithFuel fuel) (state [.keyword .functionKw] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "function"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "function"] 1 prior) := by
  exact ⟨rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem mapping_requires_its_left_parenthesis (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.identifier "mapping"] 1 prior) = .named ∧
    selectedBranch (state [.identifier "mapping", .symbol .less] 2 prior) = .named ∧
    selectedBranch (state [.identifier "mapping", .symbol .leftParen] 2 prior) = .mapping ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping"] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .less] 2 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .less] 2 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .leftParen] 2 prior) =
      parseMappingType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .leftParen] 2 prior) := by
  exact ⟨rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem comptime_requires_its_angle (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.identifier "comptime"] 1 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .leftParen] 2 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .less] 2 prior) = .comptime ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime"] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .leftParen] 2 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .leftParen] 2 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .less] 2 prior) =
      parseComptimeType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .less] 2 prior) := by
  exact ⟨rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem proxy_and_tuple_have_their_own_branches (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.symbol .at] 1 prior) = .proxy ∧
    selectedBranch (state [.symbol .leftParen] 1 prior) = .tuple ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .at] 1 prior) =
      parseProxyType (typeExprWithFuel fuel) (state [.symbol .at] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .leftParen] 1 prior) =
      parseTupleType (typeExprWithFuel fuel) (state [.symbol .leftParen] 1 prior) := by
  exact ⟨rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem hidden_second_tokens_do_not_select_pairs (fuel : Nat) (prior : List ParseDiagnostic) :
    (state [.identifier "mapping", .symbol .leftParen] 1 prior).tokens[1]? = some (token (.symbol .leftParen)) ∧
    (state [.identifier "comptime", .symbol .less] 1 prior).tokens[1]? = some (token (.symbol .less)) ∧
    (state [.identifier "mapping", .symbol .leftParen] 1 prior).peekOffsetKind? 1 = none ∧
    (state [.identifier "comptime", .symbol .less] 1 prior).peekOffsetKind? 1 = none ∧
    selectedBranch (state [.identifier "mapping", .symbol .leftParen] 1 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .less] 1 prior) = .named ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .leftParen] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .leftParen] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .less] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .less] 1 prior) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem final_selection_keeps_complete_state (fuel : Nat) {input : State}
    (selection : TypeDispatchSelects input.declarativeRemainder .final) :
    typeExprWithFuel (fuel + 1) input = .reject {
      span := input.currentSpan, found := input.peekKind?
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } input := by
  rw [typeExprWithFuel_eq_raw_of_selection fuel selection]
  rfl

theorem unexpected_token_reports_without_commit (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.symbol .plus] 1 prior) = .final ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .plus] 1 prior) = .reject {
      span := span 0 1, found := some (.symbol .plus)
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } (state [.symbol .plus] 1 prior) ∧
    (state [.symbol .plus] 1 prior).diagnostics = prior := by
  refine ⟨rfl, final_selection_keeps_complete_state fuel (selectedBranch_eq_iff.mp rfl), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

theorem hidden_current_token_reports_window_end (fuel : Nat) (prior : List ParseDiagnostic) :
    (state [.keyword .functionKw] 0 prior).tokens[0]? = some (token (.keyword .functionKw)) ∧
    selectedBranch (state [.keyword .functionKw] 0 prior) = .final ∧
    typeExprWithFuel (fuel + 1) (state [.keyword .functionKw] 0 prior) = .reject {
      span := span 99 99, found := none
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } (state [.keyword .functionKw] 0 prior) ∧
    (state [.keyword .functionKw] 0 prior).diagnostics = prior := by
  refine ⟨rfl, rfl, final_selection_keeps_complete_state fuel (selectedBranch_eq_iff.mp rfl), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

private def canonicalFile : SourceFile := { id := source, content := "mapping(" }
private def canonicalLexed : LexedFile := {
  source, tokens := [
    { span := span 0 7, value := .identifier "mapping" },
    { span := span 7 8, value := .symbol .leftParen }
  ], comments := [], diagnostics := []
}

set_option maxRecDepth 16384 in
theorem canonical_mapping_prefix_lexes_and_selects (fuel : Nat) (prior : List ParseDiagnostic) :
    Lexer.lex canonicalFile = .ok canonicalLexed ∧
    selectedBranch { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } = .mapping ∧
    typeExprWithFuel (fuel + 1) { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } =
      parseMappingType (typeExprWithFuel fuel)
        { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } := by
  refine ⟨?_, rfl, runs_selected fuel rfl⟩
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxTypeDispatchTraceProperties
end
