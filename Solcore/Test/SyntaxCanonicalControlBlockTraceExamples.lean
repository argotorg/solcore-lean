import Solcore.Test.SyntaxControlLeafBlockTraceExamples
import Solcore.Test.SyntaxControlLeafBlockRejectionExamples

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
