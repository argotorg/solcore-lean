import Solcore.Test.SyntaxArrayLiteralTraceExamples
import Solcore.Syntax.Parser.Expression.Atom

/-! Distinct array rejection routes with the actual identifier child. After
a comma the child runs even at a closing bracket; without a comma the list
expects comma then closing bracket. Failure reports remain uncommitted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxArrayLiteralRejectionTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxArrayLiteralTraceExamples

def nameFailure (location : SourceSpan) (found : Symbol) : Failure := {
  span := location, found := some (.symbol found)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem name_rejected_at_symbol {input : Remainder} (reportSource : SourceId) (endByte : Nat)
    (location : SourceSpan) (found : Symbol)
    (token : TokenAt input.tokens input.endIndex input.cursor { span := location, value := .symbol found }) :
    IdentifierExpressionTraceRejects reportSource endByte input input
      (nameFailure location found).toDiagnostic [] := by
  have booleans : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := TokenAt.token_unique token other <;> cases impossible
  have names : IdentifierAbsentAt input := by
    rintro ⟨otherSpan, otherText, other⟩
    have impossible := TokenAt.token_unique token other
    cases impossible
  exact ⟨booleans, .absent names, .reported (.token token), rfl⟩

private theorem rejection_exec (text : String) (tokens : List Token) (prior : List ParseDiagnostic)
    (failure : Failure) (after : Remainder) (trace : List ParseDiagnostic)
    (rejection : ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source (file text).content.utf8ByteSize (remainder tokens tokens.length 0)
      after failure.toDiagnostic trace) :
    ∃ output, arrayLiteral identifierExpression (initial text tokens prior) = .reject failure output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ trace ∧
      output.tokens = tokens.toArray ∧ output.window = (initial text tokens prior).window := by
  rcases (arrayLiteral_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context
      (input := initial text tokens prior)).mp rejection with ⟨output, result, afterEq, events⟩
  have frame := arrayLiteral_preservesTokenWindow identifierExpression
    identifierExpression_preservesTokenWindow (initial text tokens prior)
  rw [result] at frame
  refine ⟨output, result, afterEq, ?_, frame.1, frame.2⟩
  simpa only [initial, State.initial, State.diagnostics, List.reverse_reverse] using events

def commaText : String := "[a-b,+] tail"
def commaTokens : List Token := [symbolToken 0 1 .leftBracket, nameToken nameA,
  symbolToken 4 5 .comma, symbolToken 5 6 .plus, symbolToken 6 7 .rightBracket,
  { span := span 8 12, value := .identifier "tail" }]

theorem comma_child_rejected :
    ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder commaTokens 6 0) (remainder commaTokens 6 3)
      (nameFailure (span 5 6) .plus).toDiagnostic [hyphen nameA] := by
  unfold ArrayLiteralTraceRejects
  exact .tailRejected (span 0 1) (input := remainder commaTokens 6 0)
    (opening := .leftBracket) (closing := .rightBracket) (afterOpening := remainder commaTokens 6 1)
    (afterFirst := remainder commaTokens 6 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, commaTokens, nameToken]))
    (name_trace (input := remainder commaTokens 6 1) nameA source 12
      ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide)
    (.elementRejected (span 4 5) (afterComma := remainder commaTokens 6 3)
      ⟨⟨by decide, rfl⟩, rfl⟩ (name_rejected_at_symbol source 12 (span 5 6) .plus ⟨by decide, rfl⟩))

/-- A comma invokes the actual identifier child; its identifier failure at
plus wins. The preceding hyphen survives and the final report is not added. -/
theorem comma_array_rejection (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral identifierExpression (initial commaText commaTokens prior) =
        .reject (nameFailure (span 5 6) .plus) output ∧
      output.declarativeRemainder = remainder commaTokens 6 3 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.tokens = commaTokens.toArray ∧
      output.window = (initial commaText commaTokens prior).window :=
  rejection_exec commaText commaTokens prior _ _ _ comma_child_rejected

def delimiterText : String := "[a-b +] tail"
def delimiterTokens : List Token := [symbolToken 0 1 .leftBracket, nameToken nameA,
  symbolToken 5 6 .plus, symbolToken 6 7 .rightBracket,
  { span := span 8 12, value := .identifier "tail" }]
def delimiterFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightBracket] }, context := .expression
}

theorem delimiter_rejected :
    ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 12
      (remainder delimiterTokens 5 0) (remainder delimiterTokens 5 2)
      delimiterFailure.toDiagnostic [hyphen nameA] := by
  unfold ArrayLiteralTraceRejects
  exact .tailRejected (span 0 1) (input := remainder delimiterTokens 5 0)
    (opening := .leftBracket) (closing := .rightBracket) (afterOpening := remainder delimiterTokens 5 1)
    (afterFirst := remainder delimiterTokens 5 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, nameToken]))
    (name_trace (input := remainder delimiterTokens 5 1) nameA source 12
      ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide)
    (.delimiterMissing
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, symbolToken])
      (by simp [TokenKindAbsentAt, TokenAt, remainder, delimiterTokens, symbolToken])
      (.reported (.token (current := symbolToken 5 6 .plus) ⟨by decide, rfl⟩)))

/-- No comma means the delimiter guard fails before another child is called.
The full report preserves the ordered expectations comma then right bracket. -/
theorem missing_delimiter_array_rejection (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral identifierExpression (initial delimiterText delimiterTokens prior) =
        .reject delimiterFailure output ∧ output.declarativeRemainder = remainder delimiterTokens 5 2 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.tokens = delimiterTokens.toArray ∧
      output.window = (initial delimiterText delimiterTokens prior).window :=
  rejection_exec delimiterText delimiterTokens prior _ _ _ delimiter_rejected

def trailingText : String := "[a-b,] tail"
def trailingTokens : List Token := [symbolToken 0 1 .leftBracket, nameToken nameA,
  symbolToken 4 5 .comma, symbolToken 5 6 .rightBracket,
  { span := span 7 11, value := .identifier "tail" }]

theorem trailing_child_rejected :
    ArrayLiteralTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 11
      (remainder trailingTokens 5 0) (remainder trailingTokens 5 3)
      (nameFailure (span 5 6) .rightBracket).toDiagnostic [hyphen nameA] := by
  unfold ArrayLiteralTraceRejects
  exact .tailRejected (span 0 1) (input := remainder trailingTokens 5 0)
    (opening := .leftBracket) (closing := .rightBracket) (afterOpening := remainder trailingTokens 5 1)
    (afterFirst := remainder trailingTokens 5 2) ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, trailingTokens, nameToken]))
    (name_trace (input := remainder trailingTokens 5 1) nameA source 11
      ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
    (by decide)
    (.elementRejected (span 4 5) (afterComma := remainder trailingTokens 5 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (name_rejected_at_symbol source 11 (span 5 6) .rightBracket ⟨by decide, rfl⟩))

/-- A trailing comma rejects for this actual child because right bracket is
not an identifier. This is not a rejection claim for every possible child. -/
theorem trailing_comma_identifier_array_rejection (prior : List ParseDiagnostic) :
    ∃ output, arrayLiteral identifierExpression (initial trailingText trailingTokens prior) =
        .reject (nameFailure (span 5 6) .rightBracket) output ∧
      output.declarativeRemainder = remainder trailingTokens 5 3 ∧
      output.diagnostics = prior ++ [hyphen nameA] ∧ output.tokens = trailingTokens.toArray ∧
      output.window = (initial trailingText trailingTokens prior).window :=
  rejection_exec trailingText trailingTokens prior _ _ _ trailing_child_rejected

/-- The rejected array's preceding name trace is protected; its separate
unexpected-token report is deliberately excluded from this assertion. -/
theorem rejected_name_array_protected (normalizationFile : SourceFile) (lexical : List LexicalDiagnostic)
    (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ [hyphen nameA]) =
      filterParseDiagnostics normalizationFile lexical prior ++ [hyphen nameA] := by
  rw [filterParseDiagnostics_append]
  exact congrArg (filterParseDiagnostics normalizationFile lexical prior ++ ·)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical
      (ArrayLiteralTraceRejects.cascadeFilters (fun name => name.cascadeFilters _ _)
        (fun rejection => rejection.cascadeFilters _ _) comma_child_rejected))

set_option maxRecDepth 16384 in
theorem comma_lexes : Lexer.lex (file commaText) = .ok (carrier commaTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 16384 in
theorem delimiter_lexes : Lexer.lex (file delimiterText) = .ok (carrier delimiterTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_comma_child_rejection :
    ∃ lexed output, Lexer.lex (file commaText) = .ok lexed ∧
      arrayLiteral identifierExpression (State.initial (file commaText) lexed) =
        .reject (nameFailure (span 5 6) .plus) output ∧
      output.declarativeRemainder = remainder commaTokens 6 3 ∧ output.diagnostics = [hyphen nameA] := by
  rcases comma_array_rejection [] with ⟨output, result, after, events, _, _⟩
  exact ⟨carrier commaTokens, output, comma_lexes, result, after, events⟩

theorem canonical_missing_delimiter_rejection :
    ∃ lexed output, Lexer.lex (file delimiterText) = .ok lexed ∧
      arrayLiteral identifierExpression (State.initial (file delimiterText) lexed) =
        .reject delimiterFailure output ∧ output.declarativeRemainder = remainder delimiterTokens 5 2 ∧
      output.diagnostics = [hyphen nameA] := by
  rcases missing_delimiter_array_rejection [] with ⟨output, result, after, events, _, _⟩
  exact ⟨carrier delimiterTokens, output, delimiter_lexes, result, after, events⟩

end Solcore.Test.SyntaxArrayLiteralRejectionTraceExamples
