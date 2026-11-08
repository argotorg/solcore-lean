import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.ParenthesizedTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Test.Syntax.Statements
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.ParameterSoundness

/-!
# Expression atom tests

Atoms of the expression grammar: literals, array literals, parenthesized forms and dot
constructors, with their dispatch, recovery, rejection and totality statements.
-/

section
-- leanmerge: from Solcore.Test.SyntaxArrayLiteralTraceExamples
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
end

section
-- leanmerge: from Solcore.Test.SyntaxArrayLiteralRejectionTraceExamples
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
end

section
-- leanmerge: from Solcore.Test.SyntaxDotConstructorRejectionTraceProperties
/-! Raw leading-dot rejection consumers. The nonempty example uses explicit
token carriers and actual checked-name expression children, not a general
expression parser or a canonical lexer claim. Parser decision is not used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDotConstructorRejectionTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Raw invocation needs no dispatcher guard: an absent dot produces its
complete uncommitted primitive failure without invoking any nested parser. -/
theorem unselected_missing_dot_rejects_without_child (nested : Parser Expr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .dot))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .symbol .dot, tail := [] }
      .expression input.declarativeRemainder failure.toDiagnostic) :
    dotConstructor nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .dot .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [dotConstructor, bind, result]

/-- Name rejection also bypasses every argument parser and propagates the
entire rejected state, rather than committing or rewriting the name report. -/
theorem name_rejection_bypasses_all_arguments (nested : Parser Expr)
    {input afterDot rejected : State} {dot : Token} {failure : Failure}
    (dotResult : symbol .dot .expression input = .ok dot afterDot)
    (nameResult : expressionName afterDot = .reject failure rejected) :
    dotConstructor nested input = .reject failure rejected := by
  simp only [dotConstructor, bind, dotResult, nameResult]

/-- The optional wrapper neither recovers nor changes any field of a selected
argument-list failure state, even when the nested parser has changed that state. -/
theorem optional_arguments_keep_whole_failure_state (nested : Parser Expr)
    {input rejected : State} {failure : Failure} {openingSpan : SourceSpan}
    (selected : TokenAt input.tokens input.window.endIndex input.cursor {
      span := openingSpan, value := .symbol .leftParen })
    (result : delimitedNoTrailing .leftParen .rightParen true nested .expression .expression input =
      .reject failure rejected) : optionalDotConstructorArguments nested input = .reject failure rejected := by
  have guard := DelimitedTraceInternals.symbol_present .leftParen (input := input)
    (after := { input.declarativeRemainder with cursor := input.cursor + 1 }) ⟨selected, rfl⟩
  exact optionalDotConstructorArguments_reject_iff_list.mpr ⟨guard, result⟩

theorem argument_rejection_keeps_whole_failure_state (nested : Parser Expr)
    {input afterDot afterName rejected : State} {dot : Token} {name : Identifier} {failure : Failure}
    (dotResult : symbol .dot .expression input = .ok dot afterDot)
    (nameResult : expressionName afterDot = .ok name afterName)
    (argumentsResult : optionalDotConstructorArguments nested afterName = .reject failure rejected) :
    dotConstructor nested input = .reject failure rejected := by
  simp only [dotConstructor, bind, dotResult, nameResult, argumentsResult]

private def source : SourceId := { origin := .main, path := "dot-rejection-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 1 4, value := "a-b" }
private def nameC : Identifier := { span := span 5 8, value := "c-d" }
private def nameToken (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := {
  span := name.span, kind := .invalidIdentifierHyphen name.value
}
private def tokens : Array Token := #[
  { span := span 0 1, value := .symbol .dot }, nameToken nameA,
  { span := span 4 5, value := .symbol .leftParen }, nameToken nameC,
  { span := span 8 9, value := .symbol .comma },
  { span := span 9 10, value := .symbol .plus },
  { span := span 10 11, value := .symbol .rightParen },
  { span := span 12 16, value := .identifier "tail" }]
private def rem (cursor : Nat) : Remainder := { tokens, endIndex := 8, cursor }
private def initial (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := ".a-b(c-d,+) tail" }, tokens, cursor := 0
  window := { endIndex := 8, endByte := 16 }, diagnosticsRev := prior.reverse
}
private def plusFailure : Failure := {
  span := span 9 10, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

private theorem name_trace {input : Remainder} (name : Identifier)
    (token : TokenAt input.tokens input.endIndex input.cursor (nameToken name))
    (spelling : IdentifierHyphenSpelling name.value) :
    ExpressionNameTraceParses source 16 input name { input with cursor := input.cursor + 1 } [hyphen name] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨otherSpan, other⟩ <;>
      have impossible := token.token_unique other <;> cases impossible
  exact .identifier absent (.parsed ⟨token, rfl, rfl, rfl⟩ (.hyphen spelling))

private theorem argumentsRejected : OptionalDotConstructorArgumentsTraceRejects
    IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16 (rem 2)
      (rem 5) plusFailure.toDiagnostic [hyphen nameC] := by
  have tail : NoTrailingDelimitedTailTraceRejects .rightParen .expression IdentifierExpressionTraceParses
      IdentifierExpressionTraceRejects source 16 (rem 4) (rem 5) plusFailure.toDiagnostic [] :=
    .elementRejected (span 8 9) (afterComma := rem 5) ⟨⟨by decide, rfl⟩, rfl⟩
      ⟨by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, rem, tokens],
        .absent (by simp [IdentifierAbsentAt, TokenAt, rem, tokens]),
        .reported (.token (current := { span := span 9 10, value := .symbol .plus }) ⟨by decide, rfl⟩), rfl⟩
  have listRejected : NoTrailingDelimitedListTraceRejects .leftParen .rightParen true .expression
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects source 16 (rem 2) (rem 5)
      plusFailure.toDiagnostic [hyphen nameC] :=
    .tailRejected (span 4 5) (afterOpening := rem 3) (afterFirst := rem 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.absent (by simp [TokenKindAbsentAt, TokenAt, rem, tokens, nameToken]))
      (.parsed (name_trace (input := rem 3) nameC ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameC; decide)))
      (by decide) tail
  exact .present (span 4 5) ⟨by decide, rfl⟩ listRejected

/-- Constructor-name events come before successful argument-name events;
the rejecting next argument supplies its full report without committing it. -/
theorem name_and_argument_events_precede_uncommitted_failure (prior : List ParseDiagnostic) :
    ∃ output, dotConstructor identifierExpression (initial prior) = .reject plusFailure output ∧
      output.declarativeRemainder = rem 5 ∧ output.diagnostics = prior ++ [hyphen nameA, hyphen nameC] := by
  have rejected : DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source 16 (rem 0) (rem 5) plusFailure.toDiagnostic [hyphen nameA, hyphen nameC] :=
    .argumentsRejected (span 0 1) (afterDot := rem 1) (afterName := rem 2)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (name_trace (input := rem 1) nameA ⟨by decide, rfl⟩ (by unfold IdentifierHyphenSpelling nameA; decide))
      argumentsRejected
  simpa only [initial, State.diagnostics, List.reverse_reverse] using
    (dotConstructor_trace_reject_failure_iff identifierExpression_trace_success_sound
      identifierExpression_trace_reject_sound identifierExpression_trace_success_complete
      identifierExpression_trace_reject_complete identifierExpression_success_context (input := initial prior)).mp rejected

end Solcore.Test.SyntaxDotConstructorRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxDotConstructorSuccessTraceProperties
/-! Concrete wrappers with arbitrary prior diagnostics: absent/empty argument
branches bypass any child, and real checked-name arguments retain exact order. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxDotConstructorSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @DotConstructorTraceParses.ordinary
example := @DotConstructorTraceParses.result_unique
example := @dotConstructor_trace_success_iff

theorem missing_parenthesis_keeps_entire_state (nested : Parser Expr) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen)) :
    optionalDotConstructorArguments nested input = .ok none input :=
  optionalDotConstructorArguments_eq_none_of_absent nested absent

/-- No-argument constructors need no child contract, and use the name's span as endpoint. -/
theorem no_arguments_bypasses_any_child (nested : Parser Expr)
    {input : State} {dotSpan : SourceSpan} {name : Identifier} {afterDot afterName : Remainder}
    {nameEvents : List ParseDiagnostic}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (nameParsed : ExpressionNameTraceParses input.file.id input.window.endByte
      afterDot name afterName nameEvents)
    (absent : TokenKindAbsentAt afterName.tokens afterName.endIndex afterName.cursor (.symbol .leftParen)) :
    dotConstructor nested input = .ok {
      span := SourceSpan.cover dotSpan name.span
      value := .dotConstructor dotSpan name none } { input with
        cursor := input.cursor + 2
        diagnosticsRev := nameEvents.reverse ++ input.diagnosticsRev } := by
  have dotResult := symbol_eq_ok_of_exactTokenParses .dot .expression dot
  rcases dot with ⟨_, rfl⟩
  have nameResult := expressionName_eq_ok_of_trace
    (input := { input with cursor := input.cursor + 1 }) nameParsed
  have absentNext : TokenKindAbsentAt input.tokens input.window.endIndex
      (input.cursor + 2) (.symbol .leftParen) := by
    simpa only [nameParsed.output_eq, State.declarativeRemainder] using absent
  have argsResult := optionalDotConstructorArguments_eq_none_of_absent nested
    (input := { input with
      cursor := input.cursor + 2
      diagnosticsRev := nameEvents.reverse ++ input.diagnosticsRev }) absentNext
  exact dotConstructor_success_iff_components.mpr
    ⟨_, _, name, _, none, dotResult, nameResult, argsResult, rfl⟩

/-- Boolean-first names remain identifier-shaped in the constructor AST and emit nothing. -/
theorem boolean_constructor_without_arguments_is_silent (nested : Parser Expr)
    {input : State} {dotSpan nameSpan : SourceSpan} {afterDot afterName : Remainder}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (name : ExactTokenParses (.keyword .trueKw) afterDot nameSpan afterName)
    (absent : TokenKindAbsentAt afterName.tokens afterName.endIndex afterName.cursor (.symbol .leftParen)) :
    dotConstructor nested input = .ok {
      span := SourceSpan.cover dotSpan nameSpan
      value := .dotConstructor dotSpan { span := nameSpan, value := "true" } none }
      { input with cursor := input.cursor + 2 } := by
  have parsed : ExpressionNameTraceParses input.file.id input.window.endByte afterDot
      { span := nameSpan, value := "true" } afterName [] := by
    rcases name with ⟨token, rfl⟩
    exact .boolean ⟨.trueKeyword token, rfl⟩
  simpa only [List.reverse_nil, List.nil_append] using
    no_arguments_bypasses_any_child nested dot parsed absent

/-- Empty written parentheses are some empty list, never the absent-argument case. -/
theorem empty_arguments_bypasses_any_child (nested : Parser Expr)
    {input : State} {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (opening : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan after) :
    optionalDotConstructorArguments nested input = .ok
      (some { span := SourceSpan.cover openingSpan closingSpan, elements := [] })
      { input with cursor := input.cursor + 2 } := by
  rw [optionalDotConstructorArguments_eq_of_present nested opening.1]
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have closingPresent := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [delimitedNoTrailing, delimitedWithPolicy, openingResult, Bool.true_and,
    closingPresent, if_true, closeDelimited, closingResult, List.reverse_nil]

private theorem checked_name_trace {source : SourceId} {endByte : Nat}
    {input output : Remainder} {name : Identifier}
    (parsed : IdentifierParses input name output) (hyphen : IdentifierHyphenSpelling name.value) :
    ExpressionNameTraceParses source endByte input name output
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have absent : BooleanPatternAbsentAt input := by
    constructor <;> rintro ⟨span, keyword⟩ <;>
      have tokenEq := parsed.1.token_unique keyword <;> cases tokenEq
  exact .identifier absent (.parsed parsed (.hyphen hyphen))

/-- Real constructor/name arguments contribute three separate events. The
outer dot, name, and written-parenthesis spans remain separately observable. -/
theorem checked_constructor_and_arguments_keep_event_order
    {input : State} {dotSpan openingSpan commaSpan closingSpan : SourceSpan}
    {name first second : Identifier}
    {afterDot afterName afterOpening afterFirst afterComma afterSecond after : Remainder}
    (dot : ExactTokenParses (.symbol .dot) input.declarativeRemainder dotSpan afterDot)
    (nameParsed : IdentifierParses afterDot name afterName)
    (nameHyphen : IdentifierHyphenSpelling name.value)
    (opening : ExactTokenParses (.symbol .leftParen) afterName openingSpan afterOpening)
    (firstParsed : IdentifierParses afterOpening first afterFirst)
    (firstHyphen : IdentifierHyphenSpelling first.value)
    (comma : ExactTokenParses (.symbol .comma) afterFirst commaSpan afterComma)
    (secondParsed : IdentifierParses afterComma second afterSecond)
    (secondHyphen : IdentifierHyphenSpelling second.value)
    (closing : ExactTokenParses (.symbol .rightParen) afterSecond closingSpan after) :
    ∃ output, dotConstructor identifierExpression input = .ok {
        span := SourceSpan.cover dotSpan (SourceSpan.cover openingSpan closingSpan)
        value := .dotConstructor dotSpan name (some {
          span := SourceSpan.cover openingSpan closingSpan
          elements := [{ span := first.span, value := .identifier first },
            { span := second.span, value := .identifier second }] }) } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ [
        { span := name.span, kind := .invalidIdentifierHyphen name.value },
        { span := first.span, kind := .invalidIdentifierHyphen first.value },
        { span := second.span, kind := .invalidIdentifierHyphen second.value }] := by
  have firstAbsent : TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex
      afterOpening.cursor (.symbol .rightParen) := by
    rintro ⟨span, token⟩; have impossible := firstParsed.1.token_unique token; cases impossible
  have commaAbsent : TokenKindAbsentAt afterSecond.tokens afterSecond.endIndex
      afterSecond.cursor (.symbol .comma) := by
    rintro ⟨span, token⟩; have impossible := closing.1.token_unique token; cases impossible
  apply dotConstructor_trace_success_complete identifierExpression_trace_success_complete
    identifierExpression_success_context
  exact .parsed dotSpan dot (checked_name_trace nameParsed nameHyphen) (.present
    (.nonempty openingSpan closingSpan opening (.absent firstAbsent)
      (IdentifierExpressionTraceParses.parsed (checked_name_trace firstParsed firstHyphen))
      (by rw [firstParsed.2.2.2]; exact Nat.lt_succ_self _)
      (.next commaSpan comma (IdentifierExpressionTraceParses.parsed (checked_name_trace secondParsed secondHyphen))
        (by rw [secondParsed.2.2.2]; exact Nat.lt_succ_self _) (.close commaAbsent closing))))

theorem checked_constructor_filter_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr} {trace : List ParseDiagnostic}
    (parsed : DotConstructorTraceParses IdentifierExpressionTraceParses source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun child => child.cascadeFilters _ _))

end Solcore.Test.SyntaxDotConstructorSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomDispatchTraceProperties
/-! Concrete ordered atom selections, independent of recursive expression or
block outcomes. Only the currently visible token participates in these guards. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomDispatchTraceInternals
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "expression-atom-selection.sol" }
private def span : SourceSpan := { source, startByte := 2, endByte := 9 }
private def token (value : TokenKind) : Token := { span, value }
private def remainder (kinds : List TokenKind) (endIndex cursor : Nat) : Remainder :=
  { tokens := (kinds.map token).toArray, endIndex, cursor }
private def state (kinds : List TokenKind) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (kinds.map token).toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def sampleKind : ExpressionAtomDispatchBranch → TokenKind
  | .literal => .decimalLiteral "7"
  | .name => .identifier "a-b"
  | .dotConstructor => .symbol .dot
  | .proxy => .symbol .at
  | .parenthesized => .symbol .leftParen
  | .array => .symbol .leftBracket
  | .lambda => .keyword .lamKw
  | .final => .symbol .plus

/-- Every branch is witnessed directly by token premises, not parser evaluation. -/
theorem all_eight_independent_selections (branch : ExpressionAtomDispatchBranch) :
    ExpressionAtomDispatchSelects (remainder [sampleKind branch] 1 0) branch := by
  cases branch <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
      remainder, sampleKind, token]

theorem boolean_keywords_and_written_identifiers_are_names :
    ExpressionAtomDispatchSelects (remainder [.keyword .trueKw] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .falseKw] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "true"] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "false"] 1 0) .name ∧
    token (.keyword .trueKw) ≠ token (.identifier "true") ∧
    token (.keyword .falseKw) ≠ token (.identifier "false") := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide⟩ <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenAt, remainder, token]

theorem hexadecimal_and_string_select_literals :
    ExpressionAtomDispatchSelects (remainder [.hexadecimalLiteral "0xff"] 1 0) .literal ∧
    ExpressionAtomDispatchSelects (remainder [.stringLiteral "true"] 1 0) .literal := by
  constructor <;> constructor <;> simp [CoreLiteralStartsAt, TokenAt, remainder, token]

theorem lambda_keyword_and_written_identifier_are_distinct :
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 1 0) .lambda ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "lam"] 1 0) .name := by
  refine ⟨all_eight_independent_selections .lambda, ?_⟩
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenAt, remainder, token]

/-- Backing presence is insufficient outside the numeric window. Numeric
membership is also insufficient when no backing token exists. -/
theorem invisible_tokens_select_final :
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 0 0) .final ∧
    ExpressionAtomDispatchSelects (remainder [] 7 0) .final ∧
    ExpressionAtomDispatchSelects (remainder [.decimalLiteral "7"] 1 4) .final ∧
    (remainder [.keyword .lamKw] 0 0).tokens[0]? = some (token (.keyword .lamKw)) ∧
    (remainder [] 7 0).cursor < (remainder [] 7 0).endIndex ∧
    (remainder [.decimalLiteral "7"] 1 4).endIndex <
      (remainder [.decimalLiteral "7"] 1 4).cursor := by
  refine ⟨?_, ?_, ?_, rfl, by decide, by decide⟩ <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, remainder]

theorem same_carrier_window_changes_selection :
    (remainder [.keyword .lamKw] 1 0).tokens = (remainder [.keyword .lamKw] 0 0).tokens ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 1 0) .lambda ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 0 0) .final :=
  ⟨rfl, all_eight_independent_selections .lambda, invisible_tokens_select_final.1⟩

/-- Equal observations transport the chosen branch even with different
carriers, numeric positions, and unobserved suffixes. -/
theorem shifted_current_token_keeps_selection (branch : ExpressionAtomDispatchBranch) :
    ExpressionAtomDispatchSelects
      (remainder [.symbol .plus, sampleKind branch, .keyword .lamKw] 2 1) branch := by
  apply (ExpressionAtomDispatchSelects.congr_of_tokenAt
    (left := remainder [sampleKind branch] 1 0) (right := remainder
      [.symbol .plus, sampleKind branch, .keyword .lamKw] 2 1) (branch := branch) ?_).mp
      (all_eight_independent_selections branch)
  intro current
  simp [TokenAt, remainder]

/-- Every direct witness determines the real guard and its complete raw Reply,
without a success, rejection, frame, or ordinary contract for either child. -/
theorem all_eight_raw_replies (nested : Parser Expr) (block : Parser Block)
    (branch : ExpressionAtomDispatchBranch) (prior : List ParseDiagnostic) :
    selectedBranch (state [sampleKind branch] 1 0 prior) = branch ∧
    expressionAtomCore nested block (state [sampleKind branch] 1 0 prior) =
      rawParser nested block branch (state [sampleKind branch] 1 0 prior) :=
  ⟨selectedBranch_eq_iff.mpr (all_eight_independent_selections branch),
    expressionAtomCore_eq_raw_of_selection nested block (all_eight_independent_selections branch)⟩

theorem boolean_names_run_identifier_expression (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.keyword .trueKw] 1 0 prior) =
      identifierExpression (state [.keyword .trueKw] 1 0 prior) ∧
    expressionAtomCore nested block (state [.keyword .falseKw] 1 0 prior) =
      identifierExpression (state [.keyword .falseKw] 1 0 prior) ∧
    expressionAtomCore nested block (state [.identifier "true"] 1 0 prior) =
      identifierExpression (state [.identifier "true"] 1 0 prior) ∧
    expressionAtomCore nested block (state [.identifier "false"] 1 0 prior) =
      identifierExpression (state [.identifier "false"] 1 0 prior) :=
  ⟨expressionAtomCore_eq_raw_of_selection nested block (input := state [.keyword .trueKw] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.keyword .falseKw] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.identifier "true"] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.2.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.identifier "false"] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.2.2.1⟩

/-- A non-lambda atom never invokes the supplied block parser. -/
theorem unselected_block_cannot_change_reply (nested : Parser Expr) (left right : Parser Block)
    {input : State} {branch : ExpressionAtomDispatchBranch}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder branch)
    (notLambda : branch ≠ .lambda) :
    expressionAtomCore nested left input = expressionAtomCore nested right input := by
  rw [expressionAtomCore_eq_raw_of_selection nested left selected,
    expressionAtomCore_eq_raw_of_selection nested right selected]
  cases branch <;> first | rfl | exact False.elim (notLambda rfl)

/-- A selected lambda invokes the supplied block, but not the atom's separate
recursive expression argument. The statement preserves even invariant Replies. -/
theorem lambda_selection_ignores_nested (left right : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore left block (state [.keyword .lamKw] 1 0 prior) =
      expressionAtomCore right block (state [.keyword .lamKw] 1 0 prior) := by
  rw [expressionAtomCore_eq_raw_of_selection left block (input := state [.keyword .lamKw] 1 0 prior)
      (all_eight_independent_selections .lambda),
    expressionAtomCore_eq_raw_of_selection right block (input := state [.keyword .lamKw] 1 0 prior)
      (all_eight_independent_selections .lambda)]
  rfl

theorem leaf_selection_ignores_both_children (nestedLeft nestedRight : Parser Expr)
    (blockLeft blockRight : Parser Block) {input : State} {branch : ExpressionAtomDispatchBranch}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder branch)
    (leaf : branch ∈ [.literal, .name, .proxy, .final]) :
    expressionAtomCore nestedLeft blockLeft input = expressionAtomCore nestedRight blockRight input := by
  rw [expressionAtomCore_eq_raw_of_selection nestedLeft blockLeft selected,
    expressionAtomCore_eq_raw_of_selection nestedRight blockRight selected]
  cases branch <;> first | rfl | simp at leaf

theorem final_selection_keeps_full_state (nested : Parser Expr) (block : Parser Block) {input : State}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder .final) :
    expressionAtomCore nested block input = .reject {
      span := input.currentSpan, found := input.peekKind?
      expected := { head := .expression, tail := [] }, context := .expression
    } input := by
  rw [expressionAtomCore_eq_raw_of_selection nested block selected]
  rfl

private def eofFailure : Failure := {
  span := { source, startByte := 99, endByte := 99 }, found := none
  expected := { head := .expression, tail := [] }, context := .expression
}

theorem invisible_tokens_preserve_final_reply (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.keyword .lamKw] 0 0 prior) =
      .reject eofFailure (state [.keyword .lamKw] 0 0 prior) ∧
    expressionAtomCore nested block (state [] 7 0 prior) = .reject eofFailure (state [] 7 0 prior) ∧
    expressionAtomCore nested block (state [.decimalLiteral "7"] 1 4 prior) =
      .reject eofFailure (state [.decimalLiteral "7"] 1 4 prior) :=
  ⟨final_selection_keeps_full_state nested block invisible_tokens_select_final.1,
    final_selection_keeps_full_state nested block invisible_tokens_select_final.2.1,
    final_selection_keeps_full_state nested block invisible_tokens_select_final.2.2.1⟩

theorem unexpected_token_report_is_not_committed (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.symbol .plus] 1 0 prior) = .reject {
      span, found := some (.symbol .plus)
      expected := { head := .expression, tail := [] }, context := .expression
    } (state [.symbol .plus] 1 0 prior) ∧
    (state [.symbol .plus] 1 0 prior).diagnostics = prior := by
  refine ⟨final_selection_keeps_full_state nested block (all_eight_independent_selections .final), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

theorem prior_diagnostics_do_not_select_branches (kinds : List TokenKind) (endIndex cursor : Nat)
    (left right : List ParseDiagnostic) :
    selectedBranch (state kinds endIndex cursor left) = selectedBranch (state kinds endIndex cursor right) :=
  selectedBranch_eq_of_remainder_eq rfl

end Solcore.Test.SyntaxExpressionAtomDispatchTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomNumericWindowProperties
/-! Both supplied children satisfy every three-field fuel contract, but a
rejected child can enlarge endIndex. Public atom recovery then succeeds with
that changed numeric window. The independent trace reconstructs the whole
reply without source-content validity or a rejected full-window frame. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomNumericWindowProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-numeric-window.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def tokens : Array Token := #[token 0 1 .leftParen, token 1 2 .plus, token 2 3 .semicolon]
private def before : Remainder := { tokens, cursor := 0, endIndex := 3 }
private def failed : Remainder := { before with cursor := 1, endIndex := 4 }
private def after : Remainder := { before with cursor := 2, endIndex := 4 }
private def input (text : String) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := text }, tokens, cursor := 0
  window := { endIndex := 3, endByte := 3 }, diagnosticsRev := prior.reverse
}
private def failure : Failure := {
  span := span 1 2, found := some (.symbol .plus)
  expected := { head := .expression, tail := [] }, context := .expression
}
private def errorValue : Expr := { span := span 0 2, value := .error }
private def recoveryEvent : ParseDiagnostic := expressionAtomRecoveryTraceEvent errorValue.span
private def rejectedRemainder (enlarge : Bool) (state : Remainder) : Remainder := {
  state with endIndex := if enlarge then 4 else state.endIndex
}
private def rejectedState (enlarge : Bool) (state : State) : State := {
  state with window := { state.window with endIndex := if enlarge then 4 else state.window.endIndex }
}
private def rejecting {α : Type} (enlarge : Bool) : Parser α := fun state =>
  .reject failure (rejectedState enlarge state)
private abbrev nested : Parser Expr := rejecting true
private abbrev block : Parser Block := rejecting false
private def neverSuccess {α : Type} (_source : SourceId) (_endByte : Nat) (_input : Remainder)
    (_value : α) (_after : Remainder) (_trace : List ParseDiagnostic) : Prop := False
private def childRejects (enlarge : Bool) (_source : SourceId) (_endByte : Nat)
    (state after : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  after = rejectedRemainder enlarge state ∧ report = failure.toDiagnostic ∧ trace = []
private abbrev coreParses := ExpressionAtomDispatchTraceParses
  (neverSuccess (α := Expr)) (neverSuccess (α := Block))
private abbrev coreRejects := ExpressionAtomDispatchTraceRejects
  (neverSuccess (α := Expr)) (childRejects true) (childRejects false)
private def recovered (text : String) (prior : List ParseDiagnostic) : State := {
  input text prior with
  cursor := 2
  window := { endIndex := 4, endByte := 3 }
  diagnosticsRev := recoveryEvent :: failure.toDiagnostic :: prior.reverse
}

private theorem rejecting_success_sound {α : Type} (enlarge : Bool) :
    ParserTraceSuccessSound (rejecting (α := α) enlarge) neverSuccess := by
  intro state output value result
  cases result
private theorem rejecting_success_complete {α : Type} (enlarge : Bool) :
    ParserTraceSuccessComplete (rejecting (α := α) enlarge) neverSuccess := by
  intro state value after trace impossible
  exact False.elim impossible
private theorem rejecting_success_context {α : Type} (enlarge : Bool) :
    ParserSuccessContext (rejecting (α := α) enlarge) := by
  intro state output value result
  cases result
private theorem rejecting_reject_sound {α : Type} (enlarge : Bool) :
    ParserTraceRejectSound (rejecting (α := α) enlarge) (childRejects enlarge) := by
  intro state output actual result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm⟩
private theorem rejecting_reject_complete {α : Type} (enlarge : Bool) :
    ParserTraceRejectComplete (rejecting (α := α) enlarge) (childRejects enlarge) := by
  rintro state after report trace ⟨rfl, rfl, rfl⟩
  exact ⟨failure, rejectedState enlarge state, rfl, rfl, rfl, (List.append_nil _).symm⟩
private theorem rejecting_reject_frame {α : Type} (enlarge : Bool)
    {state output : State} {actual : Failure} (result : rejecting (α := α) enlarge state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  cases result
  exact ⟨rfl, rfl⟩
private theorem rejecting_contract {α : Type} (enlarge : Bool) (fuel : Nat) :
    UnrestrictedFuelElementContract (rejecting (α := α) enlarge) fuel where
  endIndexOnSuccess result := by cases result
  cursorLtOnSuccess result := by cases result
  ordinary _ _ := .inr ⟨_, _, rfl⟩

private theorem core_success_sound : ParserTraceSuccessSound (expressionAtomCore nested block) coreParses :=
  expressionAtomCore_trace_success_sound (rejecting_success_sound true) (rejecting_success_context true)
    (rejecting_success_sound false)
private theorem core_success_complete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreParses :=
  expressionAtomCore_trace_success_complete (rejecting_success_complete true) (rejecting_success_context true)
    (rejecting_success_complete false)
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects :=
  expressionAtomCore_reject_trace_sound (rejecting_success_sound true) (rejecting_reject_sound true)
    (rejecting_success_context true) (rejecting_reject_sound false)
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects :=
  expressionAtomCore_trace_reject_complete (rejecting_success_complete true) (rejecting_reject_complete true)
    (rejecting_success_context true) (rejecting_reject_complete false)
private theorem core_success_frame {state output : State} {value : Expr}
    (result : expressionAtomCore nested block state = .ok value output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  have frame := expressionAtomCore_trace_success_context (rejecting_success_context true)
    (rejecting_success_context false) result
  exact ⟨frame.1, congrArg TokenWindow.endByte frame.2⟩
private theorem core_reject_frame {state output : State} {actual : Failure}
    (result : expressionAtomCore nested block state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte :=
  expressionAtomCore_reject_source_endByte (rejecting_success_context true)
    (rejecting_reject_frame true) (rejecting_reject_frame false) result

theorem children_have_every_fuel_contract (fuel : Nat) :
    UnrestrictedFuelElementContract nested fuel ∧ UnrestrictedFuelElementContract block fuel :=
  ⟨rejecting_contract true fuel, rejecting_contract false fuel⟩

theorem nested_changes_only_rejected_endIndex {state output : State} {actual : Failure}
    (result : nested state = .reject actual output) :
    output.file = state.file ∧ output.tokens = state.tokens ∧ output.cursor = state.cursor ∧
    output.window.endByte = state.window.endByte ∧ output.diagnostics = state.diagnostics ∧
    output.window.endIndex = 4 := by
  cases result
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem selected : ExpressionAtomDispatchSelects before .parenthesized := by
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, before, tokens, token]

theorem independent_core_rejection : coreRejects source 3 before failed failure.toDiagnostic [] :=
  .selected .parenthesized selected
    (.firstRejected (span 0 1) ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, before, tokens, token]) ⟨rfl, rfl, rfl⟩)

private theorem rewind_continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind before failed) := by
  intro stops
  cases stops <;> simp_all [TokenAt, expressionAtomTraceRewind, before, failed, tokens, token]

private theorem plus_continues :
    ¬ ExpressionAtomRecoveryStops { before with cursor := 1, endIndex := 4 } { before with cursor := 1, endIndex := 4 } := by
  intro stops
  cases stops <;> simp_all [TokenAt, before, tokens, token]

private theorem independent_recovery : ExpressionAtomRecoveryTraceParses source 3
    (expressionAtomTraceRewind before failed) errorValue after [recoveryEvent] := by
  refine ⟨.recovered (token := token 0 1 .leftParen) ⟨by change 0 < 4; decide, rfl⟩
    (.next (token := token 1 2 .plus) plus_continues ⟨by change 1 < 4; decide, rfl⟩
      (.stop (.semicolon ⟨by change 2 < 4; decide, rfl⟩))), rfl⟩

theorem independent_public_recovery : ExpressionAtomTraceParses coreParses coreRejects source 3
    before errorValue after [failure.toDiagnostic, recoveryEvent] :=
  .recovered independent_core_rejection rewind_continues independent_recovery

/-- Reverse correspondence, not only direct evaluation, reconstructs the
changed numeric window and every incoming diagnostic exactly. -/
theorem public_reply_from_independent_trace (text : String) (prior : List ParseDiagnostic) :
    expressionAtom nested block (input text prior) = .ok errorValue (recovered text prior) :=
  (expressionAtom_trace_success_state_iff core_success_sound core_reject_sound core_success_complete
    core_reject_complete core_success_frame core_reject_frame (input := input text prior)).mp independent_public_recovery

theorem public_recovery_retains_failed_numeric_window (text : String) (prior : List ParseDiagnostic) :
    (recovered text prior).file = (input text prior).file ∧
    (recovered text prior).tokens = (input text prior).tokens ∧
    (recovered text prior).window.endByte = (input text prior).window.endByte ∧
    (recovered text prior).cursor = 2 ∧ (recovered text prior).window.endIndex = 4 ∧
    (recovered text prior).diagnostics = prior ++ [failure.toDiagnostic, recoveryEvent] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [recovered, State.diagnostics, List.reverse_cons, List.reverse_reverse, List.append_assoc]
  rfl

theorem prior_reports_are_preserved_with_multiplicity (text : String) (prior : List ParseDiagnostic) :
    expressionAtom nested block (input text (prior ++ [failure.toDiagnostic])) =
      .ok errorValue (recovered text (prior ++ [failure.toDiagnostic])) ∧
    (recovered text (prior ++ [failure.toDiagnostic])).diagnostics =
      prior ++ [failure.toDiagnostic, failure.toDiagnostic, recoveryEvent] :=
  ⟨public_reply_from_independent_trace text _, by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (public_recovery_retains_failed_numeric_window text (prior ++ [failure.toDiagnostic])).2.2.2.2.2⟩

/-- Success-frame fields in the child contract are vacuous for always-rejecting
children; public recovery turns the unconstrained rejected endIndex into success. -/
theorem public_atom_has_no_unrestricted_fuel_contract (fuel : Nat) :
    ¬ UnrestrictedFuelElementContract (expressionAtom nested block) fuel := by
  intro contract
  have impossible := contract.endIndexOnSuccess (public_reply_from_independent_trace "" [])
  change 4 = 3 at impossible
  contradiction

theorem public_atom_has_no_full_window_success_context :
    ¬ ParserSuccessContext (expressionAtom nested block) := by
  intro contextFrame
  have impossible := congrArg TokenWindow.endIndex (contextFrame (public_reply_from_independent_trace "" [])).2
  change 4 = 3 at impossible
  contradiction

end Solcore.Test.SyntaxExpressionAtomNumericWindowProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomRecoveryTraceProperties
/-! Standalone recovery consumes its mandatory first token before testing a
boundary. Independent scans drive complete replies, including malformed token
windows; recovery events have conditional, not protected, cascade behavior. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomRecoveryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-recovery-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def skipped : Token := { span := span 1 4, value := .identifier "a-b" }
private def elseToken (startByte endByte : Nat) : Token := { span := span startByte endByte, value := .keyword .elseKw }
private def scanTokens : List Token := [symbol 0 1 .semicolon, skipped, elseToken 4 8, symbol 8 9 .plus]
private def semicolonTokens : List Token := [elseToken 0 4, symbol 4 5 .semicolon, symbol 5 6 .plus]
private def sparseTokens : List Token := [symbol 0 1 .plus]
private def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}
private def input (tokens : List Token) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def recovered (startByte endByte : Nat) : Expr := {
  span := span startByte endByte, value := .error
}
private def event (startByte endByte : Nat) : ParseDiagnostic := expressionAtomRecoveryTraceEvent (span startByte endByte)
private def final (tokens : List Token) (endIndex cursor : Nat) (diagnostic : ParseDiagnostic)
    (prior : List ParseDiagnostic) : State := {
  input tokens endIndex cursor prior with diagnosticsRev := diagnostic :: prior.reverse
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}

private theorem scan_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder scanTokens 4 0) (recovered 0 4) (remainder scanTokens 4 2) [event 0 4] := by
  have continues : ¬ ExpressionAtomRecoveryStops (remainder scanTokens 4 1) (remainder scanTokens 4 1) := by
    intro stops
    cases stops <;> simp_all [TokenAt, remainder, scanTokens, skipped]
  refine ⟨.recovered (token := symbol 0 1 .semicolon) ⟨by change 0 < 4; decide, rfl⟩ ?_, rfl⟩
  exact .next continues (token := skipped) ⟨by change 1 < 4; decide, rfl⟩
    (.stop (.elseKeyword ⟨by change 2 < 4; decide, rfl⟩))

private theorem semicolon_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder semicolonTokens 3 0) (recovered 0 4) (remainder semicolonTokens 3 1) [event 0 4] :=
  ⟨.recovered (token := elseToken 0 4) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.semicolon ⟨by change 1 < 3; decide, rfl⟩)), rfl⟩

/-- Initial semicolon is consumed, the intervening hyphen identifier is skipped
without checking it, and the later else keyword is left unread. -/
theorem mandatory_semicolon_then_else_stop (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 4 0 prior) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) prior) ∧
    (final scanTokens 4 2 (event 0 4) prior).diagnostics = prior ++ [event 0 4] ∧
    (final scanTokens 4 2 (event 0 4) prior).peek? = some (elseToken 4 8) := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input scanTokens 4 0 prior)).mp scan_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Even an initial else keyword is consumed; only the following semicolon
is a scan stop. -/
theorem mandatory_else_then_semicolon_stop (prior : List ParseDiagnostic) :
    recoverAtom (input semicolonTokens 3 0 prior) = .ok (recovered 0 4)
      (final semicolonTokens 3 1 (event 0 4) prior) ∧
    (final semicolonTokens 3 1 (event 0 4) prior).peek? = some (symbol 4 5 .semicolon) :=
  ⟨(recoverAtom_trace_success_state_iff (input := input semicolonTokens 3 0 prior)).mp semicolon_trace, rfl⟩

private theorem sparse_trace : ExpressionAtomRecoveryTraceParses source 99
    (remainder sparseTokens 3 0) (recovered 0 1) (remainder sparseTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .plus) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.missingToken (by change 1 < 3; decide) rfl)), rfl⟩

private theorem sparse_rejection : ExpressionAtomRecoveryTraceRejects source 99
    (remainder sparseTokens 3 1) (remainder sparseTokens 3 1) missingFailure.toDiagnostic [] :=
  ⟨.missingToken (by change 1 < 3; decide) rfl,
    .reported (.missingToken (by change 1 < 3; decide) rfl), rfl⟩

/-- Missing backing inside the numeric window ends an established scan, but
rejects if recovery has not yet obtained its mandatory first token. -/
theorem missing_backing_stop_versus_initial_rejection (prior : List ParseDiagnostic) :
    recoverAtom (input sparseTokens 3 0 prior) = .ok (recovered 0 1)
      (final sparseTokens 3 1 (event 0 1) prior) ∧
    recoverAtom (input sparseTokens 3 1 prior) = .reject missingFailure (input sparseTokens 3 1 prior) ∧
    (input sparseTokens 3 1 prior).cursor < (input sparseTokens 3 1 prior).window.endIndex ∧
    (input sparseTokens 3 1 prior).peek? = none ∧
    (input sparseTokens 3 1 prior).diagnostics = prior := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input sparseTokens 3 0 prior)).mp sparse_trace,
    (recoverAtom_trace_reject_failure_state_iff (input := input sparseTokens 3 1 prior)).mp sparse_rejection,
    by change 1 < 3; decide, rfl, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- A window end likewise rejects without consuming a hidden backing token. -/
theorem hidden_first_token_rejects_unchanged (prior : List ParseDiagnostic) :
    (input sparseTokens 0 0 prior).tokens[0]? = some (symbol 0 1 .plus) ∧
    recoverAtom (input sparseTokens 0 0 prior) = .reject missingFailure (input sparseTokens 0 0 prior) := by
  refine ⟨rfl, (recoverAtom_trace_reject_failure_state_iff (input := input sparseTokens 0 0 prior)
    (after := remainder sparseTokens 0 0) (failure := missingFailure) (trace := [])).mp ?_⟩
  exact ⟨.windowEnd (by change 0 ≤ 0; decide), .reported (.windowEnd (by change 0 ≤ 0; decide)), rfl⟩

/-- After the mandatory token, an active window end stops before a still-backed
identifier. Its hidden spelling is neither consumed nor checked. -/
theorem active_window_hides_next_token (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 1 0 prior) = .ok (recovered 0 1)
      (final scanTokens 1 1 (event 0 1) prior) ∧
    (final scanTokens 1 1 (event 0 1) prior).tokens[1]? = some skipped ∧
    (final scanTokens 1 1 (event 0 1) prior).peek? = none := by
  refine ⟨(recoverAtom_trace_success_state_iff (input := input scanTokens 1 0 prior)
    (value := recovered 0 1) (after := remainder scanTokens 1 1) (trace := [event 0 1])).mp ?_, rfl, rfl⟩
  exact ⟨.recovered (token := symbol 0 1 .semicolon) ⟨by change 0 < 1; decide, rfl⟩
    (.stop (.windowEnd (by change 1 ≤ 1; decide))), rfl⟩

/-- Standalone recovery appends only its own event to an already committed
original failure. The original complete report is neither replayed nor removed. -/
theorem committed_failure_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    recoverAtom (input scanTokens 4 0 (prior ++ [original.toDiagnostic])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])).diagnostics =
      prior ++ [original.toDiagnostic, event 0 4] := by
  have result := mandatory_semicolon_then_else_stop (prior ++ [original.toDiagnostic])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

theorem duplicate_prior_events_are_not_deduplicated (prior : List ParseDiagnostic) :
    recoverAtom (input scanTokens 4 0 (prior ++ [event 0 4, event 0 4])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [event 0 4, event 0 4])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [event 0 4, event 0 4])).diagnostics =
      prior ++ [event 0 4, event 0 4, event 0 4] := by
  have result := mandatory_semicolon_then_else_stop (prior ++ [event 0 4, event 0 4])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

theorem recovery_event_kept_when_not_suppressed (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [event 0 4] :=
  scan_trace.cascade_kept text lexical retained

theorem recovery_event_dropped_when_suppressed (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [] :=
  scan_trace.cascade_dropped text lexical suppressed

/-- Concrete filtering shows why a recovery event cannot use an unconditional
protected-suffix theorem: a matching lexical range removes it. -/
theorem recovery_event_is_conditionally_filtered (text : String) :
    filterParseDiagnostics { id := source, content := text } [] [event 0 4] = [event 0 4] ∧
    filterParseDiagnostics { id := source, content := text }
      [{ span := span 0 4, kind := .invalidToken }] [event 0 4] = [] := by
  constructor
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_kept_when_not_suppressed text [] (by simp [LexicalCascadeSuppresses]))
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_dropped_when_suppressed text [span 0 4]
        ⟨span 0 4, by simp, ⟨rfl, .inl rfl⟩⟩)

end Solcore.Test.SyntaxExpressionAtomRecoveryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomRejectionContextProperties
/-! A synthetic rejected expression replaces both tokens and endIndex while
keeping its file/endByte. Actual parenthesized atom dispatch and public rewind
retain that failed carrier, so a new boundary replaces the original nonboundary.
The unused block deliberately returns an invariant; no child totality is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomRejectionContextProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-rejection-context.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (value : TokenKind) : Token := { span := span 0 1, value }
private def original : List Token := [token (.symbol .leftParen), token (.identifier "x")]
private def changed : List Token := [token (.symbol .semicolon)]
private def before : Remainder := { tokens := original.toArray, cursor := 0, endIndex := 2 }
private def failed : Remainder := { tokens := changed.toArray, cursor := 3, endIndex := 1 }
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := original.toArray, cursor := 0
  window := { endIndex := 2, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def event : ParseDiagnostic := { span := span 1 4, kind := .invalidIdentifierHyphen "a-b" }
private def failure : Failure := {
  span := span 1 4, found := some (.symbol .plus)
  expected := { head := .expression, tail := [] }, context := .expression
}
private def replaceOnReject (state : State) : State := {
  state with
  tokens := changed.toArray
  cursor := 3
  window := { endIndex := 1, endByte := state.window.endByte }
  diagnosticsRev := event :: state.diagnosticsRev
}
private def nested : Parser Expr := fun state => .reject failure (replaceOnReject state)
private def unusedBlock : Parser Block := fun state => .invariant (.fuelExhausted .expression state.currentSpan)
private def childSuccess (_ : SourceId) (_ : Nat) (_ : Remainder) (_ : Expr)
    (_ : Remainder) (_ : List ParseDiagnostic) : Prop := False
private def childRejects (_ : SourceId) (_ : Nat) (_ : Remainder) (after : Remainder)
    (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  after = failed ∧ report = failure.toDiagnostic ∧ trace = [event]
private def blockRejects (_ : SourceId) (_ : Nat) (_ _ : Remainder)
    (_ : ParseDiagnostic) (_ : List ParseDiagnostic) : Prop := False
private abbrev coreRejects := ExpressionAtomDispatchTraceRejects childSuccess childRejects blockRejects
private def rejectedState (prior : List ParseDiagnostic) : State := {
  input prior with
  tokens := changed.toArray
  cursor := 3
  window := { endIndex := 1, endByte := 99 }
  diagnosticsRev := event :: prior.reverse
}

private theorem nested_success_sound : ParserTraceSuccessSound nested childSuccess := by
  intro state output value result
  simp [nested] at result
private theorem nested_success_complete : ParserTraceSuccessComplete nested childSuccess := by
  intro state value after trace impossible
  exact False.elim impossible
private theorem nested_success_context : ParserSuccessContext nested := by
  intro state output value result
  simp [nested] at result
private theorem nested_reject_sound : ParserTraceRejectSound nested childRejects := by
  intro state output actual result
  change Reply.reject failure (replaceOnReject state) = Reply.reject actual output at result
  cases result
  refine ⟨[event], ⟨rfl, rfl, rfl⟩, ?_⟩
  simp only [replaceOnReject, State.diagnostics, List.reverse_cons]
private theorem nested_reject_complete : ParserTraceRejectComplete nested childRejects := by
  rintro state after report trace ⟨rfl, rfl, rfl⟩
  refine ⟨failure, replaceOnReject state, rfl, rfl, rfl, ?_⟩
  simp only [replaceOnReject, State.diagnostics, List.reverse_cons]
private theorem nested_reject_frame {state output : State} {actual : Failure}
    (result : nested state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  change Reply.reject failure (replaceOnReject state) = Reply.reject actual output at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_reject_sound : ParserTraceRejectSound unusedBlock blockRejects := by
  intro state output actual result
  simp [unusedBlock] at result
private theorem block_reject_complete : ParserTraceRejectComplete unusedBlock blockRejects := by
  intro state after report trace impossible
  exact False.elim impossible
private theorem block_reject_frame {state output : State} {actual : Failure}
    (result : unusedBlock state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  simp [unusedBlock] at result

private theorem core_reject_frame {state output : State} {actual : Failure}
    (result : expressionAtomCore nested unusedBlock state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte :=
  expressionAtomCore_reject_source_endByte nested_success_context nested_reject_frame block_reject_frame result
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore nested unusedBlock) coreRejects :=
  expressionAtomCore_reject_trace_sound nested_success_sound nested_reject_sound nested_success_context block_reject_sound
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore nested unusedBlock) coreRejects :=
  expressionAtomCore_trace_reject_complete nested_success_complete nested_reject_complete
    nested_success_context block_reject_complete

private theorem selected_parenthesis : ExpressionAtomDispatchSelects before .parenthesized := by
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, before, original, token]

theorem independent_core_rejection : coreRejects source 99 before failed failure.toDiagnostic [event] :=
  .selected .parenthesized selected_parenthesis
    (.firstRejected (span 0 1) ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, before, original, token]) ⟨rfl, rfl, rfl⟩)

/-- The same complete child Failure and event escape; only file/endByte are
framed. The independent remainder supplies every replaced state field. -/
theorem core_reply_from_independent_trace (prior : List ParseDiagnostic) :
    expressionAtomCore nested unusedBlock (input prior) = .reject failure (rejectedState prior) :=
  (expressionAtomCore_trace_reject_failure_state_iff nested_success_sound nested_reject_sound
    nested_success_complete nested_reject_complete nested_success_context block_reject_sound block_reject_complete
    core_reject_frame (input := input prior)).mp independent_core_rejection

theorem weak_frame_allows_new_carrier_and_endIndex (prior : List ParseDiagnostic) :
    (rejectedState prior).file = (input prior).file ∧
    (rejectedState prior).window.endByte = (input prior).window.endByte ∧
    (rejectedState prior).tokens ≠ (input prior).tokens ∧
    (rejectedState prior).window.endIndex ≠ (input prior).window.endIndex ∧
    (rejectedState prior).cursor = 3 := by
  have frame := core_reject_frame (core_reply_from_independent_trace prior)
  exact ⟨frame.1, frame.2, by change changed.toArray ≠ original.toArray; decide, by change 1 ≠ 2; decide, rfl⟩

theorem rewind_changes_boundary_observation :
    ¬ ExpressionAtomBoundaryStops before ∧
    ExpressionAtomBoundaryStops (expressionAtomTraceRewind before failed) ∧
    (expressionAtomTraceRewind before failed).tokens = failed.tokens ∧
    (expressionAtomTraceRewind before failed).endIndex = 1 ∧
    (expressionAtomTraceRewind before failed).cursor = before.cursor := by
  refine ⟨?_, .semicolon ⟨by change 0 < 1; decide, rfl⟩, rfl, rfl, rfl⟩
  intro stops
  cases stops <;> simp_all [TokenAt, before, original, token]

theorem independent_public_boundary_rejection :
    ExpressionAtomTraceRejects coreRejects source 99 before
      (expressionAtomTraceRewind before failed) failure.toDiagnostic [event] :=
  .boundary independent_core_rejection rewind_changes_boundary_observation.2.1

/-- Public recovery is bypassed using the changed carrier, not the original
opening parenthesis. The original report stays terminal and uncommitted. -/
theorem public_reply_keeps_failed_carrier (prior : List ParseDiagnostic) :
    expressionAtom nested unusedBlock (input prior) =
      .reject failure { rejectedState prior with cursor := 0 } ∧
    ({ rejectedState prior with cursor := 0 } : State).diagnostics = prior ++ [event] ∧
    isAtomBoundary (input prior) = false ∧
    isAtomBoundary { rejectedState prior with cursor := 0 } = true := by
  refine ⟨(expressionAtom_trace_reject_failure_state_iff core_reject_sound core_reject_complete
    core_reject_frame (input := input prior)).mp independent_public_boundary_rejection, ?_, rfl, rfl⟩
  simp only [rejectedState, State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem prior_duplicate_event_is_not_replayed (prior : List ParseDiagnostic) :
    expressionAtom nested unusedBlock (input (prior ++ [event])) =
      .reject failure { rejectedState (prior ++ [event]) with cursor := 0 } ∧
    ({ rejectedState (prior ++ [event]) with cursor := 0 } : State).diagnostics = prior ++ [event, event] := by
  have result := public_reply_keeps_failed_carrier (prior ++ [event])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

end Solcore.Test.SyntaxExpressionAtomRejectionContextProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomTotalityProperties
/-! The real literal leaf supplies the minimal progress contract at every
fuel. One atom layer then has ordinary outcomes on arbitrary numerical States;
this is not recursive expression or block trace closure. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTotalityProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

theorem literal_child_contract (fuel : Nat) :
    UnrestrictedFuelElementContract literalExpression fuel where
  endIndexOnSuccess result := by rw [literalExpression_success_state_shape result]
  cursorLtOnSuccess result := by
    rw [literalExpression_success_state_shape result]
    exact Nat.lt_succ_self _
  ordinary input _ := by
    rcases coreLiteral_ordinary input with ⟨literal, next, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨{ span := literal.span, value := .literal literal }, next,
        by simp only [literalExpression, bind, result, pure]⟩
    · exact .inr ⟨failure, rejected, by simp only [literalExpression, bind, result]⟩

private def source : SourceId := { origin := .main, path := "atom-unrestricted.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def fixedBlock : Block := { span := span 0 0, value := [] }
private def emptyBlock : Parser Block := pure fixedBlock
private theorem emptyBlock_ordinary : Parser.Ordinary emptyBlock := fun input => .inl ⟨fixedBlock, input, rfl⟩

private def OrdinaryAt {α : Type} (parser : Parser α) (input : State) : Prop :=
  (∃ value next, parser input = .ok value next) ∨
    (∃ failure next, parser input = .reject failure next)

/-- The child has no validity premise; the two loop bounds are still explicit. -/
theorem literal_tuple_tail_ordinary (nestedFuel loopFuel : Nat) (opening : Token)
    (elementsRev : List Expr) (input : State)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    OrdinaryAt (tupleTail literalExpression opening loopFuel elementsRev) input :=
  tupleTail_ordinary_of_unrestrictedElementFuel literalExpression nestedFuel
    (literal_child_contract nestedFuel) opening loopFuel elementsRev input loopAdequate nestedAdequate

/-- Raw grouping/tuples, arrays, and dot constructors share only the explicit
remaining-count bound. No source, token-span, diagnostic, or ValidFor premise is hidden. -/
theorem literal_raw_branches_ordinary (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    OrdinaryAt (parenthesized literalExpression) input ∧
    OrdinaryAt (arrayLiteral literalExpression) input ∧
    OrdinaryAt (dotConstructor literalExpression) input :=
  ⟨parenthesized_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate,
    arrayLiteral_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate,
    dotConstructor_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate⟩

/-- An explicitly supplied ordinary block discharges the final child premise.
This parser contains just one dispatch layer over literal children. -/
theorem literal_core_and_public_ordinary (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    OrdinaryAt (expressionAtomCore literalExpression emptyBlock) input ∧
    OrdinaryAt (expressionAtom literalExpression emptyBlock) input :=
  ⟨expressionAtomCore_ordinary_of_unrestrictedElementFuel literalExpression emptyBlock fuel
      (literal_child_contract fuel) emptyBlock_ordinary input adequate,
    expressionAtom_ordinary_of_unrestrictedElementFuel literalExpression emptyBlock fuel
      (literal_child_contract fuel) emptyBlock_ordinary input adequate⟩

private def numeral : Token := { span := span 2 4, value := .decimalLiteral "42" }
private def fixture (tokens : Array Token) (cursor endIndex : Nat)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def overshot (prior : List ParseDiagnostic) : State := fixture #[numeral] 9 7 prior
private def hidden (prior : List ParseDiagnostic) : State := fixture #[numeral] 0 0 prior
private def missing (prior : List ParseDiagnostic) : State := fixture #[] 0 3 prior
private def eofFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}

theorem malformed_carriers_are_not_valid (prior : List ParseDiagnostic) :
    ¬ (overshot prior).ValidFor ∧ ¬ (hidden prior).ValidFor ∧ ¬ (missing prior).ValidFor := by
  refine ⟨?_, ?_, ?_⟩
  · intro valid
    have bound := valid.cursor_le_endIndex
    change 9 ≤ 7 at bound
    omega
  · intro valid
    have bound := valid.endByte_le_source
    change 99 ≤ 0 at bound
    omega
  · intro valid
    have bound := valid.endIndex_le_size
    change 3 ≤ 0 at bound
    omega

/-- A stored but hidden literal cannot be mistaken for a present token, and
a missing backing token is distinct from a numerical end-of-window. -/
theorem malformed_lookahead (prior : List ParseDiagnostic) :
    (hidden prior).tokens[0]? = some numeral ∧ (hidden prior).peek? = none ∧
    (hidden prior).atEnd = true ∧ (missing prior).peek? = none ∧
    (missing prior).atEnd = false ∧ (overshot prior).remainingCount = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem malformed_core_and_public_outcomes (prior : List ParseDiagnostic) :
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (overshot prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (overshot prior)) ∧
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (hidden prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (hidden prior)) ∧
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (missing prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (missing prior)) :=
  ⟨literal_core_and_public_ordinary 0 (overshot prior) (by change 0 < 1; decide),
    literal_core_and_public_ordinary 0 (hidden prior) (by change 0 < 1; decide),
    literal_core_and_public_ordinary 3 (missing prior) (by change 3 < 4; decide)⟩

private theorem absent_core (input : State) (noToken : input.peek? = none) :
    expressionAtomCore literalExpression emptyBlock input =
      rejectAt input { head := .expression, tail := [] } .expression := by
  simp only [expressionAtomCore, isCoreLiteral, isBooleanValue, isIdentifier, isSymbol,
    isKeyword, State.peekKind?, noToken, Option.map_none]
  rfl

/-- Overshot and hidden-token ends retain the whole State and arbitrary prior
events. The uncommitted expression failure is at endByte, not the stored literal. -/
theorem numerical_end_rejects_without_events (prior : List ParseDiagnostic) :
    expressionAtom literalExpression emptyBlock (overshot prior) = .reject eofFailure (overshot prior) ∧
    expressionAtom literalExpression emptyBlock (hidden prior) = .reject eofFailure (hidden prior) := by
  constructor
  · rw [expressionAtom, absent_core (overshot prior) rfl]
    rfl
  · rw [expressionAtom, absent_core (hidden prior) rfl]
    rfl

/-- The numerical gap is not a boundary. Public recovery commits the core
report once, then fails on its mandatory first token; its terminal report is
not emitted a second time and all non-diagnostic State fields remain exact. -/
theorem missing_backing_commits_one_report (prior : List ParseDiagnostic) :
    expressionAtomCore literalExpression emptyBlock (missing prior) = .reject eofFailure (missing prior) ∧
    expressionAtom literalExpression emptyBlock (missing prior) =
      .reject eofFailure ((missing prior).emit eofFailure.toDiagnostic) ∧
    ((missing prior).emit eofFailure.toDiagnostic).diagnostics = prior ++ [eofFailure.toDiagnostic] := by
  refine ⟨?_, ?_, ?_⟩
  · exact absent_core (missing prior) rfl
  · rw [expressionAtom, absent_core (missing prior) rfl]
    rfl
  · simp only [State.emit, State.diagnostics, missing, fixture, List.reverse_cons, List.reverse_reverse]

private def sym (first last : Nat) (kind : Symbol) : Token := {
  span := span first last, value := .symbol kind
}
private def literal42 : Expr := { span := numeral.span, value := .literal { span := numeral.span, value := .decimal "42" } }
private def groupTokens : Array Token := #[sym 0 1 .leftParen, numeral, sym 4 5 .rightParen]
private def tupleTokens : Array Token := #[sym 0 1 .leftParen, numeral, sym 4 5 .comma, numeral, sym 8 9 .rightParen]
private def rem (tokens : Array Token) (cursor : Nat) : Remainder := { tokens, cursor, endIndex := 9 }
private def groupValue : Expr := { span := span 0 5, value := .group literal42 }
private def tupleValue : Expr := {
  span := span 0 9, value := .tuple { span := span 0 9, elements := [literal42, literal42] }
}

private theorem parenthesized_exec {input : State} {value : Expr} {after : Remainder}
    (parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses input.file.id
      input.window.endByte input.declarativeRemainder value after []) :
    parenthesized literalExpression input = .ok value (input.traceResult after []) := by
  rcases parenthesized_trace_success_complete literalExpression_trace_success_complete
      literalExpression_success_context parsed with ⟨output, result, afterEq, events⟩
  have frame := parenthesized_success_context literalExpression_success_context result
  exact State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events ▸ result

private theorem group_parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses source 99
    (rem groupTokens 0) groupValue (rem groupTokens 3) [] :=
  .group (span 0 1) (span 4 5) (afterOpening := rem groupTokens 1) (afterElement := rem groupTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rem, groupTokens, numeral])
    ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, rem, groupTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩

private theorem tuple_parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses source 99
    (rem tupleTokens 0) tupleValue (rem tupleTokens 5) [] :=
  .tuple (span 0 1) (span 8 9) (afterOpening := rem tupleTokens 1) (afterFirst := rem tupleTokens 2)
    (first := literal42) (rest := [literal42]) (headEvents := []) (tailEvents := [])
    ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, numeral])
    ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
    (.final (span 4 5) (span 8 9) (afterComma := rem tupleTokens 3) (afterElement := rem tupleTokens 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, numeral])
      ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩)

/-- Actual group and two-element tuple successes are derived from independent
token judgments. Their impossible source/window bounds and prior events are
retained in the whole Reply; no complete-parser decision procedure is used. -/
theorem malformed_groups_and_tuples_still_succeed (prior : List ParseDiagnostic) :
    parenthesized literalExpression (fixture groupTokens 0 9 prior) =
      .ok groupValue (fixture groupTokens 3 9 prior) ∧
    parenthesized literalExpression (fixture tupleTokens 0 9 prior) =
      .ok tupleValue (fixture tupleTokens 5 9 prior) :=
  ⟨parenthesized_exec (input := fixture groupTokens 0 9 prior) group_parsed,
    parenthesized_exec (input := fixture tupleTokens 0 9 prior) tuple_parsed⟩

/-- Even without backing storage, all raw collection branches have ordinary
outcomes under the displayed numerical fuel budget. -/
theorem missing_backing_raw_branches_ordinary (prior : List ParseDiagnostic) :
    OrdinaryAt (parenthesized literalExpression) (missing prior) ∧
    OrdinaryAt (arrayLiteral literalExpression) (missing prior) ∧
    OrdinaryAt (dotConstructor literalExpression) (missing prior) :=
  literal_raw_branches_ordinary 3 (missing prior) (by change 3 < 4; decide)

end Solcore.Test.SyntaxExpressionAtomTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomTraceProgressProperties
/-! A stationary child satisfies all five exact trace contracts and ordinary
execution, but not strict progress. A selected parenthesized atom therefore
exposes noProgress, and completeness rules out either independent trace outcome.
Joint uniqueness and disjointness are deliberately not treated as existence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceProgressProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def stationary {α : Type} (fixed : α) : Parser α := fun input => .ok fixed input
private def stationaryTrace {α : Type} (fixed : α) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : α) (after : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = fixed ∧ after = input ∧ trace = []
private def neverReject (_source : SourceId) (_endByte : Nat) (_input _after : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

private theorem stationary_sound {α : Type} (fixed : α) :
    ParserTraceSuccessSound (stationary fixed) (stationaryTrace fixed) := by
  intro input output value result
  change Reply.ok fixed input = .ok value output at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm⟩

private theorem stationary_complete {α : Type} (fixed : α) :
    ParserTraceSuccessComplete (stationary fixed) (stationaryTrace fixed) := by
  intro input value after trace parsed
  rcases parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨input, rfl, rfl, (List.append_nil _).symm⟩

private theorem stationary_frame {α : Type} (fixed : α) :
    ParserSuccessContext (stationary fixed) := by
  intro input output value result
  change Reply.ok fixed input = .ok value output at result
  cases result
  exact ⟨rfl, rfl⟩

private theorem stationary_reject_sound {α : Type} (fixed : α) :
    ParserTraceRejectSound (stationary fixed) neverReject := by
  intro input rejected failure result
  change Reply.ok fixed input = .reject failure rejected at result
  cases result

private theorem stationary_reject_complete {α : Type} (fixed : α) :
    ParserTraceRejectComplete (stationary fixed) neverReject := by
  intro input after report trace impossible
  exact False.elim impossible

private theorem stationary_exact {α : Type} (fixed : α) (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (stationaryTrace fixed) neverReject source endByte where
  successResultUnique := by
    rintro input left right afterLeft afterRight leftTrace rightTrace
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intros; contradiction
  successRejectDisjoint := by intros; contradiction

/-- These are genuine contracts over every State, not just the fixture below. -/
theorem stationary_child_has_five_contracts_and_is_ordinary {α : Type} (fixed : α) :
    ParserTraceSuccessSound (stationary fixed) (stationaryTrace fixed) ∧
    ParserTraceSuccessComplete (stationary fixed) (stationaryTrace fixed) ∧
    ParserSuccessContext (stationary fixed) ∧
    ParserTraceRejectSound (stationary fixed) neverReject ∧
    ParserTraceRejectComplete (stationary fixed) neverReject ∧
    Parser.Ordinary (stationary fixed) :=
  ⟨stationary_sound fixed, stationary_complete fixed, stationary_frame fixed,
    stationary_reject_sound fixed, stationary_reject_complete fixed,
    fun input => .inl ⟨fixed, input, rfl⟩⟩

private def source : SourceId := { origin := .main, path := "stationary-atom.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def tokens : Array Token := #[token 0 1 .leftParen, token 1 2 .plus, token 2 3 .rightParen]
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "(+)" }, tokens, cursor := 0
  window := { endIndex := 3, endByte := 3 }, diagnosticsRev := prior.reverse
}
private def fixed : Expr := { span := span 1 2, value := .error }
private def fixedBlock : Block := { span := span 0 3, value := [] }

private theorem parenthesized_selected (prior : List ParseDiagnostic) :
    ExpressionAtomDispatchSelects (input prior).declarativeRemainder .parenthesized := by
  constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
      input, State.declarativeRemainder, tokens, token]

/-- The child succeeds while leaving the plus token and all State fields intact. -/
theorem successful_child_has_zero_progress (prior : List ParseDiagnostic) :
    stationary fixed { input prior with cursor := 1 } =
      .ok fixed { input prior with cursor := 1 } ∧
    ¬ (1 : Nat) < ({ input prior with cursor := 1 } : State).cursor :=
  ⟨rfl, Nat.lt_irrefl 1⟩

/-- Exact token execution and the selected raw branch expose the progress check;
no evaluation tactic is applied to the complete atom parser. -/
theorem stationary_atom_reaches_noProgress (block : Parser Block) (prior : List ParseDiagnostic) :
    expressionAtomCore (stationary fixed) block (input prior) =
      .invariant (.noProgress .expression (span 1 2)) := by
  have opening : ExactTokenParses (.symbol .leftParen) (input prior).declarativeRemainder
      (span 0 1) { (input prior).declarativeRemainder with cursor := 1 } :=
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have closeAbsent : isSymbol ({ input prior with cursor := 1 } : State) .rightParen = false :=
    DelimitedTraceInternals.symbol_absent .rightParen (by
      simp [TokenKindAbsentAt, TokenAt, input, tokens, token])
  rw [expressionAtomCore_eq_raw_of_selection (stationary fixed) block (parenthesized_selected prior)]
  change parenthesized (stationary fixed) (input prior) = _
  rw [parenthesized, symbol_eq_ok_of_exactTokenParses .leftParen .expression opening]
  simp only [show (input prior).cursor + 1 = 1 from rfl, closeAbsent, Bool.false_eq_true,
    if_false, stationary, Nat.le_refl, if_true]
  rfl

/-- Both children have independent exact joint bundles, so the atom layer does
too. This is compatible with having no trace outcome at the fixture. -/
theorem stationary_dispatch_has_exact_joint (sourceId : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec
      (ExpressionAtomDispatchTraceParses (stationaryTrace fixed) (stationaryTrace fixedBlock))
      (ExpressionAtomDispatchTraceRejects (stationaryTrace fixed) neverReject neverReject) sourceId endByte :=
  expressionAtomDispatchTraceExactOutcomeSpec
    (stationary_exact fixed sourceId endByte) (stationary_exact fixedBlock sourceId endByte)

/-- The direction from grammar to execution, not vacuous execution soundness,
excludes both successes and rejections at this noProgress input. -/
theorem stationary_dispatch_has_no_trace_outcome (prior : List ParseDiagnostic) :
    (¬ ∃ value after trace, ExpressionAtomDispatchTraceParses (stationaryTrace fixed)
      (stationaryTrace fixedBlock) source 3 (input prior).declarativeRemainder value after trace) ∧
    (¬ ∃ after report trace, ExpressionAtomDispatchTraceRejects (stationaryTrace fixed)
      neverReject neverReject source 3 (input prior).declarativeRemainder after report trace) := by
  constructor
  · rintro ⟨value, after, trace, parsed⟩
    rcases expressionAtomCore_trace_success_complete (stationary_complete fixed)
      (stationary_frame fixed) (stationary_complete fixedBlock) (input := input prior) parsed with ⟨output, result, _⟩
    rw [stationary_atom_reaches_noProgress] at result
    contradiction
  · rintro ⟨after, report, trace, rejection⟩
    rcases expressionAtomCore_trace_reject_complete (stationary_complete fixed)
      (stationary_reject_complete fixed) (stationary_frame fixed)
      (stationary_reject_complete fixedBlock) (input := input prior) rejection with ⟨failure, rejected, result, _⟩
    rw [stationary_atom_reaches_noProgress] at result
    contradiction

theorem stationary_atom_is_not_ordinary (block : Parser Block) :
    ¬ Parser.Ordinary (expressionAtomCore (stationary fixed) block) := by
  intro ordinary
  exact ordinary.ne_invariant (input []) (.noProgress .expression (span 1 2))
    (stationary_atom_reaches_noProgress block [])

end Solcore.Test.SyntaxExpressionAtomTraceProgressProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomTraceSupport
/-! Concrete atom-test support: the recursive expression slot uses the actual
literal leaf, while the supplied block is exactly one pure empty AST. These
contracts describe only that supplied parser, not general recursive blocks. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

def emptyBlock : Block := {
  span := { source := { origin := .main, path := "unused-atom-block.sol" }, startByte := 0, endByte := 0 }, value := []
}
def blockParser : Parser Block := pure emptyBlock
def blockTrace (_ : SourceId) (_ : Nat) (input : Remainder) (value : Block)
    (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = emptyBlock ∧ output = input ∧ trace = []
def blockRejects (_ : SourceId) (_ : Nat) (_ _ : Remainder) (_ : ParseDiagnostic)
    (_ : List ParseDiagnostic) : Prop := False

private theorem block_success_sound : ParserTraceSuccessSound blockParser blockTrace := by
  intro input output value result
  change Reply.ok emptyBlock input = Reply.ok value output at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, by simp⟩
private theorem block_success_complete : ParserTraceSuccessComplete blockParser blockTrace := by
  rintro input value after trace ⟨rfl, rfl, rfl⟩
  exact ⟨input, rfl, rfl, by simp⟩
private theorem block_success_context : ParserSuccessContext blockParser := by
  intro input output value result
  change Reply.ok emptyBlock input = Reply.ok value output at result
  cases result
  exact ⟨rfl, rfl⟩
private theorem block_reject_sound : ParserTraceRejectSound blockParser blockRejects := by
  intro input output failure result
  simp [blockParser, pure] at result
private theorem block_reject_complete : ParserTraceRejectComplete blockParser blockRejects := by
  intro input after report trace impossible
  exact False.elim impossible
private theorem block_reject_frame {input output : State} {failure : Failure}
    (result : blockParser input = .reject failure output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  simp [blockParser, pure] at result

abbrev coreParses := ExpressionAtomDispatchTraceParses LiteralExpressionTraceParses blockTrace
abbrev coreRejects := ExpressionAtomDispatchTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects blockRejects

private theorem core_success_sound : ParserTraceSuccessSound (expressionAtomCore literalExpression blockParser) coreParses :=
  expressionAtomCore_trace_success_sound literalExpression_trace_success_sound literalExpression_success_context block_success_sound
private theorem core_success_complete : ParserTraceSuccessComplete (expressionAtomCore literalExpression blockParser) coreParses :=
  expressionAtomCore_trace_success_complete literalExpression_trace_success_complete literalExpression_success_context block_success_complete
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore literalExpression blockParser) coreRejects :=
  expressionAtomCore_reject_trace_sound literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_success_context block_reject_sound
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore literalExpression blockParser) coreRejects :=
  expressionAtomCore_trace_reject_complete literalExpression_trace_success_complete literalExpression_trace_reject_complete
    literalExpression_success_context block_reject_complete
private theorem core_success_frame {input output : State} {value : Expr}
    (result : expressionAtomCore literalExpression blockParser input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  have frame := expressionAtomCore_trace_success_context literalExpression_success_context block_success_context result
  exact ⟨frame.1, congrArg TokenWindow.endByte frame.2⟩
private theorem core_reject_frame {input output : State} {failure : Failure}
    (result : expressionAtomCore literalExpression blockParser input = .reject failure output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte :=
  expressionAtomCore_reject_source_endByte literalExpression_success_context
    (fun result => ⟨(literalExpression_reject_context result).1,
      congrArg TokenWindow.endByte (literalExpression_reject_context result).2⟩) block_reject_frame result

theorem core_reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : coreRejects input.file.id input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionAtomCore literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionAtomCore_trace_reject_failure_state_iff literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_trace_success_complete literalExpression_trace_reject_complete literalExpression_success_context
    block_reject_sound block_reject_complete core_reject_frame).mp rejection

theorem public_success_of_trace {input : State} {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : ExpressionAtomTraceParses coreParses coreRejects input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    expressionAtom literalExpression blockParser input = .ok value (input.traceResult after trace) :=
  (expressionAtom_trace_success_state_iff core_success_sound core_reject_sound core_success_complete core_reject_complete
    core_success_frame core_reject_frame).mp parsed

theorem public_reject_of_trace {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejection : ExpressionAtomTraceRejects coreRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    expressionAtom literalExpression blockParser input = .reject failure (input.traceResult after trace) :=
  (expressionAtom_trace_reject_failure_state_iff core_reject_sound core_reject_complete core_reject_frame).mp rejection

end Solcore.Test.SyntaxExpressionAtomTraceSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxExpressionAtomTraceProperties
/-! Independent public atom traces drive complete executable replies. The real
literal child rejects inside a dot constructor after its checked-name event.
Recovery rewinds only the cursor, commits that report once, and skips tokens
without replaying name checks. This is one atom layer, not full expressions. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxExpressionAtomTraceSupport

private def source : SourceId := { origin := .main, path := "public-atom-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (value : Symbol) : Token := { span := span startByte endByte, value := .symbol value }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def tokens : List Token := [symbol 0 1 .dot, { span := name.span, value := .identifier name.value },
  symbol 4 5 .leftParen, symbol 5 6 .plus, symbol 6 7 .rightParen, symbol 8 9 .semicolon]
private def remainder (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def input (cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex := 6, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def coreFailure : Failure := {
  span := span 5 6, found := some (.symbol .plus), expected := { head := .coreLiteral, tail := [] }, context := .expression
}
private def recovered : Expr := { span := span 0 6, value := .error }
private def recoveryEvent : ParseDiagnostic := expressionAtomRecoveryTraceEvent recovered.span
private def events : List ParseDiagnostic := [nameEvent, coreFailure.toDiagnostic, recoveryEvent]
private def final (prior : List ParseDiagnostic) : State := {
  input 4 prior with diagnosticsRev := events.reverse ++ prior.reverse
}

private theorem name_trace : ExpressionNameTraceParses source 99 (remainder 1) name (remainder 2) [nameEvent] :=
  .identifier (by simp [BooleanPatternAbsentAt, TokenKindAbsentAt, TokenAt, remainder, tokens, name])
    (.parsed ⟨⟨by change 1 < 6; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide)))

private theorem literal_rejection : LiteralExpressionTraceRejects source 99 (remainder 3) (remainder 3)
    coreFailure.toDiagnostic [] :=
  ⟨.absent (by simp [CoreLiteralAbsentAt, TokenAt, remainder, tokens, symbol]),
    .reported (.token (current := symbol 5 6 .plus) ⟨by change 3 < 6; decide, rfl⟩), rfl⟩

private theorem core_rejection : coreRejects source 99 (remainder 0) (remainder 3) coreFailure.toDiagnostic [nameEvent] := by
  have selection : ExpressionAtomDispatchSelects (remainder 0) .dotConstructor :=
    .dotConstructor (by simp [CoreLiteralStartsAt, TokenAt, remainder, tokens, symbol])
      (by simp [ExpressionNameStartsAt, TokenAt, remainder, tokens, symbol])
      ⟨span 0 1, ⟨by change 0 < 6; decide, rfl⟩⟩
  apply ExpressionAtomDispatchTraceRejects.selected .dotConstructor selection
  change DotConstructorTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
    source 99 (remainder 0) (remainder 3) coreFailure.toDiagnostic [nameEvent]
  simpa only [List.append_nil] using DotConstructorTraceRejects.argumentsRejected
    (input := remainder 0) (afterDot := remainder 1) (afterName := remainder 2)
    (span 0 1) ⟨⟨by change 0 < 6; decide, rfl⟩, rfl⟩ name_trace
    (.present (input := remainder 2) (span 4 5) ⟨by change 2 < 6; decide, rfl⟩
      (.firstRejected (afterOpening := remainder 3) (span 4 5) ⟨⟨by change 2 < 6; decide, rfl⟩, rfl⟩
        (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, symbol])) literal_rejection))

private theorem scan_continues {cursor : Nat} (position : cursor = 1 ∨ cursor = 2 ∨ cursor = 3) :
    ¬ ExpressionAtomRecoveryStops (remainder cursor) (remainder cursor) := by
  rcases position with rfl | rfl | rfl <;> intro stops <;>
    cases stops <;> simp_all [TokenAt, remainder, tokens, name, symbol]

private theorem recovery_trace : ExpressionAtomRecoveryTraceParses source 99 (remainder 0)
    recovered (remainder 4) [recoveryEvent] :=
  ⟨.recovered (token := symbol 0 1 .dot) ⟨by change 0 < 6; decide, rfl⟩
    (.next (scan_continues (.inl rfl)) ⟨by change 1 < 6; decide, rfl⟩
      (.next (scan_continues (.inr (.inl rfl))) ⟨by change 2 < 6; decide, rfl⟩
        (.next (scan_continues (.inr (.inr rfl))) ⟨by change 3 < 6; decide, rfl⟩
          (.stop (.rightParen ⟨by change 4 < 6; decide, rfl⟩))))), rfl⟩

private theorem nonboundary : ¬ ExpressionAtomBoundaryStops (remainder 0) := by
  intro stops
  cases stops <;> simp_all [TokenAt, remainder, tokens, symbol]

private theorem public_trace : ExpressionAtomTraceParses coreParses coreRejects source 99
    (remainder 0) recovered (remainder 4) events :=
  .recovered core_rejection nonboundary recovery_trace

/-- Core literal failure occurs after the name warning, before any recovery
report is committed. Its complete Failure is preserved. -/
theorem dot_core_failure_retains_checked_name (prior : List ParseDiagnostic) :
    expressionAtomCore literalExpression blockParser (input 0 prior) =
      .reject coreFailure { input 3 prior with diagnosticsRev := nameEvent :: prior.reverse } ∧
    ({ input 3 prior with diagnosticsRev := nameEvent :: prior.reverse } : State).diagnostics = prior ++ [nameEvent] := by
  refine ⟨core_reject_of_trace (input := input 0 prior) core_rejection, ?_⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Revisited and skipped name tokens are not checked again. The closing
parenthesis and following semicolon remain outside the recovered error span. -/
theorem public_dot_recovery_orders_reports (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 0 prior) = .ok recovered (final prior) ∧
    (final prior).diagnostics = prior ++ events ∧
    (final prior).cursor = 4 ∧ (final prior).peek? = some (symbol 6 7 .rightParen) ∧
    (final prior).tokens[5]? = some (symbol 8 9 .semicolon) := by
  refine ⟨public_success_of_trace (input := input 0 prior) public_trace, ?_, rfl, rfl, rfl⟩
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem prior_duplicates_survive_recovery (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 0 (prior ++ [nameEvent, nameEvent])) =
      .ok recovered (final (prior ++ [nameEvent, nameEvent])) ∧
    (final (prior ++ [nameEvent, nameEvent])).diagnostics =
      prior ++ [nameEvent, nameEvent, nameEvent, coreFailure.toDiagnostic, recoveryEvent] := by
  have result := public_dot_recovery_orders_reports (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [events, List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

/-- A successful selected name is returned directly, even though the supplied
literal-only nested parser would reject its spelling. The next '(' is unread. -/
theorem successful_name_bypasses_recovery (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 1 prior) =
      .ok { span := name.span, value := .identifier name }
        { input 2 prior with diagnosticsRev := nameEvent :: prior.reverse } ∧
    ({ input 2 prior with diagnosticsRev := nameEvent :: prior.reverse } : State).peek? = some (symbol 4 5 .leftParen) := by
  have selection : ExpressionAtomDispatchSelects (remainder 1) .name :=
    .name (by simp [CoreLiteralStartsAt, TokenAt, remainder, tokens])
      (.inr (.inr ⟨name.span, name.value, ⟨by change 1 < 6; decide, rfl⟩⟩))
  have parsed : ExpressionAtomTraceParses coreParses coreRejects source 99 (remainder 1)
      { span := name.span, value := .identifier name } (remainder 2) [nameEvent] :=
    .core (.selected .name selection (.parsed name_trace))
  exact ⟨public_success_of_trace (input := input 1 prior) parsed, rfl⟩

private def boundaryFailure : Failure := {
  span := span 6 7, found := some (.symbol .rightParen), expected := { head := .expression, tail := [] }, context := .expression
}
private theorem boundary_trace : ExpressionAtomTraceRejects coreRejects source 99
    (remainder 4) (remainder 4) boundaryFailure.toDiagnostic [] := by
  have selection : ExpressionAtomDispatchSelects (remainder 4) .final := by
    apply ExpressionAtomDispatchSelects.final <;>
      simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, remainder, tokens, symbol]
  exact .boundary (input := remainder 4) (failed := remainder 4)
    (ExpressionAtomDispatchTraceRejects.selected .final selection
      (.rejected (.reported (.token (current := symbol 6 7 .rightParen) ⟨by change 4 < 6; decide, rfl⟩))))
    (.rightParen ⟨by change 4 < 6; decide, rfl⟩)

theorem first_boundary_failure_is_uncommitted (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (input 4 prior) = .reject boundaryFailure (input 4 prior) ∧
    (input 4 prior).diagnostics = prior := by
  refine ⟨public_reject_of_trace (input := input 4 prior) boundary_trace, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

private def missingInput (prior : List ParseDiagnostic) : State := {
  input 0 prior with tokens := #[], window := { endIndex := 2, endByte := 99 }
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}
private theorem missing_trace : ExpressionAtomTraceRejects coreRejects source 99
    (missingInput []).declarativeRemainder (missingInput []).declarativeRemainder missingFailure.toDiagnostic
    [missingFailure.toDiagnostic] := by
  have selection : ExpressionAtomDispatchSelects (missingInput []).declarativeRemainder .final := by
    apply ExpressionAtomDispatchSelects.final <;>
      simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
        missingInput, input, State.declarativeRemainder]
  have core : coreRejects source 99 (missingInput []).declarativeRemainder
      (missingInput []).declarativeRemainder missingFailure.toDiagnostic [] :=
    .selected .final selection
      (.rejected (.reported (.missingToken (by change 0 < 2; decide) rfl)))
  have continues : ¬ ExpressionAtomBoundaryStops (missingInput []).declarativeRemainder := by
    intro stops
    cases stops <;> simp_all [TokenAt, missingInput, input, State.declarativeRemainder]
  exact .recovery core continues ⟨.missingToken (by change 0 < 2; decide) rfl,
    .reported (.missingToken (by change 0 < 2; decide) rfl), rfl⟩

/-- The core and recovery failures have equal payloads, but only the original
is committed. The second remains the exact terminal Failure. -/
theorem initial_missing_backing_separates_two_reports (prior : List ParseDiagnostic) :
    expressionAtom literalExpression blockParser (missingInput prior) =
      .reject missingFailure { missingInput prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } ∧
    ({ missingInput prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } : State).diagnostics =
      prior ++ [missingFailure.toDiagnostic] ∧
    (missingInput prior).cursor < (missingInput prior).window.endIndex ∧ (missingInput prior).peek? = none := by
  refine ⟨public_reject_of_trace (input := missingInput prior) missing_trace, ?_, by change 0 < 2; decide, rfl⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

theorem mixed_recovery_filter_retains_name (text : String) (lexical : List SourceSpan)
    (reportSuppressed : LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoverySuppressed : LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events [nameEvent] :=
  expressionAtomRecoveryTrace_cascadeFilters text lexical
    (show ParseDiagnosticCascadeFilters text lexical [nameEvent] [nameEvent] from
      .keep (fun suppressed => suppressed.1) .nil)
    (.drop ⟨by trivial, reportSuppressed⟩ .nil)
    (recovery_trace.cascade_dropped text lexical recoverySuppressed)

theorem lexical_cascade_drops_only_report_and_recovery (text : String) :
    filterParseDiagnostics { id := source, content := text }
      [{ span := span 0 6, kind := .invalidToken }] events = [nameEvent] :=
  filterParseDiagnostics_eq_of_cascadeFilters _ _
    (mixed_recovery_filter_retains_name text [span 0 6]
      ⟨span 0 6, by simp, ⟨rfl, .inr (.inl ⟨by decide, by decide⟩)⟩⟩
      ⟨span 0 6, by simp, ⟨rfl, .inl rfl⟩⟩)

end Solcore.Test.SyntaxExpressionAtomTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxLiteralExpressionTraceExactnessProperties
/-! Concrete literal expressions close the expression assumptions in return
existence and isolated-block correspondence. These are restricted parsers. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralExpressionTraceExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

/-- The concrete literal-return parser cannot produce an invariant outcome,
even on invalid carriers or with arbitrary prior diagnostics. -/
theorem literal_return_ne_invariant (input : State) (error : ParserInvariantError) :
    returnStatement literalExpression input ≠ .invariant error := by
  intro result
  rcases SyntaxReturnStatementTraceExactnessProperties.return_execution_has_ordinary_outcome
      literalExpression_trace_success_complete literalExpression_trace_reject_complete
      literalExpression_success_context input
      (literalExpressionTraceOutcomeExists input.file.id input.window.endByte) with successful | rejected
  · rcases successful with ⟨statement, output, trace, ordinary, _⟩
    rw [result] at ordinary
    contradiction
  · rcases rejected with ⟨failure, output, trace, ordinary, _⟩
    rw [result] at ordinary
    contradiction

theorem literal_return_rejection_excludes_success
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte input rejected report trace) :
    ¬ ∃ statement output events, ReturnStatementTraceParses LiteralExpressionTraceParses
      source endByte input statement output events :=
  (literalReturnStatementTraceExactOutcomeSpec source endByte).successRejectDisjoint rejection

/-- Every expression and statement execution premise is discharged by the
real literal leaf; only the independent restricted-block judgment remains. -/
theorem isolated_literal_return_block_trace_iff
    (policy : TailExpressionPolicy) {input : State} {body : Block} {after : Remainder}
    {trace : List ParseDiagnostic} :
    IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
        policy.declarative)
      input.file.id input.window.endByte input.declarativeRemainder body after trace ↔
    ∃ output, isolateBlock (coreBlock (returnStatement literalExpression) policy) input = .ok body output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  SyntaxReturnStatementTraceExactnessProperties.isolated_return_block_trace_iff
    literalExpression_trace_success_sound literalExpression_trace_reject_sound
    literalExpression_trace_success_complete literalExpression_trace_reject_complete
    literalExpression_success_context policy

end Solcore.Test.SyntaxLiteralExpressionTraceExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxLiteralReturnTraceExamples
/-! Concrete empty and decimal returns through the actual literal-expression
leaf. General expression behavior is not asserted. Only canonical lexer
fixtures use kernel decision; parser outcomes follow independent trace rules. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralReturnTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "literal-return-trace.sol" }
def file (content : String) : SourceFile := { id := source, content }
def byteSpan (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
def marker (offset : Nat) : Token := { span := byteSpan offset (offset + 6), value := .keyword .returnKw }
def decimal (offset : Nat) : Token := { span := byteSpan offset (offset + 2), value := .decimalLiteral "42" }
def semicolon (offset : Nat) : Token := { span := byteSpan offset (offset + 1), value := .symbol .semicolon }
def literal42 (offset : Nat) : Expr := {
  span := byteSpan offset (offset + 2)
  value := .literal { span := byteSpan offset (offset + 2), value := .decimal "42" }
}
def carrier (tokens : List Token) : LexedFile := { source, tokens, comments := [], diagnostics := [] }
def atCursor (tokens : List Token) (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := tokens.length, cursor }
def initial (content : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  State.initial (file content) (carrier tokens) with diagnosticsRev := prior.reverse
}

/-- Located decimal-token recognition instantiates the actual literal grammar,
retaining the original spelling, expression span, and empty event sequence. -/
theorem literal42_trace {input : Remainder} (offset : Nat)
    (reportSource : SourceId) (endByte : Nat)
    (token : TokenAt input.tokens input.endIndex input.cursor (decimal offset)) :
    LiteralExpressionTraceParses reportSource endByte input (literal42 offset)
      { input with cursor := input.cursor + 1 } [] :=
  ⟨.parsed (.decimal token), rfl⟩

/-- The concrete `return;` skips every supplied expression parser, even one
that would reject, emit events, or return an invariant on this input. -/
theorem empty_return_bypasses_expression (expression : Parser Expr) (prior : List ParseDiagnostic) :
    returnStatement expression (initial "return;" [marker 0, semicolon 6] prior) =
      .ok { span := byteSpan 0 7, value := .returnStmt none }
        { initial "return;" [marker 0, semicolon 6] prior with cursor := 2 } :=
  returnStatement_eq_ok_none_of_exactTokens expression
    (input := initial "return;" [marker 0, semicolon 6] prior)
    (markerSpan := byteSpan 0 6) (semicolonSpan := byteSpan 6 7)
    (afterMarker := atCursor [marker 0, semicolon 6] 1)
    (after := atCursor [marker 0, semicolon 6] 2)
    ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩

def completeTokens : List Token := [marker 0, decimal 7, semicolon 9]
def returnedLiteral : Statement := { span := byteSpan 0 10, value := .returnStmt (some (literal42 7)) }

private theorem completeParsed : ReturnStatementTraceParses LiteralExpressionTraceParses
    source 10 (atCursor completeTokens 0) returnedLiteral (atCursor completeTokens 3) [] :=
  .parsed (byteSpan 0 6) (byteSpan 9 10)
    (afterMarker := atCursor completeTokens 1) (afterValue := atCursor completeTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, atCursor, completeTokens, decimal])
      (literal42_trace 7 source 10 ⟨by decide, rfl⟩))
    ⟨⟨by decide, rfl⟩, rfl⟩

theorem literal_return_retains_prior (prior : List ParseDiagnostic) :
    ∃ output, returnStatement literalExpression (initial "return 42;" completeTokens prior) =
        .ok returnedLiteral output ∧ output.declarativeRemainder = atCursor completeTokens 3 ∧
      output.diagnostics = prior := by
  simpa only [initial, State.diagnostics, State.initial, List.reverse_reverse, List.append_nil] using
    (returnStatement_trace_success_iff literalExpression_trace_success_sound
      literalExpression_trace_success_complete (input := initial "return 42;" completeTokens prior)).mp completeParsed

def missingTokens : List Token := [marker 0, decimal 7]
def missingFailure : Failure := {
  span := byteSpan 9 9, found := none
  expected := { head := .symbol .semicolon, tail := [] }, context := .statement
}

private theorem missingParsed : ReturnStatementTraceRejects LiteralExpressionTraceParses
    LiteralExpressionTraceRejects source 9 (atCursor missingTokens 0)
      (atCursor missingTokens 2) missingFailure.toDiagnostic [] :=
  .semicolonRejected (byteSpan 0 6)
    (afterMarker := atCursor missingTokens 1) (afterValue := atCursor missingTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, atCursor, missingTokens, decimal])
      (literal42_trace 7 source 9 ⟨by decide, rfl⟩))
    (by simp [TokenKindAbsentAt, TokenAt, atCursor, missingTokens])
    (.reported (.windowEnd (by decide)))

/-- The literal has already been consumed when EOF reports the mandatory
semicolon at byte 9. The exact failure remains outside all prior events. -/
theorem literal_return_window_end_failure (prior : List ParseDiagnostic) :
    ∃ output, returnStatement literalExpression (initial "return 42" missingTokens prior) =
        .reject missingFailure output ∧ output.declarativeRemainder = atCursor missingTokens 2 ∧
      output.diagnostics = prior := by
  simpa only [initial, State.diagnostics, State.initial, List.reverse_reverse, List.append_nil] using
    (returnStatement_trace_reject_failure_iff literalExpression_trace_success_sound
      literalExpression_trace_reject_sound literalExpression_trace_success_complete
      literalExpression_trace_reject_complete literalExpression_success_context
      (input := initial "return 42" missingTokens prior)).mp missingParsed

private theorem lex_ok_of_toOption {sourceFile : SourceFile} {lexed : LexedFile}
    (checked : (Lexer.lex sourceFile).toOption = some lexed) : Lexer.lex sourceFile = .ok lexed := by
  cases result : Lexer.lex sourceFile with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

set_option maxRecDepth 8192 in
theorem complete_lexes : Lexer.lex (file "return 42;") = .ok (carrier completeTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

set_option maxRecDepth 8192 in
theorem missing_lexes : Lexer.lex (file "return 42") = .ok (carrier missingTokens) := by
  apply lex_ok_of_toOption
  decide +kernel

theorem canonical_literal_return (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file "return 42;") = .ok lexed ∧
      returnStatement literalExpression
          { State.initial (file "return 42;") lexed with diagnosticsRev := prior.reverse } =
        .ok returnedLiteral output ∧
      output.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 3, cursor := 3 } ∧
      output.diagnostics = prior := by
  rcases literal_return_retains_prior prior with ⟨output, result⟩
  exact ⟨carrier completeTokens, output, complete_lexes, result⟩

theorem canonical_literal_return_missing_semicolon (prior : List ParseDiagnostic) :
    ∃ lexed output, Lexer.lex (file "return 42") = .ok lexed ∧
      returnStatement literalExpression
          { State.initial (file "return 42") lexed with diagnosticsRev := prior.reverse } =
        .reject missingFailure output ∧
      output.declarativeRemainder = { tokens := lexed.tokens.toArray, endIndex := 2, cursor := 2 } ∧
      output.diagnostics = prior := by
  rcases literal_return_window_end_failure prior with ⟨output, result⟩
  exact ⟨carrier missingTokens, output, missing_lexes, result⟩

end Solcore.Test.SyntaxLiteralReturnTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxLiteralReturnBlockTraceExamples
/-! A return-only block uses the actual decimal-literal expression leaf and
the empty-return bypass. This is a restricted composition, not general Core
expression or statement trace completeness. Tokens are explicitly constructed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLiteralReturnBlockTraceExamples

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxLiteralReturnTraceExamples

def blockTokens : List Token := [
  { span := byteSpan 0 1, value := .symbol .leftBrace },
  marker 2, decimal 9, semicolon 11, marker 13, semicolon 19,
  { span := byteSpan 21 22, value := .symbol .rightBrace },
  { span := byteSpan 23 27, value := .identifier "tail" }]
def blockRem (endIndex cursor : Nat) : Remainder := { tokens := blockTokens.toArray, endIndex, cursor }
def firstReturn : Statement := { span := byteSpan 2 12, value := .returnStmt (some (literal42 9)) }
def lastReturn : Statement := { span := byteSpan 13 20, value := .returnStmt none }
def body : Block := { span := byteSpan 0 22, value := [firstReturn, lastReturn] }
def blockInput (prior : List ParseDiagnostic) : State := initial "{ return 42; return; } tail" blockTokens prior

private theorem firstParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) :
    ReturnStatementTraceParses LiteralExpressionTraceParses reportSource endByte
      (blockRem endIndex 1) firstReturn (blockRem endIndex 4) [] :=
  .parsed (byteSpan 2 8) (byteSpan 11 12)
    (afterMarker := blockRem endIndex 2) (afterValue := blockRem endIndex 3)
    ⟨⟨by change 1 < endIndex; omega, rfl⟩, rfl⟩
    (.present (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, decimal])
      (literal42_trace 9 reportSource endByte ⟨by change 2 < endIndex; omega, rfl⟩))
    ⟨⟨by change 3 < endIndex; omega, rfl⟩, rfl⟩

private theorem lastParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) :
    ReturnStatementTraceParses LiteralExpressionTraceParses reportSource endByte
      (blockRem endIndex 4) lastReturn (blockRem endIndex 6) [] :=
  .parsed (byteSpan 13 19) (byteSpan 19 20)
    (afterMarker := blockRem endIndex 5) (afterValue := blockRem endIndex 5)
    ⟨⟨by change 4 < endIndex; omega, rfl⟩, rfl⟩
    (.absent (byteSpan 19 20) ⟨by change 5 < endIndex; omega, rfl⟩)
    ⟨⟨by change 5 < endIndex; omega, rfl⟩, rfl⟩

private theorem blockParsed (reportSource : SourceId) (endByte endIndex : Nat)
    (inside : 6 < endIndex) (policy : CoreBlockTailPolicy) :
    CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy
      reportSource endByte (blockRem endIndex 0) body (blockRem endIndex 7) [] := by
  have closing : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 6) [] (byteSpan 21 22) (blockRem endIndex 7) [] :=
    .close _ ⟨⟨inside, rfl⟩, rfl⟩
  have last : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 4) [lastReturn] (byteSpan 21 22)
      (blockRem endIndex 7) [] :=
    .next (by change 4 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, marker])
      (lastParsed reportSource endByte endIndex inside) (by change 4 < 6; decide) closing
  have items : CoreBlockItemsTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses)
      reportSource endByte (blockRem endIndex 1) [firstReturn, lastReturn] (byteSpan 21 22)
      (blockRem endIndex 7) [] :=
    .next (by change 1 < endIndex; omega)
      (by simp [TokenKindAbsentAt, TokenAt, blockRem, blockTokens, marker])
      (firstParsed reportSource endByte endIndex inside) (by change 1 < 4; decide) last
  have tails : CoreBlockTailsDiagnosticTrace policy [firstReturn, lastReturn] [] := by
    have firstClean : CoreBlockStatementDiagnosticTrace firstReturn [] := .clean trivial
    have lastClean : CoreBlockStatementDiagnosticTrace lastReturn [] := .clean trivial
    cases policy with
    | allow => exact .cons firstClean .lastAllowed
    | require => exact .cons firstClean (.lastRequired lastClean)
  exact .parsed (byteSpan 0 1) (byteSpan 21 22) (afterOpening := blockRem endIndex 1)
    ⟨⟨by change 0 < endIndex; omega, rfl⟩, rfl⟩ items tails

private def capture : BalancedBlockCapture := { span := byteSpan 0 22, endIndex := 7, endByte := 22 }

private theorem blockCaptured : BalancedBlockCaptures (blockRem 8 0) capture :=
  .captured (input := blockRem 8 0) (openingSpan := byteSpan 0 1) (closingSpan := byteSpan 21 22)
    ⟨by decide, rfl⟩
    (.other (token := marker 2) ⟨by decide, rfl⟩ (by decide) (by decide)
      (.other (token := decimal 9) ⟨by decide, rfl⟩ (by decide) (by decide)
        (.other (token := semicolon 11) ⟨by decide, rfl⟩ (by decide) (by decide)
          (.other (token := marker 13) ⟨by decide, rfl⟩ (by decide) (by decide)
            (.other (token := semicolon 19) ⟨by decide, rfl⟩ (by decide) (by decide)
              (.close ⟨by decide, rfl⟩))))))

/-- The actual return constructor uses the actual literal leaf for the first
value and bypasses it for the second return. Both full ASTs remain ordered. -/
theorem literal_and_empty_returns_raw (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, coreBlock (returnStatement literalExpression) policy (blockInput prior) = .ok body output ∧
      output.declarativeRemainder = blockRem 8 7 ∧ output.diagnostics = prior := by
  simpa only [blockInput, initial, State.initial, State.diagnostics, List.reverse_reverse, List.append_nil] using
    (coreBlock_trace_success_iff (returnStatement_trace_success_sound literalExpression_trace_success_sound)
      (returnStatement_trace_success_complete literalExpression_trace_success_complete)
      (returnStatement_success_context literalExpression_success_context) policy
      (input := blockInput prior)).mp (blockParsed source 27 8 (by decide) policy.declarative)

/-- Balanced success restores the full parent window and leaves `tail`
unread after the mixed nonempty/empty return body, with every prior event intact. -/
theorem literal_and_empty_returns_isolated (policy : TailExpressionPolicy) (prior : List ParseDiagnostic) :
    ∃ output, isolateBlock (coreBlock (returnStatement literalExpression) policy) (blockInput prior) =
        .ok body output ∧ output.declarativeRemainder = blockRem 8 7 ∧ output.diagnostics = prior ∧
      output.file = (blockInput prior).file ∧ output.window = (blockInput prior).window ∧
      output.peek? = some { span := byteSpan 23 27, value := .identifier "tail" } := by
  have parsed : IsolatedBlockTraceParses
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy.declarative)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy.declarative)
      source 27 (blockRem 8 0) body (blockRem 8 7) [] :=
    .captured blockCaptured (blockParsed source 22 7 (by decide) policy.declarative)
  rcases (isolatedCoreBlock_trace_success_iff (statement := returnStatement literalExpression)
      (returnStatement_trace_success_sound literalExpression_trace_success_sound)
      (returnStatement_reject_trace_sound literalExpression_trace_success_sound
        literalExpression_trace_reject_sound literalExpression_success_context)
      (returnStatement_trace_success_complete literalExpression_trace_success_complete)
      (returnStatement_trace_reject_complete literalExpression_trace_success_complete
        literalExpression_trace_reject_complete literalExpression_success_context)
      (returnStatement_success_context literalExpression_success_context) policy
      (input := blockInput prior)).mp parsed with ⟨output, result, after, diagnostics⟩
  rcases BlockInternals.captureBlock?_complete (input := blockInput prior) blockCaptured with
    ⟨captured, captureResult, _, _, _⟩
  have frame := isolateBlock_captured_success_frame captureResult result
  refine ⟨output, result, after, ?_, frame.1, frame.2.2.1, ?_⟩
  · simpa only [blockInput, initial, State.initial, State.diagnostics,
      List.reverse_reverse, List.append_nil] using diagnostics
  · have tokens := congrArg Remainder.tokens after
    have endpoint := congrArg Remainder.endIndex after
    have cursor := congrArg Remainder.cursor after
    change output.tokens = blockTokens.toArray at tokens
    change output.window.endIndex = 8 at endpoint
    change output.cursor = 7 at cursor
    simp only [State.peek?, tokens, endpoint, cursor, Nat.reduceLT, if_true]
    rfl

end Solcore.Test.SyntaxLiteralReturnBlockTraceExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxParenthesizedRejectionTraceProperties
/-! Public consumers of the raw, not dispatcher-selected, boundaries. These
exact-token laws quantify arbitrary parsers, states, and prior diagnostics;
there is no lexical or concrete nested-expression completeness claim. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParenthesizedRejectionTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.Parser.DelimitedTraceInternals


theorem unselected_tail_reports_comma_without_calling_child
    (nested : Parser Expr) (opening : Token) (fuel : Nat) (elementsRev : List Expr)
    {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .comma))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .comma, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    tupleTail nested opening (fuel + 1) elementsRev input = .reject failure input := by
  rcases (symbol_reject_reports_iff .comma .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [tupleTail, result]

theorem unselected_parenthesized_reports_opening_without_calling_child
    (nested : Parser Expr) {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .leftParen))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .leftParen, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    parenthesized nested input = .reject failure input := by
  rcases (symbol_reject_reports_iff .leftParen .expression).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parenthesized, result]

theorem closing_rejection_preserves_every_state_field
    (opening : Token) (elementsRev : List Expr) {input : State} {failure : Failure}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .rightParen))
    (reported : DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
      { head := .symbol .rightParen, tail := [] } .expression input.declarativeRemainder failure.toDiagnostic) :
    closeTuple opening elementsRev input = .reject failure input := by
  rcases (closeTuple_reject_reports_iff opening elementsRev).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  exact result

/-- Even a trailing comma with one prior element closes a group, not a tuple.
The child parser is completely arbitrary and is bypassed at the right paren. -/
theorem trailing_comma_single_element_is_group_without_child
    (nested : Parser Expr) (opening : Token) (only : Expr) (fuel : Nat)
    {input : State} {afterComma after : DeclarativeGrammar.Remainder} (commaSpan closingSpan : SourceSpan)
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) [only] input =
      .ok { span := SourceSpan.cover opening.span closingSpan, value := .group only }
        { input with cursor := input.cursor + 1 + 1 } ∧
      ({ input with cursor := input.cursor + 1 + 1 } : State).declarativeRemainder = after := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
  rcases comma with ⟨_, rfl⟩
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  have selected := symbol_present .rightParen (input := { input with cursor := input.cursor + 1 }) closing
  exact ⟨by simp only [tupleTail, commaResult, selected, if_true, closeTuple_eq_of_symbol, closingResult]
            rfl, closing.2.symm⟩

/-- After a successful child, a non-comma goes directly to a right-paren
failure; no generic comma-or-closing report and no extra event is introduced. -/
theorem first_child_events_survive_right_paren_only_failure
    (nested : Parser Expr) {input next : State} {afterOpening : DeclarativeGrammar.Remainder}
    (openingSpan : SourceSpan) (value : Expr) (failure : Failure) (events : List ParseDiagnostic)
    (opening : DeclarativeGrammar.ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (notEmpty : DeclarativeGrammar.TokenKindAbsentAt afterOpening.tokens afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
    (child : nested { input with cursor := input.cursor + 1 } = .ok value next)
    (progress : input.cursor + 1 < next.cursor)
    (childEvents : next.diagnostics = input.diagnostics ++ events)
    (noComma : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex next.cursor (.symbol .comma))
    (noClosing : DeclarativeGrammar.TokenKindAbsentAt next.tokens next.window.endIndex next.cursor (.symbol .rightParen))
    (reported : DeclarativeGrammar.RejectAtReports next.file.id next.window.endByte
      { head := .symbol .rightParen, tail := [] } .expression next.declarativeRemainder failure.toDiagnostic) :
    parenthesized nested input = .reject failure next ∧ next.diagnostics = input.diagnostics ++ events := by
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have closingResult := closing_rejection_preserves_every_state_field
    { span := openingSpan, value := .symbol .leftParen } [value] noClosing reported
  have moved : ¬ next.cursor ≤ input.cursor + 1 := by omega
  exact ⟨by simp only [parenthesized, openingResult, symbol_absent .rightParen
              (input := { input with cursor := input.cursor + 1 }) notEmpty, Bool.false_eq_true, if_false,
              child, moved, symbol_absent .comma noComma, closingResult], childEvents⟩

end Solcore.Test.SyntaxParenthesizedRejectionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParenthesizedSuccessTraceProperties
/-! Boundary consumers for the bespoke parenthesized parser. Immediate empty
and trailing closes bypass any child, preserve all prior events, and interpret
an already-read singleton as a group even after a comma. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParenthesizedSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

theorem empty_parentheses_bypass_any_child (nested : Parser Expr)
    {input : State} {openingSpan closingSpan : SourceSpan} {afterOpening after : Remainder}
    (opening : ExactTokenParses (.symbol .leftParen) input.declarativeRemainder openingSpan afterOpening)
    (closing : ExactTokenParses (.symbol .rightParen) afterOpening closingSpan after) :
    parenthesized nested input = .ok
      (closeParenthesizedExpression openingSpan closingSpan [])
      { input with cursor := input.cursor + 2 } := by
  have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .expression opening
  rcases opening with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [parenthesized, openingResult, present, if_true, closeTuple_eq_of_symbol, closingResult,
    List.reverse_nil]

/-- Closing is silent even with an arbitrary accumulated reverse prefix; the
prefix is restored in forward order exactly once and never diagnosed again. -/
theorem trailing_close_bypasses_any_child (nested : Parser Expr) (opening : Token)
    (elementsRev : List Expr) (fuel : Nat) {input : State}
    {commaSpan closingSpan : SourceSpan} {afterComma after : Remainder}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) elementsRev input = .ok
      (closeParenthesizedExpression opening.span closingSpan elementsRev.reverse)
      { input with cursor := input.cursor + 2 } := by
  have commaResult := symbol_eq_ok_of_exactTokenParses .comma .expression comma
  rcases comma with ⟨_, rfl⟩
  have present := DelimitedTraceInternals.symbol_present .rightParen
    (input := { input with cursor := input.cursor + 1 }) closing
  have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .expression
    (input := { input with cursor := input.cursor + 1 }) closing
  simp only [tupleTail, commaResult, present, if_true, closeTuple_eq_of_symbol, closingResult]

theorem two_element_prefix_closes_as_forward_tuple (nested : Parser Expr) (opening : Token)
    (first second : Expr) (fuel : Nat) {input : State}
    {commaSpan closingSpan : SourceSpan} {afterComma after : Remainder}
    (comma : ExactTokenParses (.symbol .comma) input.declarativeRemainder commaSpan afterComma)
    (closing : ExactTokenParses (.symbol .rightParen) afterComma closingSpan after) :
    tupleTail nested opening (fuel + 1) [second, first] input = .ok
      { span := SourceSpan.cover opening.span closingSpan
        value := .tuple { span := SourceSpan.cover opening.span closingSpan, elements := [first, second] } }
      { input with cursor := input.cursor + 2 } :=
  trailing_close_bypasses_any_child nested opening [second, first] fuel comma closing

end Solcore.Test.SyntaxParenthesizedSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomCoreTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomCoreTotalityProperties

open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @expressionAtomCore_ordinary_of_elementFuel
example := @expressionAtomCore_ne_invariant_of_elementFuel
example := @expressionAtom_ordinary_of_elementFuel
example := @expressionAtom_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserExpressionAtomCoreTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomDelimitedFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomDelimitedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @optionalDotConstructorArguments_ordinary_of_elementFuel
example := @optionalDotConstructorArguments_ne_invariant_of_elementFuel
example := @dotConstructor_ordinary_of_elementFuel
example := @dotConstructor_ne_invariant_of_elementFuel
example := @arrayLiteral_ordinary_of_elementFuel
example := @arrayLiteral_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserExpressionAtomDelimitedFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomLeafTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomLeafTotalityProperties

open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example : ElementTotalityContract expressionName :=
  expressionName_elementTotalityContract

example : Parser.InvariantFreeOnValid literalExpression :=
  literalExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid identifierExpression :=
  identifierExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid proxyExpression :=
  proxyExpression_invariantFreeOnValid

example : Parser.InvariantFreeOnValid optionalLambdaReturnType :=
  optionalLambdaReturnType_invariantFreeOnValid

end Solcore.Test.SyntaxParserExpressionAtomLeafTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomProperties
/-! External consumers for canonical Core expression-atom contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax.Parser

example := @ExpressionAtomInternals.expressionName_validFor
example := @ExpressionAtomInternals.expressionName_preservesTokenWindow
example := @ExpressionAtomInternals.expressionName_preservesTokensOnSuccess
example := @ExpressionAtomInternals.expressionName_ok_state_shape
example := @ExpressionAtomInternals.expressionName_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.expressionName_cursor_lt_onSuccess
example := @ExpressionAtomInternals.expressionName_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.literalExpression_validFor
example := @ExpressionAtomInternals.literalExpression_preservesTokenWindow
example := @ExpressionAtomInternals.literalExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.literalExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.literalExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.identifierExpression_validFor
example := @ExpressionAtomInternals.identifierExpression_preservesTokenWindow
example := @ExpressionAtomInternals.identifierExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.identifierExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.identifierExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.proxyExpression_validFor
example := @ExpressionAtomInternals.proxyExpression_preservesTokenWindow
example := @ExpressionAtomInternals.proxyExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.proxyExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.proxyExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.dotConstructor_validFor
example := @ExpressionAtomInternals.dotConstructor_preservesTokenWindow
example := @ExpressionAtomInternals.dotConstructor_preservesTokensOnSuccess
example := @ExpressionAtomInternals.dotConstructor_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.dotConstructor_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.closeTuple_validFor
example := @ExpressionAtomInternals.closeTuple_preservesTokenWindow
example := @ExpressionAtomInternals.closeTuple_preservesTokensOnSuccess
example := @ExpressionAtomInternals.closeTuple_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.closeTuple_preservesOpeningStartOnSuccess
example := @ExpressionAtomInternals.closeTuple_endsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.closeTuple_endsAtLastConsumedTokenOnSuccess
example := @ExpressionAtomInternals.tupleTail_validFor
example := @ExpressionAtomInternals.tupleTail_preservesTokenWindow
example := @ExpressionAtomInternals.tupleTail_preservesTokensOnSuccess
example := @ExpressionAtomInternals.tupleTail_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.tupleTail_preservesOpeningStartOnSuccess
example := @ExpressionAtomInternals.tupleTail_endsAtLastConsumedTokenOnSuccess
example := @ExpressionAtomInternals.parenthesized_validFor
example := @ExpressionAtomInternals.parenthesized_preservesTokenWindow
example := @ExpressionAtomInternals.parenthesized_preservesTokensOnSuccess
example := @ExpressionAtomInternals.parenthesized_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.parenthesized_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.parenthesized_endsAtLastConsumedTokenOnSuccess
example := @ExpressionAtomInternals.arrayLiteral_validFor
example := @ExpressionAtomInternals.arrayLiteral_preservesTokenWindow
example := @ExpressionAtomInternals.arrayLiteral_preservesTokensOnSuccess
example := @ExpressionAtomInternals.arrayLiteral_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.arrayLiteral_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.arrayLiteral_retainsDelimitedEndOnSuccess
example := @ExpressionAtomInternals.optionalLambdaReturnType_validFor
example := @ExpressionAtomInternals.optionalLambdaReturnType_preservesTokenWindow
example := @ExpressionAtomInternals.optionalLambdaReturnType_preservesTokensOnSuccess
example := @ExpressionAtomInternals.optionalLambdaReturnType_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.optionalLambdaReturnType_some_startsAfterArrow
example := @ExpressionAtomInternals.lambdaExpression_preservesTokenWindow
example := @ExpressionAtomInternals.lambdaExpression_preservesTokensOnSuccess
example := @ExpressionAtomInternals.lambdaExpression_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.lambdaExpression_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.lambdaExpression_retainsBodyEndOnSuccess
example := @ExpressionAtomInternals.lambdaExpression_validFor
example := @ExpressionAtomInternals.expressionAtomCore_validFor
example := @ExpressionAtomInternals.finishRecoveredAtom_validFor
example := @ExpressionAtomInternals.recoverAtomAux_validFor
example := @ExpressionAtomInternals.recoverAtom_validFor
example := @ExpressionAtomInternals.expressionAtom_validFor
example := @ExpressionAtomInternals.expressionAtom_preservesTokenWindow
example := @ExpressionAtomInternals.expressionAtom_preservesTokensOnSuccess
example := @ExpressionAtomInternals.expressionAtom_cursorMonotoneOnSuccess
example := @ExpressionAtomInternals.expressionAtom_startsAtCurrentTokenOnSuccess
example := @ExpressionAtomInternals.literalExpression_cursor_lt_onSuccess
example := @ExpressionAtomInternals.identifierExpression_cursor_lt_onSuccess
example := @ExpressionAtomInternals.dotConstructor_cursor_lt_onSuccess
example := @ExpressionAtomInternals.proxyExpression_cursor_lt_onSuccess
example := @ExpressionAtomInternals.parenthesized_cursor_lt_onSuccess
example := @ExpressionAtomInternals.arrayLiteral_cursor_lt_onSuccess
example := @ExpressionAtomInternals.lambdaExpression_cursor_lt_onSuccess
example := @ExpressionAtomInternals.expressionAtomCore_cursor_lt_onSuccess
example := @ExpressionAtomInternals.recoverAtom_cursor_lt_onSuccess
example := @ExpressionAtomInternals.expressionAtom_cursor_lt_onSuccess
example := @ExpressionAtomInternals.expressionPostfix_cursor_lt_onSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomRecoveryTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @recoverAtomAux_exists_ok_of_remainingCount_lt
example := @recoverAtomAux_production_exists_ok
example := @recoverAtomAux_ne_invariant_of_remainingCount_lt
example : Parser.Ordinary recoverAtom := recoverAtom_ordinary
example := @recoverAtom_invariantFreeOnValid
example := @recoverAtom_ne_invariant

end Solcore.Test.SyntaxParserExpressionAtomRecoveryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserExpressionAtomTupleTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomTupleTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @closeTuple_invariantFreeOnValid
example := @tupleTail_ordinary_of_elementFuel
example := @tupleTail_ne_invariant_of_elementFuel
example := @tupleTail_production_ordinary_of_elementFuel
example := @tupleTail_production_ne_invariant_of_elementFuel
example := @parenthesized_ordinary_of_elementFuel
example := @parenthesized_ne_invariant_of_elementFuel

example (nested : Parser Expr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, parenthesized nested input = .ok value next) ∨
      (∃ failure next,
        parenthesized nested input = .reject failure next) :=
  parenthesized_ordinary_of_elementFuel nested nestedFuel contract input
    inputValid adequate

end Solcore.Test.SyntaxParserExpressionAtomTupleTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLiteralDiagnosticTraceProperties
/-! Real literal/Boolean leaves preserve exact payloads and distinct failures.
The real literal-expression contracts also close one nonempty return instance. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLiteralDiagnosticTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @coreLiteralTrace_outcome_total
example := @booleanIdentifierTrace_outcome_total
example := @CoreLiteralTraceRejects.disjoint_success
example := @BooleanIdentifierTraceRejects.disjoint_success
example := @literalExpression_trace_reject_sound
example := @literalExpression_trace_reject_complete

theorem decimal_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .decimalLiteral spelling }) :
    coreLiteral input = .ok { span, value := .decimal spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.decimal token)

theorem hexadecimal_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .hexadecimalLiteral spelling }) :
    coreLiteral input = .ok { span, value := .hexadecimal spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.hexadecimal token)

theorem string_keeps_spelling (spelling : String) {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .stringLiteral spelling }) :
    coreLiteral input = .ok { span, value := .string spelling }
      { input with cursor := input.cursor + 1 } :=
  coreLiteral_eq_ok_of_ordinary (.string token)

theorem true_keeps_identifier_shape {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .trueKw }) :
    booleanIdentifier input = .ok { span, value := "true" }
      { input with cursor := input.cursor + 1 } :=
  booleanIdentifier_eq_ok_of_ordinary (.trueKeyword token)

theorem false_keeps_identifier_shape {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .keyword .falseKw }) :
    booleanIdentifier input = .ok { span, value := "false" }
      { input with cursor := input.cursor + 1 } :=
  booleanIdentifier_eq_ok_of_ordinary (.falseKeyword token)

/-- The same offending semicolon has two different required expectations.
Both failures preserve every state field and leave their report uncommitted. -/
theorem same_token_retains_distinct_literal_and_boolean_expectations
    {input : State} {span : SourceSpan}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .semicolon }) :
    coreLiteral input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .coreLiteral, tail := [] }, context := .expression } input ∧
    booleanIdentifier input = .reject {
      span, found := some (.symbol .semicolon)
      expected := { head := .expression, tail := [] }, context := .expression } input := by
  have literalAbsent : CoreLiteralAbsentAt input.declarativeRemainder := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, spelling, current⟩; cases TokenAt.token_unique token current
  have booleanAbsent : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
    · rintro ⟨otherSpan, current⟩; cases TokenAt.token_unique token current
  have current : CurrentInputAt input.file.id input.window.endByte input.declarativeRemainder
      span (some (.symbol .semicolon)) :=
    .token (current := { span, value := .symbol .semicolon }) token
  exact ⟨(coreLiteral_trace_reject_failure_iff.mp
      ⟨.absent literalAbsent, .reported current, rfl⟩).1,
    (booleanIdentifier_trace_reject_failure_iff.mp
      ⟨booleanAbsent, rfl, .reported current, rfl⟩).1⟩

/-- No physical carrier token can be consumed beyond the active window. The
literal failure uses the explicit byte boundary, not a token past that window. -/
theorem window_end_literal_failure_keeps_full_state {input : State}
    (atEnd : input.window.endIndex ≤ input.cursor) :
    coreLiteral input = .reject {
      span := { source := input.file.id
                startByte := input.window.endByte
                endByte := input.window.endByte }
      found := none, expected := { head := .coreLiteral, tail := [] }, context := .expression
    } input := by
  have absent : CoreLiteralAbsentAt input.declarativeRemainder := by
    refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨span, spelling, inside, _⟩ <;>
      change input.cursor < input.window.endIndex at inside <;> omega
  exact (coreLiteral_trace_reject_failure_iff.mp
    ⟨.absent absent, .reported (.windowEnd atEnd), rfl⟩).1

/-- A nonempty return with the real literal-expression parser needs no abstract
expression contract from its caller; the literal and both marker spans survive. -/
theorem real_literal_return_keeps_prior_events
    {input : State} {afterMarker afterValue after : Remainder} {literal : CoreLiteral}
    {markerSpan semicolonSpan : SourceSpan}
    (marker : ExactTokenParses (.keyword .returnKw) input.declarativeRemainder markerSpan afterMarker)
    (valueParsed : CoreLiteralParses afterMarker literal afterValue)
    (semicolon : ExactTokenParses (.symbol .semicolon) afterValue semicolonSpan after) :
    ∃ output, returnStatement literalExpression input = .ok {
        span := SourceSpan.cover markerSpan semicolonSpan
        value := .returnStmt (some { span := literal.span, value := .literal literal })
      } output ∧ output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics := by
  have notSemicolon : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
      afterMarker.cursor (.symbol .semicolon) := by
    rintro ⟨span, current⟩
    cases valueParsed with
    | decimal token => cases TokenAt.token_unique token current
    | hexadecimal token => cases TokenAt.token_unique token current
    | string token => cases TokenAt.token_unique token current
  simpa only [List.append_nil] using
    returnStatement_trace_success_complete literalExpression_trace_success_complete
      (.parsed markerSpan semicolonSpan marker
        (.present notSemicolon ⟨.parsed valueParsed, rfl⟩) semicolon)

end Solcore.Test.SyntaxParserLiteralDiagnosticTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLiteralProperties
/-! External consumers for canonical literal parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example : coreLiteral.ValidFor Located.ValidFor :=
  coreLiteral_validFor

example : booleanIdentifier.ValidFor Located.ValidFor :=
  booleanIdentifier_validFor

example : Parser.PreservesTokenWindow coreLiteral :=
  coreLiteral_preservesTokenWindow

example : Parser.PreservesTokenWindow booleanIdentifier :=
  booleanIdentifier_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess coreLiteral :=
  coreLiteral_preservesTokensOnSuccess

example : Parser.PreservesTokensOnSuccess booleanIdentifier :=
  booleanIdentifier_preservesTokensOnSuccess

example := @coreLiteral_cursor_lt_onSuccess
example := @booleanIdentifier_cursor_lt_onSuccess

example : Parser.CursorMonotoneOnSuccess coreLiteral :=
  coreLiteral_cursorMonotoneOnSuccess

example : Parser.CursorMonotoneOnSuccess booleanIdentifier :=
  booleanIdentifier_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess coreLiteral (·.span) :=
  coreLiteral_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess booleanIdentifier (·.span) :=
  booleanIdentifier_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLiteralTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLiteralTotalityProperties

open Solcore.Syntax.Parser

example : Parser.Ordinary coreLiteral :=
  coreLiteral_ordinary

example : Parser.Ordinary booleanIdentifier :=
  booleanIdentifier_ordinary

example : ElementTotalityContract coreLiteral :=
  coreLiteral_elementTotalityContract

example : ElementTotalityContract booleanIdentifier :=
  booleanIdentifier_elementTotalityContract

end Solcore.Test.SyntaxParserLiteralTotalityProperties
end
