import Solcore.Test.SyntaxMappingTypeTraceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

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
