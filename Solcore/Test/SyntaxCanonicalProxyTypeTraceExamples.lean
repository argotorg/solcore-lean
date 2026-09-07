import Solcore.Syntax.Parser.ProxyTypeSuccessTraceProperties
import Solcore.Syntax.Parser.ProxyTypeRejectionTraceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

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
