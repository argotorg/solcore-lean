import Solcore.Syntax.Parser.ProxyExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.Type
import Solcore.Syntax.Lexer

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
