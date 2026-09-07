import Solcore.Syntax.Parser.TypeSuccessContextProperties
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

/-! Full source/window framing composes with the existing token-carrier law on
arbitrary inputs. A deliberately noncanonical carrier checks that no validity
or lexical provenance premise has slipped into the new contract. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeSuccessContextProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

theorem fuel_success_preserves_full_frame (fuel : Nat)
    {input output : State} {value : TypeExpr}
    (result : typeExprWithFuel fuel input = .ok value output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧ output.window = input.window := by
  have frame := typeExprWithFuel_success_context fuel result
  exact ⟨frame.1, typeExprWithFuel_preservesTokensOnSuccess fuel input value output result, frame.2⟩

theorem production_success_preserves_full_frame
    {input output : State} {value : TypeExpr} (result : typeExpr input = .ok value output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧ output.window = input.window := by
  have frame := typeExpr_success_context result
  exact ⟨frame.1, typeExpr_preservesTokensOnSuccess input value output result, frame.2⟩

private def source : SourceId := { origin := .main, path := "noncanonical-type-context.sol" }
private def name : Identifier := {
  span := { source, startByte := 10, endByte := 13 }, value := "a-b"
}
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }
  tokens := #[{ span := name.span, value := .identifier name.value }]
  cursor := 0
  window := { endIndex := 9, endByte := 0 }
  diagnosticsRev := prior.reverse
}
private def output (prior : List ParseDiagnostic) : State := {
  input prior with cursor := 1, diagnosticsRev := event :: prior.reverse
}

theorem noncanonical_window_keeps_source_and_window (prior : List ParseDiagnostic) :
    (input prior).tokens.size < (input prior).window.endIndex ∧
    typeExpr (input prior) = .ok (namedTypeTraceValue (tracedQualifiedName name []) none) (output prior) ∧
    (output prior).file = (input prior).file ∧ (output prior).window = (input prior).window ∧
    (output prior).diagnostics = prior ++ [event] := by
  have result := checked_name_type (input := input prior) (name := name) (trace := [event])
    ⟨by change 0 < 9; decide, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
    (by simp [TokenKindAbsentAt, TokenAt, input])
    (by simp [TokenKindAbsentAt, TokenAt, input])
    (by decide) (by decide)
  have frame := typeExpr_success_context result
  refine ⟨by change 1 < 9; decide, result, frame.1, frame.2, ?_⟩
  simp only [output, State.diagnostics, List.reverse_cons, input, List.reverse_reverse]

end Solcore.Test.SyntaxTypeSuccessContextProperties
