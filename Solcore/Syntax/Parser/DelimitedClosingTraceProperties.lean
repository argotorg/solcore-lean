import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceGrammar
import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties

/-! Silent exact closing and the two guards used by delimited trace proofs. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace DelimitedTraceInternals

theorem symbol_present (value : Symbol) {input : State} {span : SourceSpan}
    {after : DeclarativeGrammar.Remainder}
    (parsed : DeclarativeGrammar.ExactTokenParses (.symbol value)
      input.declarativeRemainder span after) : isSymbol input value = true := by
  have token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := parsed.1
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

theorem symbol_absent (value : Symbol) {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol value)) : isSymbol input value = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true value .expression present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt value .expression result).1⟩

theorem preferredCloseNotTaken_of_guard_false (closing : Symbol) (allowClose : Bool)
    {input : State} (guard : (allowClose && isSymbol input closing) = false) :
    DeclarativeGrammar.PreferredCloseNotTaken closing allowClose input.declarativeRemainder := by
  cases allowClose with
  | false => exact .disabled
  | true => exact .absent (symbolAbsentAt_of_isSymbol_eq_false closing (by simpa using guard))

theorem guard_false_of_preferredCloseNotTaken (closing : Symbol) (allowClose : Bool)
    {input : State}
    (continues : DeclarativeGrammar.PreferredCloseNotTaken closing allowClose
      input.declarativeRemainder) : (allowClose && isSymbol input closing) = false := by
  cases continues with
  | disabled => rfl
  | absent absent => simpa only [Bool.true_and] using symbol_absent closing absent

end DelimitedTraceInternals

theorem closeDelimited_success_trace_sound {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input output : State} {values : DelimitedList α}
    (result : closeDelimited opening closing context elementsRev input = .ok values output) :
    ∃ closingSpan,
      DeclarativeGrammar.ExactTokenParses (.symbol closing) input.declarativeRemainder
        closingSpan output.declarativeRemainder ∧
      values = { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse } ∧
      output = { input with cursor := input.cursor + 1 } := by
  unfold closeDelimited at result
  cases closingResult : symbol closing context input with
  | invariant error => simp [closingResult] at result
  | reject failure rejected => simp [closingResult] at result
  | ok token next =>
      simp only [closingResult] at result
      cases result
      exact ⟨token.span, symbol_success_exactTokenParses closing context closingResult,
        rfl, (symbol_ok_tokenAt closing context closingResult).2⟩

theorem closeDelimited_trace_success_iff {α : Type}
    (opening : Token) (closing : Symbol) (context : ParseContext) (elementsRev : List α)
    {input : State} {values : DelimitedList α} {after : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    ((∃ closingSpan, DeclarativeGrammar.ExactTokenParses (.symbol closing)
      input.declarativeRemainder closingSpan after ∧
      values = { span := SourceSpan.cover opening.span closingSpan, elements := elementsRev.reverse }) ∧
      trace = []) ↔
    ∃ output, closeDelimited opening closing context elementsRev input = .ok values output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, parsed, rfl⟩, rfl⟩
    have result := symbol_eq_ok_of_exactTokenParses closing context parsed
    refine ⟨{ input with cursor := input.cursor + 1 },
      by simp only [closeDelimited, result], parsed.2.symm, ?_⟩
    simp only [State.diagnostics, List.append_nil]
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases closeDelimited_success_trace_sound opening closing context elementsRev result with
      ⟨closingSpan, parsed, valuesEq, stateEq⟩
    refine ⟨⟨closingSpan, afterEq ▸ parsed, valuesEq⟩, ?_⟩
    rw [stateEq] at diagnostics
    have : input.diagnostics ++ [] = input.diagnostics ++ trace := by
      simpa only [State.diagnostics, List.append_nil] using diagnostics
    exact (List.append_cancel_left this).symm

end Solcore.Syntax.Parser
