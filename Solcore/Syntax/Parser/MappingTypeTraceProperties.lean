import Solcore.Syntax.DeclarativeMappingTypeTraceProperties
import Solcore.Syntax.Parser.DiagnosticTraceContracts
import Solcore.Syntax.Parser.ExactTokenPrimitiveSuccessTraceProperties
import Solcore.Syntax.Parser.Type

/-! Raw mapping execution preserves every located AST component and the
ordered key/value event suffix. Contextual mapping remains an identifier
token, and no progress, validity, or token-carrier child law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

variable {nested : Parser TypeExpr}
  {elementTrace : SourceId → Nat → DeclarativeGrammar.Remainder → TypeExpr →
    DeclarativeGrammar.Remainder → List ParseDiagnostic → Prop}

private theorem mapping_bind_ok_parts {α β : Type} {first : Parser α} {next : α → Parser β}
    {input output : State} {value : β} (result : (first >>= next) input = .ok value output) :
    ∃ item after, first input = .ok item after ∧ next item after = .ok value output := by
  cases firstResult : first input <;> simp only [bind, firstResult] at result
  case ok item after => exact ⟨item, after, rfl, result⟩
  case reject => contradiction
  case invariant => contradiction

theorem parseMappingType_success_iff_components {input output : State} {resultValue : TypeExpr} :
    parseMappingType nested input = .ok resultValue output ↔
    ∃ marker afterMarker opening afterOpening key afterKey arrow afterArrow value afterValue closing,
      contextual .mapping .typeExpr input = .ok marker afterMarker ∧
      symbol .leftParen .typeExpr afterMarker = .ok opening afterOpening ∧
      nested afterOpening = .ok key afterKey ∧
      symbol .fatArrow .typeExpr afterKey = .ok arrow afterArrow ∧
      nested afterArrow = .ok value afterValue ∧
      symbol .rightParen .typeExpr afterValue = .ok closing output ∧
      resultValue = DeclarativeGrammar.mappingTypeTraceValue marker.span opening.span closing.span key value := by
  constructor
  · intro result
    unfold parseMappingType at result
    rcases mapping_bind_ok_parts result with ⟨marker, afterMarker, markerResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨opening, afterOpening, openingResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨key, afterKey, keyResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨arrow, afterArrow, arrowResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨value, afterValue, valueResult, rest⟩
    rcases mapping_bind_ok_parts rest with ⟨closing, afterClosing, closingResult, finished⟩
    cases finished
    exact ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
  · rintro ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
    simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult,
      closingResult, pure, DeclarativeGrammar.mappingTypeTraceValue]

theorem parseMappingType_trace_success_sound
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessSound (parseMappingType nested) (DeclarativeGrammar.MappingTypeTraceParses elementTrace) := by
  intro input output resultValue result
  rcases parseMappingType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩
  have markerParsed := contextual_success_exactTokenParses .mapping .typeExpr markerResult
  have openingParsed := symbol_success_exactTokenParses .leftParen .typeExpr openingResult
  have arrowParsed := symbol_success_exactTokenParses .fatArrow .typeExpr arrowResult
  have closingParsed := symbol_success_exactTokenParses .rightParen .typeExpr closingResult
  have markerState := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
  have arrowState := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
  have closingState := (symbol_ok_tokenAt .rightParen .typeExpr closingResult).2
  subst afterMarker afterOpening afterArrow output
  rcases successSound keyResult with ⟨keyEvents, keyParsed, keyEq⟩
  have keyFrame := contextFrame keyResult
  rcases successSound valueResult with ⟨valueEvents, valueParsed, valueEq⟩
  refine ⟨keyEvents ++ valueEvents,
    .parsed marker.span opening.span arrow.span closing.span markerParsed openingParsed keyParsed
      arrowParsed (by simpa only [keyFrame.1, keyFrame.2] using valueParsed) closingParsed, ?_⟩
  change afterValue.diagnostics = input.diagnostics ++ (keyEvents ++ valueEvents)
  change afterValue.diagnostics = afterKey.diagnostics ++ valueEvents at valueEq
  change afterKey.diagnostics = input.diagnostics ++ keyEvents at keyEq
  rw [valueEq, keyEq]
  exact List.append_assoc _ _ _

theorem parseMappingType_trace_success_complete
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested) :
    ParserTraceSuccessComplete (parseMappingType nested) (DeclarativeGrammar.MappingTypeTraceParses elementTrace) := by
  intro input resultValue after trace parsed
  cases parsed with
  | parsed markerSpan openingSpan arrowSpan closingSpan marker opening key arrow value closing =>
      rename_i afterMarker afterOpening afterKey afterArrow afterValue keyValue valueValue keyEvents valueEvents
      have markerResult := contextual_eq_ok_of_exactTokenParses .mapping .typeExpr marker
      rcases marker with ⟨_, rfl⟩
      have openingResult := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
        (input := { input with cursor := input.cursor + 1 }) opening
      rcases opening with ⟨_, rfl⟩
      rcases successComplete (input := { input with cursor := input.cursor + 2 }) key with
        ⟨afterKeyState, keyResult, afterKeyEq, keyEq⟩
      have keyFrame := contextFrame keyResult
      have arrowAtKey : DeclarativeGrammar.ExactTokenParses (.symbol .fatArrow)
          afterKeyState.declarativeRemainder arrowSpan afterArrow := by simpa only [afterKeyEq] using arrow
      have arrowResult := symbol_eq_ok_of_exactTokenParses .fatArrow .typeExpr arrowAtKey
      have valueAtArrow : elementTrace afterKeyState.file.id afterKeyState.window.endByte
          ({ afterKeyState with cursor := afterKeyState.cursor + 1 } : State).declarativeRemainder
          valueValue afterValue valueEvents := by
        rw [arrow.2] at value
        simpa only [keyFrame.1, keyFrame.2, State.declarativeRemainder, ← afterKeyEq] using value
      rcases successComplete (input := { afterKeyState with cursor := afterKeyState.cursor + 1 }) valueAtArrow with
        ⟨afterValueState, valueResult, afterValueEq, valueEq⟩
      have closingAtValue : DeclarativeGrammar.ExactTokenParses (.symbol .rightParen)
          afterValueState.declarativeRemainder closingSpan after := by simpa only [afterValueEq] using closing
      have closingResult := symbol_eq_ok_of_exactTokenParses .rightParen .typeExpr closingAtValue
      refine ⟨{ afterValueState with cursor := afterValueState.cursor + 1 },
        parseMappingType_success_iff_components.mpr ⟨_, _, _, _, _, _, _, _, _, _, _,
          markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, rfl⟩,
        closingAtValue.2.symm, ?_⟩
      change afterValueState.diagnostics = input.diagnostics ++ (keyEvents ++ valueEvents)
      change afterValueState.diagnostics = afterKeyState.diagnostics ++ valueEvents at valueEq
      change afterKeyState.diagnostics = input.diagnostics ++ keyEvents at keyEq
      rw [valueEq, keyEq]
      exact List.append_assoc _ _ _

theorem parseMappingType_success_context
    (contextFrame : ParserSuccessContext nested) : ParserSuccessContext (parseMappingType nested) := by
  intro input output resultValue result
  rcases parseMappingType_success_iff_components.mp result with
    ⟨marker, afterMarker, opening, afterOpening, key, afterKey, arrow, afterArrow, value, afterValue,
      closing, markerResult, openingResult, keyResult, arrowResult, valueResult, closingResult, _⟩
  have markerState := (contextual_ok_tokenAt .mapping .typeExpr markerResult).2
  have openingState := (symbol_ok_tokenAt .leftParen .typeExpr openingResult).2
  have arrowState := (symbol_ok_tokenAt .fatArrow .typeExpr arrowResult).2
  have closingState := (symbol_ok_tokenAt .rightParen .typeExpr closingResult).2
  subst afterMarker afterOpening afterArrow output
  have keyFrame := contextFrame keyResult
  have valueFrame := contextFrame valueResult
  exact ⟨valueFrame.1.trans keyFrame.1, valueFrame.2.trans keyFrame.2⟩

theorem parseMappingType_trace_success_iff
    (successSound : ParserTraceSuccessSound nested elementTrace)
    (successComplete : ParserTraceSuccessComplete nested elementTrace)
    (contextFrame : ParserSuccessContext nested)
    {input : State} {value : TypeExpr} {after : DeclarativeGrammar.Remainder} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.MappingTypeTraceParses elementTrace input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
    ∃ output, parseMappingType nested input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact parseMappingType_trace_success_complete successComplete contextFrame
  · rintro ⟨output, result, afterEq, diagnostics⟩
    rcases parseMappingType_trace_success_sound successSound contextFrame result with ⟨actualTrace, parsed, actualEq⟩
    have events := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, events] using parsed

end Solcore.Syntax.Parser
