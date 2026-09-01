import Solcore.Syntax.Parser.EnumProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Valid-input totality for canonical enum constructors. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace EnumInternals

private theorem bind_cursor_lt_of_first {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    (firstStrict : ∀ {input middle : State} {value : alpha},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value,
      Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  change (match first input with
    | .ok firstValue middle => next firstValue middle
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [firstResult] at parsed
  | invariant error => simp [firstResult] at parsed

/-- Optional enum payloads inherit public type-parser totality. -/
theorem enumConstructorFields_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ fields next, enumConstructorFields input = .ok fields next) ∨
      (∃ failure next,
        enumConstructorFields input = .reject failure next) := by
  unfold enumConstructorFields
  simp only [getState, bind]
  split
  · rcases delimitedNoTrailing_ordinary .leftParen .rightParen true typeExpr
        .typeExpr .topLevel typeExpr_elementTotalityContract input inputValid with
      ⟨fields, next, fieldsResult⟩ |
      ⟨failure, rejected, fieldsResult⟩
    · exact Or.inl ⟨some fields, next, by
        simp only [fieldsResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [fieldsResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

theorem enumConstructorFields_invariantFreeOnValid :
    Parser.InvariantFreeOnValid enumConstructorFields :=
  enumConstructorFields_ordinary

/-- A constructor name and its optional payload have only ordinary outcomes. -/
theorem enumConstructor_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ constructor next, enumConstructor input = .ok constructor next) ∨
      (∃ failure next, enumConstructor input = .reject failure next) := by
  rcases (identifier_ordinary .topItem) input with
    ⟨name, afterName, nameResult⟩ |
    ⟨failure, rejected, nameResult⟩
  · have nameReply := identifier_validFor .topItem input inputValid
    rw [nameResult] at nameReply
    rcases enumConstructorFields_ordinary afterName nameReply.2.1 with
      ⟨fields, final, fieldsResult⟩ |
      ⟨failure, rejected, fieldsResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover name.span
            (fields.map (fun values => values.span) |>.getD name.span)
          value := { leadingComments := [], name, fields }
        }, final, by
          simp only [enumConstructor, bind, nameResult, fieldsResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [enumConstructor, bind, nameResult, fieldsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [enumConstructor, bind, nameResult]⟩

theorem enumConstructor_invariantFreeOnValid :
    Parser.InvariantFreeOnValid enumConstructor :=
  enumConstructor_ordinary

/-- Every successful constructor consumes its leading identifier. -/
theorem enumConstructor_cursor_lt_onSuccess
    {input final : State} {value : EnumConstructor}
    (parsed : enumConstructor input = .ok value final) :
    input.cursor < final.cursor := by
  unfold enumConstructor at parsed
  apply bind_cursor_lt_of_first
    (identifier_elementTotalityContract .topItem).cursorLtOnSuccess ?_ parsed
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    enumConstructorFields_cursorMonotoneOnSuccess
  intro fields
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Enum constructors can drive the body parser's progress-checked loop. -/
theorem enumConstructor_elementTotalityContract :
    ElementTotalityContract enumConstructor := {
  validFor := enumConstructor_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := enumConstructor_preservesTokenWindow
  cursorLtOnSuccess := enumConstructor_cursor_lt_onSuccess
  invariantFree := enumConstructor_invariantFreeOnValid.ne_invariant
}

end EnumInternals
end Solcore.Syntax.Parser
