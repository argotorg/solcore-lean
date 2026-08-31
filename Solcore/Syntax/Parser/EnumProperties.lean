import Solcore.Syntax.Parser.Enum
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.TypeDeclarationValidity

/-! Provenance and carrier contracts for canonical enum parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace EnumInternals

private theorem enumBind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem getState_preservesTokenWindowForEnum :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

/-- Optional constructor fields preserve delimiters and recursive types. -/
theorem enumConstructorFields_validFor :
    enumConstructorFields.ValidFor
      (Option.ValidFor (DelimitedList.ValidFor TypeExpr.ValidFor)) := by
  unfold enumConstructorFields
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (delimitedNoTrailing_validFor TypeExpr.ValidFor .leftParen .rightParen
        true typeExpr .typeExpr .topLevel typeExpr_validFor
        typeExpr_preservesTokensOnSuccess)
    intro fields input inputValid fieldsValid
    exact ⟨by simpa only [Option.ValidFor] using fieldsValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional constructor fields preserve every ordinary token window. -/
theorem enumConstructorFields_preservesTokenWindow :
    Parser.PreservesTokenWindow enumConstructorFields := by
  unfold enumConstructorFields
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindowForEnum
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen true
        false typeExpr .typeExpr .topLevel typeExpr_preservesTokenWindow)
    intro fields
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem enumConstructorFields_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess enumConstructorFields :=
  enumConstructorFields_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional constructor fields never rewind the parser cursor. -/
theorem enumConstructorFields_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess enumConstructorFields := by
  unfold enumConstructorFields
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen .rightParen true
        typeExpr .typeExpr .topLevel)
    intro fields
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- Present constructor fields start at the current `(` token. -/
theorem enumConstructorFields_some_startsAtCurrentTokenOnSuccess
    {input next : State} {fields : DelimitedList TypeExpr}
    (result : enumConstructorFields input = .ok (some fields) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = fields.span.startByte := by
  unfold enumConstructorFields getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    rcases enumBind_ok_components result with
      ⟨parsed, afterParsed, parsedResult, finished⟩
    have starts := delimitedNoTrailing_startsAtCurrentTokenOnSuccess .leftParen
      .rightParen true typeExpr .typeExpr .topLevel input parsed afterParsed
      parsedResult
    cases finished
    exact starts
  · simp only [present] at result
    change Reply.ok none input = .ok (some fields) next at result
    cases result

/-- One constructor retains its name, payload, and complete source range. -/
theorem enumConstructor_validFor :
    enumConstructor.ValidFor EnumConstructor.ValidFor := by
  have weak : enumConstructor.ValidFor (fun _ _ => True) := by
    unfold enumConstructor
    apply Parser.bind_validFor (identifier_validFor .topItem)
    intro name
    apply Parser.bind_validFor enumConstructorFields_validFor
    intro fields
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : enumConstructor input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok constructor final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold enumConstructor at stages
      rcases enumBind_ok_components stages with
        ⟨name, afterName, nameResult, rest⟩
      rcases enumBind_ok_components rest with
        ⟨fields, afterFields, fieldsResult, finished⟩
      have nameValid := identifier_validFor .topItem input inputValid
      rw [nameResult] at nameValid
      have fieldsValid := enumConstructorFields_validFor afterName nameValid.2.1
      rw [fieldsResult] at fieldsValid
      have nameSpanValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using nameValid.1
      have fieldsValidInput : Option.ValidFor
          (DelimitedList.ValidFor TypeExpr.ValidFor) input.file fields := by
        simpa [nameValid.2.2] using fieldsValid.1
      cases fields with
      | none =>
          have outerValid := SourceSpan.cover_validFor nameSpanValid
            nameSpanValid nameSpanValid.2.1
          cases finished
          exact ⟨⟨outerValid, by simp, nameSpanValid, by simp, by simp⟩,
            weakResult.2.1, weakResult.2.2⟩
      | some values =>
          have valuesValid : DelimitedList.ValidFor TypeExpr.ValidFor
              input.file values := by
            simpa only [Option.ValidFor] using fieldsValidInput
          rcases identifier_ok_state_shape .topItem nameResult with
            ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
          rcases enumConstructorFields_some_startsAtCurrentTokenOnSuccess
              fieldsResult with ⟨opening, openingFound, fieldsStart⟩
          have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
          have openingAt : input.tokens[afterName.cursor]? = some opening := by
            simpa [nameTokens] using
              State.getElem?_eq_some_of_peek?_eq_some openingFound
          have nameBeforeFields : name.span.endByte ≤ values.span.startByte := by
            rw [← fieldsStart]
            have ordered := inputValid.token_end_le_token_start_of_getElem?_lt
              nameAt openingAt (by omega)
            simpa [nameSpan] using ordered
          have outerValid := SourceSpan.cover_validFor nameSpanValid
            valuesValid.1 (Nat.le_trans nameSpanValid.2.1
              (Nat.le_trans nameBeforeFields valuesValid.1.2.1))
          cases finished
          refine ⟨⟨outerValid, by simp, nameSpanValid, ?_, ?_⟩,
            weakResult.2.1, weakResult.2.2⟩
          · intro retained member
            have retainedEq : retained = values := by simpa using member.symm
            simpa [retainedEq] using valuesValid.1
          · intro retained member field fieldMember
            have retainedEq : retained = values := by simpa using member.symm
            subst retained
            exact valuesValid.2 field fieldMember

/-- Constructor parsing preserves every ordinary token window. -/
theorem enumConstructor_preservesTokenWindow :
    Parser.PreservesTokenWindow enumConstructor := by
  unfold enumConstructor
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow
    enumConstructorFields_preservesTokenWindow
  intro fields
  exact Parser.pure_preservesTokenWindow _

theorem enumConstructor_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess enumConstructor :=
  enumConstructor_preservesTokenWindow.preservesTokensOnSuccess

/-- Constructor parsing never rewinds the parser cursor. -/
theorem enumConstructor_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess enumConstructor := by
  unfold enumConstructor
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    enumConstructorFields_cursorMonotoneOnSuccess
  intro fields
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A constructor starts at its ordinary identifier token. -/
theorem enumConstructor_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess enumConstructor (·.span) := by
  intro input constructor final parsed
  unfold enumConstructor at parsed
  rcases enumBind_ok_components parsed with
    ⟨name, afterName, nameResult, rest⟩
  rcases enumBind_ok_components rest with
    ⟨fields, afterFields, _fieldsResult, finished⟩
  rcases identifier_ok_state_shape .topItem nameResult with
    ⟨token, found, tokenSpan, _tokens, _cursor⟩
  cases finished
  exact ⟨token, found, by simp [SourceSpan.cover, tokenSpan]⟩

end EnumInternals
end Solcore.Syntax.Parser
