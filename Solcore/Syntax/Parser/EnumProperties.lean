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

namespace EnumBody

/-- An enum body retains a valid brace range and valid constructors. -/
def ValidFor (file : SourceFile) (body : EnumBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor EnumConstructor.ValidFor file body.constructors

end EnumBody

/-- Closing a body preserves its brace range and reversed constructor list. -/
theorem closeEnumBody_validFor (opening : Token)
    (constructorsRev : List EnumConstructor) {input : State}
    {openingIndex : Nat} (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (constructorsValid : List.ValidFor EnumConstructor.ValidFor input.file
      constructorsRev) :
    (closeEnumBody opening constructorsRev input).ValidFor input
      EnumBody.ValidFor := by
  unfold closeEnumBody
  simp only [bind]
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .rightBrace .topItem input inputValid
      rw [closingResult] at valid
      exact valid
  | ok closing afterClosing =>
      have closingValid := symbol_validFor .rightBrace .topItem input inputValid
      rw [closingResult] at closingValid
      have closingShape := symbol_ok_state_shape .rightBrace .topItem
        closingResult
      have closingFound :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingValid.1
      have openingBeforeClosing :=
        inputValid.token_end_le_token_start_of_getElem?_lt openingFound
          closingFound openingBefore
      have outerValid := SourceSpan.cover_validFor openingValid closingSpanValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1))
      exact ⟨⟨outerValid, by
          intro constructor member
          exact constructorsValid constructor (by simpa using member)⟩,
        closingValid.2.1, closingValid.2.2⟩

/-- Closing a body preserves every ordinary token window. -/
theorem closeEnumBody_preservesTokenWindow (opening : Token)
    (constructorsRev : List EnumConstructor) :
    Parser.PreservesTokenWindow (closeEnumBody opening constructorsRev) := by
  unfold closeEnumBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

theorem closeEnumBody_preservesTokensOnSuccess (opening : Token)
    (constructorsRev : List EnumConstructor) :
    Parser.PreservesTokensOnSuccess (closeEnumBody opening constructorsRev) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (closeEnumBody_preservesTokenWindow opening constructorsRev)

/-- Closing a body advances monotonically through its `}` token. -/
theorem closeEnumBody_cursorMonotoneOnSuccess (opening : Token)
    (constructorsRev : List EnumConstructor) :
    Parser.CursorMonotoneOnSuccess (closeEnumBody opening constructorsRev) := by
  unfold closeEnumBody
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .rightBrace .topItem)
  intro closing
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Closing retains the opening brace as the body's starting endpoint. -/
theorem closeEnumBody_preservesOpeningStartOnSuccess (opening : Token)
    (constructorsRev : List EnumConstructor) {input final : State}
    {body : EnumBody} (parsed : closeEnumBody opening constructorsRev input =
      .ok body final) :
    body.span.startByte = opening.span.startByte := by
  unfold closeEnumBody at parsed
  rcases enumBind_ok_components parsed with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases finished
  rfl

/-- The body endpoint is the current closing-brace token. -/
theorem closeEnumBody_endsAtCurrentTokenOnSuccess (opening : Token)
    (constructorsRev : List EnumConstructor) {input final : State}
    {body : EnumBody} (parsed : closeEnumBody opening constructorsRev input =
      .ok body final) :
    ∃ closing, input.peek? = some closing ∧
      closing.span.endByte = body.span.endByte := by
  unfold closeEnumBody at parsed
  rcases enumBind_ok_components parsed with
    ⟨closing, afterClosing, closingResult, finished⟩
  have found := (symbol_ok_state_shape .rightBrace .topItem closingResult).1
  cases finished
  exact ⟨closing, found, rfl⟩

/-- The constructor loop preserves its opening brace and accumulated cases. -/
theorem enumConstructors_validFor (opening : Token) :
    ∀ fuel constructorsRev input openingIndex,
      input.ValidFor →
      input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor EnumConstructor.ValidFor input.file constructorsRev →
      (enumConstructors opening fuel constructorsRev input).ValidFor input
        EnumBody.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro constructorsRev input openingIndex inputValid openingFound
        openingBefore constructorsValid
      unfold enumConstructors
      split
      · cases commaResult : symbol .comma .topItem input with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := symbol_validFor .comma .topItem input inputValid
            rw [commaResult] at valid
            exact valid
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma .topItem input inputValid
            rw [commaResult] at commaValid
            have commaShape := symbol_ok_state_shape .comma .topItem commaResult
            have openingFoundAfter :
                afterComma.tokens[openingIndex]? = some opening := by
              simpa [commaShape.2] using openingFound
            have openingBeforeAfter : openingIndex < afterComma.cursor := by
              simpa [commaShape.2] using Nat.lt_succ_of_lt openingBefore
            have constructorsValidAfter : List.ValidFor
                EnumConstructor.ValidFor afterComma.file constructorsRev := by
              simpa [commaValid.2.2] using constructorsValid
            simp only
            split
            · exact (closeEnumBody_validFor opening constructorsRev
                commaValid.2.1 openingFoundAfter openingBeforeAfter
                constructorsValidAfter).of_file_eq commaValid.2.2
            · cases constructorResult : enumConstructor afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  have valid := enumConstructor_validFor afterComma
                    commaValid.2.1
                  rw [constructorResult] at valid
                  exact valid.of_file_eq commaValid.2.2
              | ok constructor next =>
                  have constructorValid := enumConstructor_validFor afterComma
                    commaValid.2.1
                  rw [constructorResult] at constructorValid
                  simp only
                  split
                  · have openingFoundNext :
                        next.tokens[openingIndex]? = some opening := by
                      simpa [enumConstructor_preservesTokensOnSuccess afterComma
                        constructor next constructorResult] using
                        openingFoundAfter
                    have accumulatedValid : List.ValidFor
                        EnumConstructor.ValidFor next.file
                        (constructor :: constructorsRev) := by
                      intro retained member
                      rcases List.mem_cons.mp member with rfl | member
                      · simpa [constructorValid.2.2] using constructorValid.1
                      · simpa [constructorValid.2.2] using
                          constructorsValidAfter retained member
                    exact (inductionHypothesis (constructor :: constructorsRev)
                      next openingIndex constructorValid.2.1 openingFoundNext
                      (by omega) accumulatedValid).of_file_eq
                        (constructorValid.2.2.trans commaValid.2.2)
                  · trivial
      · exact closeEnumBody_validFor opening constructorsRev inputValid
          openingFound openingBefore constructorsValid

/-- The constructor loop preserves every ordinary token window. -/
theorem enumConstructors_preservesTokenWindow (opening : Token) :
    ∀ fuel constructorsRev,
      Parser.PreservesTokenWindow
        (enumConstructors opening fuel constructorsRev) := by
  intro fuel
  induction fuel with
  | zero => intros constructorsRev input; trivial
  | succ fuel inductionHypothesis =>
      intro constructorsRev input
      unfold enumConstructors
      split
      · have commaShape := symbol_preservesTokenWindow .comma .topItem input
        cases commaResult : symbol .comma .topItem input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [commaResult] at commaShape
            exact commaShape
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            simp only
            split
            · exact (closeEnumBody_preservesTokenWindow opening
                constructorsRev afterComma).trans commaShape
            · have constructorShape :=
                  enumConstructor_preservesTokenWindow afterComma
              cases constructorResult : enumConstructor afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  rw [constructorResult] at constructorShape
                  exact constructorShape.trans commaShape
              | ok constructor next =>
                  rw [constructorResult] at constructorShape
                  simp only
                  split
                  · exact (inductionHypothesis (constructor :: constructorsRev)
                      next).trans (constructorShape.trans commaShape)
                  · trivial
      · exact closeEnumBody_preservesTokenWindow opening constructorsRev input

theorem enumConstructors_preservesTokensOnSuccess (opening : Token)
    (fuel : Nat) (constructorsRev : List EnumConstructor) :
    Parser.PreservesTokensOnSuccess
      (enumConstructors opening fuel constructorsRev) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (enumConstructors_preservesTokenWindow opening fuel constructorsRev)

/-- The constructor loop never rewinds its parser cursor. -/
theorem enumConstructors_cursorMonotoneOnSuccess (opening : Token) :
    ∀ fuel constructorsRev,
      Parser.CursorMonotoneOnSuccess
        (enumConstructors opening fuel constructorsRev) := by
  intro fuel
  induction fuel with
  | zero => intros constructorsRev input body final parsed; contradiction
  | succ fuel inductionHypothesis =>
      intro constructorsRev input body final parsed
      unfold enumConstructors at parsed
      split at parsed
      · cases commaResult : symbol .comma .topItem input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            have commaMonotone := symbol_cursorMonotoneOnSuccess .comma
              .topItem input comma afterComma commaResult
            split at parsed
            · exact Nat.le_trans commaMonotone
                (closeEnumBody_cursorMonotoneOnSuccess opening constructorsRev
                  afterComma body final parsed)
            · cases constructorResult : enumConstructor afterComma with
              | invariant error => simp [constructorResult] at parsed
              | reject failure rejected => simp [constructorResult] at parsed
              | ok constructor next =>
                  simp only [constructorResult] at parsed
                  split at parsed
                  · exact Nat.le_trans commaMonotone (Nat.le_trans
                      (enumConstructor_cursorMonotoneOnSuccess afterComma
                        constructor next constructorResult)
                      (inductionHypothesis (constructor :: constructorsRev)
                        next body final parsed))
                  · contradiction
      · exact closeEnumBody_cursorMonotoneOnSuccess opening constructorsRev
          input body final parsed

/-- Every successful loop result keeps the original opening-brace start. -/
theorem enumConstructors_preservesOpeningStartOnSuccess (opening : Token) :
    ∀ fuel constructorsRev input body final,
      enumConstructors opening fuel constructorsRev input = .ok body final →
      body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro constructorsRev input body final parsed
      unfold enumConstructors at parsed
      split at parsed
      · cases commaResult : symbol .comma .topItem input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · exact closeEnumBody_preservesOpeningStartOnSuccess opening
                constructorsRev parsed
            · cases constructorResult : enumConstructor afterComma with
              | invariant error => simp [constructorResult] at parsed
              | reject failure rejected => simp [constructorResult] at parsed
              | ok constructor next =>
                  simp only [constructorResult] at parsed
                  split at parsed
                  · exact inductionHypothesis (constructor :: constructorsRev)
                      next body final parsed
                  · contradiction
      · exact closeEnumBody_preservesOpeningStartOnSuccess opening
          constructorsRev parsed

end EnumInternals
end Solcore.Syntax.Parser
