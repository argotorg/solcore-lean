import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.TypeDeclarationValidity
import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties
import Solcore.Syntax.DeclarativeEnumConstructorOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeEnumConstructorExactnessProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.DeclarativeEnumBodyExactnessProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.DeclarativeEnumDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeEnumDeclarationExactnessProperties
import Solcore.Syntax.Parser.GenericParametersTotalityProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace EnumInternals

/-- Parse the optional tuple payload of one enum constructor. -/
def enumConstructorFields : Parser (Option (DelimitedList TypeExpr)) := do
  let state ← getState
  if isSymbol state .leftParen then
    pure (some (← delimitedNoTrailing .leftParen .rightParen true typeExpr
      .typeExpr .topLevel))
  else
    pure none

/-- Parse one enum constructor and its optional tuple payload. -/
def enumConstructor : Parser EnumConstructor := do
  let name ← identifier .topItem
  let fields ← enumConstructorFields
  let endSpan := fields.map (fun values => values.span) |>.getD name.span
  pure {
    span := SourceSpan.cover name.span endSpan
    value := { leadingComments := [], name, fields }
  }

structure EnumBody where
  span : SourceSpan
  constructors : List EnumConstructor

def closeEnumBody (opening : Token)
    (constructorsRev : List EnumConstructor) : Parser EnumBody := do
  let closing ← symbol .rightBrace .topItem
  pure {
    span := SourceSpan.cover opening.span closing.span
    constructors := constructorsRev.reverse
  }

def enumConstructors (opening : Token) :
    Nat → List EnumConstructor → State → Reply EnumBody
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, constructorsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .topItem state with
        | .ok _ afterComma =>
            if isSymbol afterComma .rightBrace then
              closeEnumBody opening constructorsRev afterComma
            else
              let before := afterComma.cursor
              match enumConstructor afterComma with
              | .ok value next =>
                  if next.cursor > before then
                    enumConstructors opening fuel (value :: constructorsRev) next
                  else
                    .invariant (.noProgress .topLevel next.currentSpan)
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        closeEnumBody opening constructorsRev state

def enumBody : Parser EnumBody := fun state =>
  match symbol .leftBrace .topItem state with
  | .ok opening next =>
      if isSymbol next .rightBrace then
        closeEnumBody opening [] next
      else
        match enumConstructor next with
        | .ok first afterFirst =>
            enumConstructors opening (afterFirst.remainingCount + 1)
              [first] afterFirst
        | .reject failure failed => .reject failure failed
        | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

end EnumInternals

/-- Parse a canonical algebraic `enum` declaration. -/
def enumDecl
    (deriveAttribute : Option DeriveAttribute) : Parser EnumDecl := do
  let marker ← contextual .enum .topItem
  let name ← identifier .topItem
  let parameters ← optionalGenericParameters
  let body ← EnumInternals.enumBody
  let startSpan := deriveAttribute.map (fun derive => derive.span)
    |>.getD marker.span
  pure {
    span := SourceSpan.cover startSpan body.span
    value := {
      deriveAttribute
      name
      parameters
      bodySpan := body.span
      constructors := body.constructors
    }
  }

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumProperties`
-/

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

/-- Enum body parsing preserves its brace range and every constructor. -/
theorem enumBody_validFor : enumBody.ValidFor EnumBody.ValidFor := by
  intro input inputValid
  unfold enumBody
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := symbol_validFor .leftBrace .topItem input inputValid
      rw [openingResult] at valid
      exact valid
  | ok opening afterOpening =>
      have openingValid := symbol_validFor .leftBrace .topItem input inputValid
      rw [openingResult] at openingValid
      have openingShape := symbol_ok_state_shape .leftBrace .topItem
        openingResult
      have openingFound := State.getElem?_eq_some_of_peek?_eq_some
        openingShape.1
      have openingFoundAfter :
          afterOpening.tokens[input.cursor]? = some opening := by
        simpa [openingShape.2] using openingFound
      have openingBeforeAfter : input.cursor < afterOpening.cursor := by
        simp [openingShape.2]
      change (if isSymbol afterOpening .rightBrace then
          closeEnumBody opening [] afterOpening
        else match enumConstructor afterOpening with
          | .ok first afterFirst => enumConstructors opening
              (afterFirst.remainingCount + 1) [first] afterFirst
          | .reject failure failed => .reject failure failed
          | .invariant error => .invariant error).ValidFor input
            EnumBody.ValidFor
      split
      · exact Reply.ValidFor.of_file_eq
          (closeEnumBody_validFor opening [] openingValid.2.1
            openingFoundAfter openingBeforeAfter (by simp [List.ValidFor]))
          openingValid.2.2
      · cases firstResult : enumConstructor afterOpening with
        | invariant error =>
            change (Reply.invariant error).ValidFor input EnumBody.ValidFor
            trivial
        | reject failure rejected =>
            change (Reply.reject failure rejected).ValidFor input
              EnumBody.ValidFor
            have valid := enumConstructor_validFor afterOpening
              openingValid.2.1
            rw [firstResult] at valid
            exact valid.of_file_eq openingValid.2.2
        | ok first afterFirst =>
            change (enumConstructors opening
              (afterFirst.remainingCount + 1) [first] afterFirst).ValidFor
                input EnumBody.ValidFor
            have firstValid := enumConstructor_validFor afterOpening
              openingValid.2.1
            rw [firstResult] at firstValid
            have openingFoundFirst :
                afterFirst.tokens[input.cursor]? = some opening := by
              simpa [enumConstructor_preservesTokensOnSuccess afterOpening
                first afterFirst firstResult] using openingFoundAfter
            have firstAccumulated : List.ValidFor EnumConstructor.ValidFor
                afterFirst.file [first] := by
              intro constructor member
              simp only [List.mem_singleton] at member
              subst constructor
              simpa [firstValid.2.2] using firstValid.1
            exact (enumConstructors_validFor opening
              (afterFirst.remainingCount + 1) [first] afterFirst input.cursor
              firstValid.2.1 openingFoundFirst
              (Nat.lt_of_lt_of_le openingBeforeAfter
                (enumConstructor_cursorMonotoneOnSuccess afterOpening first
                  afterFirst firstResult)) firstAccumulated).of_file_eq
                (firstValid.2.2.trans openingValid.2.2)

/-- Enum body parsing preserves every ordinary token window. -/
theorem enumBody_preservesTokenWindow :
    Parser.PreservesTokenWindow enumBody := by
  intro input
  unfold enumBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [openingResult] at openingShape
      exact openingShape
  | ok opening afterOpening =>
      rw [openingResult] at openingShape
      change (if isSymbol afterOpening .rightBrace then
          closeEnumBody opening [] afterOpening
        else match enumConstructor afterOpening with
          | .ok first afterFirst => enumConstructors opening
              (afterFirst.remainingCount + 1) [first] afterFirst
          | .reject failure failed => .reject failure failed
          | .invariant error => .invariant error).PreservesTokenWindow input
      split
      · exact Reply.PreservesTokenWindow.trans
          (closeEnumBody_preservesTokenWindow opening [] afterOpening)
          openingShape
      · have firstShape := enumConstructor_preservesTokenWindow afterOpening
        cases firstResult : enumConstructor afterOpening with
        | invariant error =>
            change (Reply.invariant error).PreservesTokenWindow input
            trivial
        | reject failure rejected =>
            change (Reply.reject failure rejected).PreservesTokenWindow input
            rw [firstResult] at firstShape
            exact firstShape.trans openingShape
        | ok first afterFirst =>
            change Reply.PreservesTokenWindow (enumConstructors opening
              (afterFirst.remainingCount + 1) [first] afterFirst) input
            rw [firstResult] at firstShape
            exact (enumConstructors_preservesTokenWindow opening
              (afterFirst.remainingCount + 1) [first] afterFirst).trans
                (firstShape.trans openingShape)

theorem enumBody_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess enumBody :=
  enumBody_preservesTokenWindow.preservesTokensOnSuccess

/-- Enum body parsing never rewinds the parser cursor. -/
theorem enumBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess enumBody := by
  intro input body final parsed
  unfold enumBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have openingMonotone := symbol_cursorMonotoneOnSuccess .leftBrace
        .topItem input opening afterOpening openingResult
      split at parsed
      · exact Nat.le_trans openingMonotone
          (closeEnumBody_cursorMonotoneOnSuccess opening [] afterOpening body
            final parsed)
      · cases firstResult : enumConstructor afterOpening with
        | invariant error => simp [firstResult] at parsed
        | reject failure rejected => simp [firstResult] at parsed
        | ok first afterFirst =>
            simp only [firstResult] at parsed
            exact Nat.le_trans openingMonotone (Nat.le_trans
              (enumConstructor_cursorMonotoneOnSuccess afterOpening first
                afterFirst firstResult)
              (enumConstructors_cursorMonotoneOnSuccess opening
                (afterFirst.remainingCount + 1) [first] afterFirst body final
                parsed))

/-- An enum body starts at its current opening-brace token. -/
theorem enumBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess enumBody (·.span) := by
  intro input body final parsed
  unfold enumBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening afterOpening =>
      simp only [openingResult] at parsed
      have found := (symbol_ok_state_shape .leftBrace .topItem openingResult).1
      split at parsed
      · exact ⟨opening, found,
          (closeEnumBody_preservesOpeningStartOnSuccess opening [] parsed).symm⟩
      · cases firstResult : enumConstructor afterOpening with
        | invariant error => simp [firstResult] at parsed
        | reject failure rejected => simp [firstResult] at parsed
        | ok first afterFirst =>
            simp only [firstResult] at parsed
            exact ⟨opening, found,
              (enumConstructors_preservesOpeningStartOnSuccess opening
                (afterFirst.remainingCount + 1) [first] afterFirst body final
                parsed).symm⟩

end EnumInternals

/--
Complete enum declarations preserve all retained syntax. A supplied derive
attribute must already belong to the input and start no later than the current
`enum` token.
-/
theorem enumDecl_validFor (deriveAttribute : Option DeriveAttribute)
    {input : State} (inputValid : input.ValidFor)
    (deriveValid : Option.ValidFor DeriveAttribute.ValidFor input.file
      deriveAttribute)
    (deriveStartsBeforeCurrent : ∀ derive ∈ deriveAttribute,
      derive.span.startByte ≤ input.currentSpan.startByte) :
    (enumDecl deriveAttribute input).ValidFor input EnumDecl.ValidFor := by
  have weak : (enumDecl deriveAttribute).ValidFor (fun _ _ => True) := by
    unfold enumDecl
    apply Parser.bind_validFor (contextual_validFor .enum .topItem)
    intro marker
    apply Parser.bind_validFor (identifier_validFor .topItem)
    intro name
    apply Parser.bind_validFor optionalGenericParameters_validFor
    intro parameters
    apply Parser.bind_validFor EnumInternals.enumBody_validFor
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  have weakResult := weak input inputValid
  cases parsed : enumDecl deriveAttribute input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold enumDecl at stages
      rcases EnumInternals.enumBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases EnumInternals.enumBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases EnumInternals.enumBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases EnumInternals.enumBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerValid := contextual_validFor .enum .topItem input inputValid
      rw [markerResult] at markerValid
      have nameValid := identifier_validFor .topItem afterMarker
        markerValid.2.1
      rw [nameResult] at nameValid
      have parametersValid := optionalGenericParameters_validFor afterName
        nameValid.2.1
      rw [parametersResult] at parametersValid
      have bodyValid := EnumInternals.enumBody_validFor afterParameters
        parametersValid.2.1
      rw [bodyResult] at bodyValid
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using markerValid.1
      have nameSpanValid : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerValid.2.2] using nameValid.1
      have parametersValidInput : Option.ValidFor
          (NonemptyDelimitedList.ValidFor Located.ValidFor) input.file
          parameters := by
        simpa [nameValid.2.2, markerValid.2.2] using parametersValid.1
      have bodyValidInput : EnumInternals.EnumBody.ValidFor input.file body := by
        simpa [parametersValid.2.2, nameValid.2.2, markerValid.2.2] using
          bodyValid.1
      have markerShape := acceptToken_ok_state_shape (.contextual .enum)
        .topItem (·.isContextual .enum) markerResult
      have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
      rcases EnumInternals.enumBody_startsAtCurrentTokenOnSuccess
          afterParameters body afterBody bodyResult with
        ⟨opening, openingFound, bodyStart⟩
      have openingAt : input.tokens[afterParameters.cursor]? = some opening := by
        have found := State.getElem?_eq_some_of_peek?_eq_some openingFound
        simpa [optionalGenericParameters_preservesTokensOnSuccess afterName
            parameters afterParameters parametersResult,
          identifier_preservesTokensOnSuccess .topItem afterMarker name
            afterName nameResult,
          contextual_preservesTokensOnSuccess .enum .topItem input marker
            afterMarker markerResult] using found
      have cursorOrder : input.cursor < afterParameters.cursor :=
        Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
          (.contextual .enum) .topItem (·.isContextual .enum) markerResult)
          (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
            afterMarker name afterName nameResult)
            (optionalGenericParameters_cursorMonotoneOnSuccess afterName
              parameters afterParameters parametersResult))
      have markerBeforeBody : marker.span.startByte ≤ body.span.endByte := by
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          markerAt openingAt cursorOrder
        exact Nat.le_trans markerSpanValid.2.1 (Nat.le_trans separated (by
          rw [bodyStart]
          exact bodyValidInput.1.2.1))
      let startSpan := deriveAttribute.map (fun derive => derive.span)
        |>.getD marker.span
      have startValid : startSpan.ValidFor input.file := by
        cases deriveAttribute with
        | none => simpa [startSpan] using markerSpanValid
        | some derive =>
            simpa [startSpan, Option.ValidFor] using deriveValid.1
      have startBeforeBody : startSpan.startByte ≤ body.span.endByte := by
        cases deriveAttribute with
        | none => simpa [startSpan] using markerBeforeBody
        | some derive =>
            have before := deriveStartsBeforeCurrent derive (by simp)
            have currentIsMarker : input.currentSpan = marker.span := by
              simp [State.currentSpan, markerShape.1]
            rw [currentIsMarker] at before
            exact Nat.le_trans before markerBeforeBody
      have outerValid := SourceSpan.cover_validFor startValid bodyValidInput.1
        startBeforeBody
      have retainedDerivesValid : ∀ retained ∈ deriveAttribute,
          DeriveAttribute.ValidFor input.file retained := by
        intro retained member
        cases deriveAttribute with
        | none => simp at member
        | some derive =>
            have retainedEq : retained = derive := by simpa using member.symm
            subst retained
            simpa only [Option.ValidFor] using deriveValid
      cases finished
      refine ⟨⟨outerValid, retainedDerivesValid, nameSpanValid, ?_, ?_,
        bodyValidInput.1, bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩
      · cases parameters with
        | none => simp
        | some values => simpa [Option.ValidFor] using parametersValidInput.1
      · cases parameters with
        | none => simp
        | some values =>
            intro retained member parameter parameterMember
            have retainedEq : retained = values := by simpa using member.symm
            subst retained
            exact parametersValidInput.2 parameter parameterMember

/-- The no-derive enum parser has an unconditional declaration contract. -/
theorem enumDecl_none_validFor :
    (enumDecl none).ValidFor EnumDecl.ValidFor := by
  intro input inputValid
  exact enumDecl_validFor none inputValid (by trivial) (by simp)

/-- Complete enum declarations preserve every ordinary token window. -/
theorem enumDecl_preservesTokenWindow
    (deriveAttribute : Option DeriveAttribute) :
    Parser.PreservesTokenWindow (enumDecl deriveAttribute) := by
  unfold enumDecl
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .enum .topItem)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow
    optionalGenericParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow
    EnumInternals.enumBody_preservesTokenWindow
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem enumDecl_preservesTokensOnSuccess
    (deriveAttribute : Option DeriveAttribute) :
    Parser.PreservesTokensOnSuccess (enumDecl deriveAttribute) :=
  (enumDecl_preservesTokenWindow deriveAttribute).preservesTokensOnSuccess

/-- Complete enum declarations never rewind the parser cursor. -/
theorem enumDecl_cursorMonotoneOnSuccess
    (deriveAttribute : Option DeriveAttribute) :
    Parser.CursorMonotoneOnSuccess (enumDecl deriveAttribute) := by
  unfold enumDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (contextual_cursorMonotoneOnSuccess .enum .topItem)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    EnumInternals.enumBody_cursorMonotoneOnSuccess
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Without a derive attribute, an enum starts at its current `enum` token. -/
theorem enumDecl_none_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (enumDecl none) (·.span) := by
  unfold enumDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (contextual_startsAtCurrentTokenOnSuccess .enum .topItem)
  intro marker input declaration final parsed
  rcases EnumInternals.enumBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases EnumInternals.enumBind_ok_components rest with
    ⟨parameters, afterParameters, _parametersResult, rest⟩
  rcases EnumInternals.enumBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

/-- With a derive attribute, the declaration retains its supplied start. -/
theorem enumDecl_some_preservesDerivedStartOnSuccess
    (deriveAttribute : DeriveAttribute) {input final : State}
    {declaration : EnumDecl}
    (parsed : enumDecl (some deriveAttribute) input = .ok declaration final) :
    deriveAttribute.span.startByte = declaration.span.startByte := by
  unfold enumDecl at parsed
  rcases EnumInternals.enumBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases EnumInternals.enumBind_ok_components rest with
    ⟨name, afterName, _nameResult, rest⟩
  rcases EnumInternals.enumBind_ok_components rest with
    ⟨parameters, afterParameters, _parametersResult, rest⟩
  rcases EnumInternals.enumBind_ok_components rest with
    ⟨body, afterBody, _bodyResult, finished⟩
  cases finished
  rfl

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumConstructorSoundnessProperties`
-/

/-! Success soundness for enum constructors and their optional payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem enumConstructorSoundness_bind_ok_components {α β : Type}
    {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

/-- Optional constructor fields follow their prioritized no-trailing grammar. -/
theorem enumConstructorFields_success_sound {input next : State}
    {fields : Option (DelimitedList TypeExpr)}
    (result : enumConstructorFields input = .ok fields next) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsParses
      input.declarativeRemainder fields next.declarativeRemainder := by
  unfold enumConstructorFields getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases fieldsResult : delimitedNoTrailing .leftParen .rightParen true
        typeExpr .typeExpr .topLevel input with
    | invariant error =>
        simp [fieldsResult] at result
    | reject failure rejected =>
        simp [fieldsResult] at result
    | ok values afterValues =>
        have fieldsGrammar := delimitedNoTrailing_allowEmpty_success_sound
          .leftParen .rightParen typeExpr
          DeclarativeGrammar.TypeExprParses .typeExpr .topLevel
          typeExpr_success_sound typeExpr_preservesTokenWindow fieldsResult
        simp only [fieldsResult, pure] at result
        cases result
        exact .present fieldsGrammar
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

/-- Optional-field grammar soundness composes with source validity. -/
theorem enumConstructorFields_success_sound_and_validFor
    {input next : State} {fields : Option (DelimitedList TypeExpr)}
    (inputValid : input.ValidFor)
    (result : enumConstructorFields input = .ok fields next) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsParses
        input.declarativeRemainder fields next.declarativeRemainder ∧
      Option.ValidFor (DelimitedList.ValidFor TypeExpr.ValidFor)
        input.file fields := by
  refine ⟨enumConstructorFields_success_sound result, ?_⟩
  have valid := enumConstructorFields_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Every successful enum constructor follows its exact retained grammar. -/
theorem enumConstructor_success_sound {input next : State}
    {constructor : EnumConstructor}
    (result : enumConstructor input = .ok constructor next) :
    DeclarativeGrammar.EnumConstructorParses input.declarativeRemainder
      constructor next.declarativeRemainder := by
  unfold enumConstructor at result
  rcases enumConstructorSoundness_bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  rcases enumConstructorSoundness_bind_ok_components rest with
    ⟨fields, afterFields, fieldsResult, finished⟩
  cases finished
  exact .parsed (identifier_success_sound .topItem nameResult)
    (enumConstructorFields_success_sound fieldsResult)

/-- Constructor grammar soundness composes with source validity. -/
theorem enumConstructor_success_sound_and_validFor {input next : State}
    {constructor : EnumConstructor} (inputValid : input.ValidFor)
    (result : enumConstructor input = .ok constructor next) :
    DeclarativeGrammar.EnumConstructorParses input.declarativeRemainder
        constructor next.declarativeRemainder ∧
      EnumConstructor.ValidFor input.file constructor := by
  refine ⟨enumConstructor_success_sound result, ?_⟩
  have valid := enumConstructor_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumConstructorOrdinarySuccessSoundnessProperties`
-/

/-! Ordinary-success bridges for enum constructors and tuple payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Every successful optional enum-constructor payload follows the public Core
type ordinary grammar with its exact output remainder. -/
theorem enumConstructorFields_success_ordinaryOutcome_sound
    {input output : State} {fields : Option (DelimitedList TypeExpr)}
    (result : enumConstructorFields input = .ok fields output) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      input.declarativeRemainder fields output.declarativeRemainder :=
  enumConstructorFields_success_sound result

/-- Every successful enum constructor records its exact name, optional tuple
payload, AST span, empty leading trivia, and output remainder. -/
theorem enumConstructor_success_ordinaryOutcome_sound
    {input output : State} {constructor : EnumConstructor}
    (result : enumConstructor input = .ok constructor output) :
    DeclarativeGrammar.EnumConstructorOrdinaryParses
      input.declarativeRemainder constructor output.declarativeRemainder :=
  enumConstructor_success_sound result

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumConstructorOrdinaryRejectionSoundnessProperties`
-/

/-! Exact ordinary-rejection bridges for enum constructors and tuple payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- A rejected optional enum-constructor payload has a positively guarded
opening parenthesis and the exact no-trailing nested type-list rejection. -/
theorem enumConstructorFields_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumConstructorFields input = .reject failure rejected) :
    DeclarativeGrammar.OptionalEnumConstructorFieldsRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold enumConstructorFields getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with
      ⟨opening, openingResult⟩
    simp only [present, if_true] at result
    cases fieldsResult : delimitedNoTrailing .leftParen .rightParen true
        typeExpr .typeExpr .topLevel input with
    | invariant error => simp [fieldsResult] at result
    | ok fields output => simp [fieldsResult, pure] at result
    | reject fieldsFailure fieldsRejected =>
        simp only [fieldsResult] at result
        cases result
        exact .present
          ⟨opening.span,
            (symbol_ok_tokenAt .leftParen .typeExpr openingResult).1⟩
          (delimitedNoTrailing_reject_sound .leftParen .rightParen true
            typeExpr DeclarativeGrammar.TypeExprOrdinaryParses
            DeclarativeGrammar.TypeExprRejects .typeExpr .topLevel
            typeExpr_success_sound typeExpr_reject_sound fieldsResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Every rejected enum constructor records its first rejecting stage: the
name, or its positively selected optional tuple payload. -/
theorem enumConstructor_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumConstructor input = .reject failure rejected) :
    DeclarativeGrammar.EnumConstructorRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold enumConstructor at result
  cases nameResult : identifier .topItem input with
  | invariant error => simp [bind, nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [bind, nameResult] at result
      cases result
      exact .nameRejected (identifier_reject_sound .topItem nameResult)
  | ok name afterName =>
      simp only [bind, nameResult] at result
      have nameParsed := identifier_success_sound .topItem nameResult
      cases fieldsResult : enumConstructorFields afterName with
      | invariant error => simp [fieldsResult] at result
      | reject fieldsFailure fieldsRejected =>
          simp only [fieldsResult] at result
          cases result
          exact .fieldsRejected nameParsed
            (enumConstructorFields_reject_ordinaryOutcome_sound fieldsResult)
      | ok fields output => simp [fieldsResult, pure] at result

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumConstructorOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for enum constructors and payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Package optional enum-constructor payload success and exact rejection. -/
theorem enumConstructorFields_ordinaryOutcome_sound :
    (∀ {input output : State} {fields : Option (DelimitedList TypeExpr)},
      enumConstructorFields input = .ok fields output →
        DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
          input.declarativeRemainder fields output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumConstructorFields input = .reject failure rejected →
        DeclarativeGrammar.OptionalEnumConstructorFieldsRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨enumConstructorFields_success_ordinaryOutcome_sound,
    enumConstructorFields_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional enum-constructor payload outcomes. -/
theorem enumConstructorFields_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      DeclarativeGrammar.OptionalEnumConstructorFieldsRejects :=
  DeclarativeGrammar.optionalEnumConstructorFieldsDeterministicOutcomeSpec

/-- Package enum-constructor success and exact sequential rejection. -/
theorem enumConstructor_ordinaryOutcome_sound :
    (∀ {input output : State} {constructor : EnumConstructor},
      enumConstructor input = .ok constructor output →
        DeclarativeGrammar.EnumConstructorOrdinaryParses
          input.declarativeRemainder constructor output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumConstructor input = .reject failure rejected →
        DeclarativeGrammar.EnumConstructorRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨enumConstructor_success_ordinaryOutcome_sound,
    enumConstructor_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive enum-constructor outcomes. -/
theorem enumConstructor_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.EnumConstructorOrdinaryParses
      DeclarativeGrammar.EnumConstructorRejects :=
  DeclarativeGrammar.enumConstructorDeterministicOutcomeSpec

/-- Re-export exact optional enum-constructor payload outcomes. -/
theorem enumConstructorFields_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
      DeclarativeGrammar.OptionalEnumConstructorFieldsRejects :=
  DeclarativeGrammar.optionalEnumConstructorFieldsExactOutcomeSpec

/-- Two successful optional payloads fix the same value and remainder. -/
theorem enumConstructorFields_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option (DelimitedList TypeExpr)}
    (leftResult : enumConstructorFields input = .ok left leftOutput)
    (rightResult : enumConstructorFields input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses.result_unique
    (enumConstructorFields_success_ordinaryOutcome_sound leftResult)
    (enumConstructorFields_success_ordinaryOutcome_sound rightResult)

/-- Two optional payload rejections have the same declarative endpoint. -/
theorem enumConstructorFields_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumConstructorFields input = .reject leftFailure leftOutput)
    (rightResult : enumConstructorFields input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalEnumConstructorFieldsRejects.output_unique
    (enumConstructorFields_reject_ordinaryOutcome_sound leftResult)
    (enumConstructorFields_reject_ordinaryOutcome_sound rightResult)

/-- Re-export unconditional exact enum-constructor outcomes. -/
theorem enumConstructor_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.EnumConstructorOrdinaryParses
      DeclarativeGrammar.EnumConstructorRejects :=
  DeclarativeGrammar.enumConstructorExactOutcomeSpec

/-- Two successful enum constructors have the same AST and remainder. -/
theorem enumConstructor_success_result_unique
    {input leftOutput rightOutput : State} {left right : EnumConstructor}
    (leftResult : enumConstructor input = .ok left leftOutput)
    (rightResult : enumConstructor input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumConstructorOrdinaryParses.result_unique
    (enumConstructor_success_ordinaryOutcome_sound leftResult)
    (enumConstructor_success_ordinaryOutcome_sound rightResult)

/-- Two enum-constructor rejections have the same declarative endpoint. -/
theorem enumConstructor_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumConstructor input = .reject leftFailure leftOutput)
    (rightResult : enumConstructor input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumConstructorRejects.output_unique
    (enumConstructor_reject_ordinaryOutcome_sound leftResult)
    (enumConstructor_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumElementTotalityProperties`
-/

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

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumBodySoundnessProperties`
-/

/-! Success soundness for the fuel-bounded enum-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem enumBodySoundness_bind_ok_components {α β : Type}
    {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

private theorem closeEnumBody_success_sound (opening : Token)
    (constructorsRev : List EnumConstructor) {input next : State}
    {body : EnumBody}
    (result : closeEnumBody opening constructorsRev input = .ok body next) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        constructors := constructorsRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan next.declarativeRemainder := by
  unfold closeEnumBody at result
  rcases enumBodySoundness_bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

private theorem tail_close_of_exact
    {input output : DeclarativeGrammar.Remainder}
    {closingSpan : SourceSpan}
    (commaAbsent : DeclarativeGrammar.TokenKindAbsentAt
      input.tokens input.endIndex input.cursor (.symbol .comma))
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      input closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input [] closingSpan output := by
  rcases closing with ⟨closingToken, rfl⟩
  exact .close commaAbsent closingToken

private theorem tail_trailing_of_exact
    {input afterComma output : DeclarativeGrammar.Remainder}
    {commaSpan closingSpan : SourceSpan}
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma)
      input commaSpan afterComma)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      afterComma closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input [] closingSpan output := by
  rcases comma with ⟨commaToken, rfl⟩
  rcases closing with ⟨closingToken, rfl⟩
  exact .trailing commaToken closingToken

private theorem tail_next_of_exact
    {input afterComma afterElement output : DeclarativeGrammar.Remainder}
    {commaSpan closingSpan : SourceSpan} {element : EnumConstructor}
    {elements : List EnumConstructor}
    (comma : DeclarativeGrammar.ExactTokenParses (.symbol .comma)
      input commaSpan afterComma)
    (closingAbsent : DeclarativeGrammar.TokenKindAbsentAt afterComma.tokens
      afterComma.endIndex afterComma.cursor (.symbol .rightBrace))
    (elementParsed : DeclarativeGrammar.EnumConstructorParses
      afterComma element afterElement)
    (progress : afterComma.cursor < afterElement.cursor)
    (tail : DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses afterElement elements
        closingSpan output) :
    DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
      DeclarativeGrammar.EnumConstructorParses input (element :: elements)
        closingSpan output := by
  rcases comma with ⟨commaToken, rfl⟩
  exact .next commaToken closingAbsent elementParsed progress tail

private theorem enumConstructors_success_sound_strong (opening : Token) :
    ∀ fuel constructorsRev input body next,
      enumConstructors opening fuel constructorsRev input = .ok body next →
        ∃ rest closingSpan,
          body = {
            span := SourceSpan.cover opening.span closingSpan
            constructors := constructorsRev.reverse ++ rest
          } ∧
          DeclarativeGrammar.TrailingDelimitedTailParses .rightBrace
            DeclarativeGrammar.EnumConstructorParses
              input.declarativeRemainder rest closingSpan
                next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro constructorsRev input body next result
      simp [enumConstructors] at result
  | succ fuel inductionHypothesis =>
      intro constructorsRev input body next result
      unfold enumConstructors at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          rcases closeEnumBody_success_sound opening constructorsRev result with
            ⟨closingSpan, bodyEq, closingGrammar⟩
          refine ⟨[], closingSpan, ?_,
            tail_close_of_exact
              (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)
              closingGrammar⟩
          simpa using bodyEq
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .topItem input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              have commaGrammar :=
                symbol_success_exactTokenParses .comma .topItem commaResult
              cases closingPresent : isSymbol afterComma .rightBrace with
              | true =>
                  simp only [closingPresent, if_true] at result
                  rcases closeEnumBody_success_sound opening constructorsRev
                      result with ⟨closingSpan, bodyEq, closingGrammar⟩
                  refine ⟨[], closingSpan, ?_,
                    tail_trailing_of_exact commaGrammar closingGrammar⟩
                  simpa using bodyEq
              | false =>
                  simp only [closingPresent, Bool.false_eq_true, if_false]
                    at result
                  cases constructorResult : enumConstructor afterComma with
                  | invariant error => simp [constructorResult] at result
                  | reject failure rejected =>
                      simp [constructorResult] at result
                  | ok constructor afterConstructor =>
                      simp only [constructorResult] at result
                      by_cases progress :
                          afterComma.cursor < afterConstructor.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis
                            (constructor :: constructorsRev) afterConstructor
                            body next result with
                          ⟨rest, closingSpan, bodyEq, tailGrammar⟩
                        refine ⟨constructor :: rest, closingSpan, ?_,
                          tail_next_of_exact commaGrammar
                            (symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                              closingPresent)
                            (enumConstructor_success_sound constructorResult)
                            progress tailGrammar⟩
                        simpa [List.reverse_cons, List.append_assoc] using bodyEq
                      · simp only [progress, if_false] at result
                        contradiction

private theorem enumBody_empty_of_exact
    {input afterOpening output : DeclarativeGrammar.Remainder}
    {openingSpan closingSpan : SourceSpan}
    (opening : DeclarativeGrammar.ExactTokenParses (.symbol .leftBrace)
      input openingSpan afterOpening)
    (closing : DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
      afterOpening closingSpan output) :
    DeclarativeGrammar.EnumBodyParses input
      (SourceSpan.cover openingSpan closingSpan) [] output := by
  unfold DeclarativeGrammar.EnumBodyParses
  rcases opening with ⟨openingToken, rfl⟩
  rcases closing with ⟨closingToken, rfl⟩
  exact .empty openingSpan closingSpan openingToken closingToken

/-- Every successful enum body follows the exact forward constructor grammar. -/
theorem enumBody_success_sound {input next : State} {body : EnumBody}
    (result : enumBody input = .ok body next) :
    DeclarativeGrammar.EnumBodyParses input.declarativeRemainder body.span
      body.constructors next.declarativeRemainder := by
  have outputShape := enumBody_preservesTokenWindow input
  rw [result] at outputShape
  unfold enumBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingSound := symbol_ok_tokenAt .leftBrace .topItem openingResult
      have openingGrammar :=
        symbol_success_exactTokenParses .leftBrace .topItem openingResult
      cases emptyPresent : isSymbol afterOpening .rightBrace with
      | true =>
          simp only [emptyPresent, if_true] at result
          rcases closeEnumBody_success_sound opening [] result with
            ⟨closingSpan, bodyEq, closingGrammar⟩
          rw [bodyEq]
          simpa using enumBody_empty_of_exact openingGrammar closingGrammar
      | false =>
          simp only [emptyPresent, Bool.false_eq_true, if_false] at result
          cases firstResult : enumConstructor afterOpening with
          | invariant error => simp [firstResult] at result
          | reject failure rejected => simp [firstResult] at result
          | ok first afterFirst =>
              simp only [firstResult] at result
              rcases enumConstructors_success_sound_strong opening
                  (afterFirst.remainingCount + 1) [first] afterFirst body next
                  result with ⟨rest, closingSpan, bodyEq, tailGrammar⟩
              rw [bodyEq]
              apply DeclarativeGrammar.TrailingDelimitedListParses.nonempty
              · have absent := symbolAbsentAt_of_isSymbol_eq_false
                    .rightBrace emptyPresent
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using absent
              · unfold DeclarativeGrammar.NonemptyTrailingDelimitedListParses
                refine ⟨opening.span, first, afterFirst.declarativeRemainder,
                  rest, closingSpan, outputShape.1,
                  congrArg TokenWindow.endIndex outputShape.2,
                  openingSound.1, ?_, ?_, tailGrammar, by simp, rfl⟩
                · simpa only [openingSound.2, State.declarativeRemainder,
                    State.tokens, State.window, State.cursor] using
                    enumConstructor_success_sound firstResult
                · have progress := enumConstructor_cursor_lt_onSuccess
                    firstResult
                  simpa only [openingSound.2, State.declarativeRemainder,
                    State.cursor] using progress

/-- Enum-body grammar soundness composes with source validity. -/
theorem enumBody_success_sound_and_validFor {input next : State}
    {body : EnumBody} (inputValid : input.ValidFor)
    (result : enumBody input = .ok body next) :
    DeclarativeGrammar.EnumBodyParses input.declarativeRemainder body.span
        body.constructors next.declarativeRemainder ∧
      EnumBody.ValidFor input.file body := by
  refine ⟨enumBody_success_sound result, ?_⟩
  have valid := enumBody_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumBodyOrdinarySuccessSoundnessProperties`
-/

/-! Ordinary-success bridge for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Every successful enum body records its exact cover span, constructor list,
and final remainder in the single-output ordinary relation. -/
theorem enumBody_success_ordinaryOutcome_sound
    {input output : State} {body : EnumBody}
    (result : enumBody input = .ok body output) :
    DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      input.declarativeRemainder (body.span, body.constructors)
        output.declarativeRemainder :=
  enumBody_success_sound result

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumBodyOrdinaryRejectionSoundnessProperties`
-/

/-! Exact ordinary-rejection bridge for the custom enum-body loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem closeEnumBody_reject_sound (opening : Token)
    (constructorsRev : List EnumConstructor)
    {input rejected : State} {failure : Failure}
    (result : closeEnumBody opening constructorsRev input =
      .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .rightBrace) := by
  unfold closeEnumBody at result
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp [bind, closingResult] at result
  | ok closing output => simp [bind, closingResult, pure] at result
  | reject closingFailure closingRejected =>
      simp only [bind, closingResult] at result
      cases result
      exact ⟨symbol_reject_state_eq .rightBrace .topItem closingResult,
        symbol_reject_tokenKindAbsentAt .rightBrace .topItem closingResult⟩

private theorem enumConstructors_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel constructorsRev input rejected failure,
      enumConstructors opening fuel constructorsRev input =
        .reject failure rejected →
      DeclarativeGrammar.DelimitedTailRejects .rightBrace true
        DeclarativeGrammar.EnumConstructorOrdinaryParses
        DeclarativeGrammar.EnumConstructorRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro constructorsRev input rejected failure result
      simp [enumConstructors] at result
  | succ fuel inductionHypothesis =>
      intro constructorsRev input rejected failure result
      unfold enumConstructors at result
      by_cases commaPresent : isSymbol input .comma = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .comma .topItem commaPresent
          with ⟨comma, commaResult⟩
        simp only [commaPresent, if_true, commaResult] at result
        by_cases closingPresent :
            isSymbol { input with cursor := input.cursor + 1 }
              .rightBrace = true
        · rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
              closingPresent with ⟨closing, closingResult⟩
          simp only [closingPresent, if_true] at result
          unfold closeEnumBody at result
          simp [bind, closingResult, pure] at result
        · have closingAbsent :
              isSymbol { input with cursor := input.cursor + 1 }
                .rightBrace = false :=
            Bool.eq_false_iff.mpr closingPresent
          simp only [closingAbsent, Bool.false_eq_true, if_false] at result
          cases constructorResult : enumConstructor
              { input with cursor := input.cursor + 1 } with
          | invariant error => simp [constructorResult] at result
          | reject constructorFailure constructorRejected =>
              simp only [constructorResult] at result
              cases result
              exact .elementRejected comma.span
                (symbol_ok_tokenAt .comma .topItem commaResult).1
                (by
                  exact .absent
                    (by
                      simpa [State.declarativeRemainder] using
                        symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                          closingAbsent))
                (by
                  simpa [State.declarativeRemainder] using
                    enumConstructor_reject_ordinaryOutcome_sound
                      constructorResult)
          | ok constructor afterConstructor =>
              simp only [constructorResult] at result
              by_cases progress :
                  afterConstructor.cursor > input.cursor + 1
              · simp only [progress, if_true] at result
                exact .laterRejected comma.span
                  (symbol_ok_tokenAt .comma .topItem commaResult).1
                  (by
                    exact .absent
                      (by
                        simpa [State.declarativeRemainder] using
                          symbolAbsentAt_of_isSymbol_eq_false .rightBrace
                            closingAbsent))
                  (by
                    simpa [State.declarativeRemainder] using
                      enumConstructor_success_ordinaryOutcome_sound
                        constructorResult)
                  (by
                    simpa [State.declarativeRemainder] using
                      progress)
                  (inductionHypothesis (constructor :: constructorsRev)
                    afterConstructor rejected failure result)
              · simp [progress] at result
      · have commaAbsent : isSymbol input .comma = false :=
          Bool.eq_false_iff.mpr commaPresent
        simp only [commaAbsent, Bool.false_eq_true, if_false] at result
        rcases closeEnumBody_reject_sound opening constructorsRev result with
          ⟨rejectedEq, closingAbsent⟩
        subst rejected
        exact .delimiterMissing
          (symbolAbsentAt_of_isSymbol_eq_false .comma commaAbsent)
          closingAbsent

/-- Every enum-body rejection follows the generic allow-empty,
allow-trailing rejection relation at the exact retained remainder. -/
theorem enumBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : enumBody input = .reject failure rejected) :
    DeclarativeGrammar.EnumBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold enumBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      simp only [openingResult] at result
      cases result
      have rejectedEq := symbol_reject_state_eq .leftBrace .topItem
        openingResult
      subst rejected
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      have openingSound := symbol_ok_tokenAt .leftBrace .topItem openingResult
      by_cases closingPresent : isSymbol afterOpening .rightBrace = true
      · rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem
            closingPresent with ⟨closing, closingResult⟩
        simp only [closingPresent, if_true] at result
        unfold closeEnumBody at result
        simp [bind, closingResult, pure] at result
      · have closingAbsent : isSymbol afterOpening .rightBrace = false :=
          Bool.eq_false_iff.mpr closingPresent
        simp only [closingAbsent, Bool.false_eq_true, if_false] at result
        have continues : DeclarativeGrammar.PreferredCloseNotTaken
            .rightBrace true {
              input.declarativeRemainder with cursor := input.cursor + 1
            } := by
          exact .absent (by
            simpa only [openingSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingAbsent)
        cases firstResult : enumConstructor afterOpening with
        | invariant error => simp [firstResult] at result
        | reject firstFailure firstRejected =>
            simp only [firstResult] at result
            cases result
            exact .firstRejected opening.span openingSound.1 continues
              (by
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                    enumConstructor_reject_ordinaryOutcome_sound firstResult)
        | ok first afterFirst =>
            simp only [firstResult] at result
            exact .tailRejected opening.span openingSound.1 continues
              (by
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                    enumConstructor_success_ordinaryOutcome_sound firstResult)
              (by
                have progress := enumConstructor_cursor_lt_onSuccess
                  firstResult
                simpa only [openingSound.2, State.declarativeRemainder,
                  State.cursor] using progress)
              (enumConstructors_reject_ordinaryOutcome_sound opening
                (afterFirst.remainingCount + 1) [first] afterFirst rejected
                  failure result)

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumBodyOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for canonical enum bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

/-- Package executable enum-body success and exact rejection. -/
theorem enumBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : EnumBody},
      enumBody input = .ok body output →
        DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
          input.declarativeRemainder (body.span, body.constructors)
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumBody input = .reject failure rejected →
        DeclarativeGrammar.EnumBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨enumBody_success_ordinaryOutcome_sound,
    enumBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive enum-body ordinary outcomes. -/
theorem enumBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      DeclarativeGrammar.EnumBodyRejects :=
  DeclarativeGrammar.enumBodyDeterministicOutcomeSpec

/-- Re-export unconditional exact enum-body outcomes. -/
theorem enumBody_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
      DeclarativeGrammar.EnumBodyRejects :=
  DeclarativeGrammar.enumBodyExactOutcomeSpec

/-- Two successful enum bodies have the same span, constructors, and remainder. -/
theorem enumBody_success_result_unique
    {input leftOutput rightOutput : State} {left right : EnumBody}
    (leftResult : enumBody input = .ok left leftOutput)
    (rightResult : enumBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases enumBody_exactOutcomeSpec.successResultUnique
      (enumBody_success_ordinaryOutcome_sound leftResult)
      (enumBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    cases bodyEq
    rfl
  · exact outputEq

/-- Two enum-body rejections have the same declarative endpoint. -/
theorem enumBody_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumBody input = .reject leftFailure leftOutput)
    (rightResult : enumBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumBodyRejects.output_unique
    (enumBody_reject_ordinaryOutcome_sound leftResult)
    (enumBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumBodyTotalityProperties`
-/

/-! Valid-input totality for canonical enum-body iteration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.EnumInternals

private theorem closeEnumBody_ordinary (opening : Token)
    (constructorsRev : List EnumConstructor) :
    Parser.Ordinary (closeEnumBody opening constructorsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span closing.span
        constructors := constructorsRev.reverse
      }, next, by
        simp only [closeEnumBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeEnumBody, bind, closingResult]⟩

/-- Strict constructor progress makes the explicit loop fuel sufficient. -/
theorem enumConstructors_ordinary :
    ∀ opening fuel constructorsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        enumConstructors opening fuel constructorsRev input = .ok body next) ∨
      (∃ failure next,
        enumConstructors opening fuel constructorsRev input =
          .reject failure next) := by
  intro opening fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro constructorsRev input inputValid adequate
      unfold enumConstructors
      by_cases commaPresent : isSymbol input .comma
      · simp only [commaPresent, if_true]
        rcases (symbol_ordinary .comma .topItem) input with
          ⟨comma, afterComma, commaResult⟩ |
          ⟨failure, rejected, commaResult⟩
        · have commaReply := symbol_validFor .comma .topItem input inputValid
          rw [commaResult] at commaReply
          have commaWindow := symbol_preservesTokenWindow .comma .topItem input
          rw [commaResult] at commaWindow
          have commaProgress := acceptToken_cursor_lt_onSuccess
            (.symbol .comma) .topItem (· == .symbol .comma) commaResult
          have afterCommaAdequate : afterComma.remainingCount < fuel :=
            remainingCount_lt_after_strict_progress commaReply.2.1
              commaWindow.2 commaProgress adequate
          by_cases closes : isSymbol afterComma .rightBrace
          · simpa only [commaResult, closes, if_true] using
              closeEnumBody_ordinary opening constructorsRev afterComma
          · rcases enumConstructor_ordinary afterComma commaReply.2.1 with
              ⟨constructor, next, constructorResult⟩ |
              ⟨failure, rejected, constructorResult⟩
            · have constructorReply :=
                enumConstructor_elementTotalityContract.validFor
                  afterComma commaReply.2.1
              rw [constructorResult] at constructorReply
              have constructorWindow :=
                enumConstructor_elementTotalityContract.preservesTokenWindow
                  afterComma
              rw [constructorResult] at constructorWindow
              have progress :=
                enumConstructor_elementTotalityContract.cursorLtOnSuccess
                  constructorResult
              have nextAdequate : next.remainingCount < fuel :=
                remainingCount_lt_of_cursor_le constructorWindow.2
                  (Nat.le_of_lt progress) afterCommaAdequate
              simpa only [commaResult, closes, Bool.false_eq_true, if_false,
                constructorResult, if_pos progress] using
                  inductionHypothesis (constructor :: constructorsRev) next
                    constructorReply.2.1 nextAdequate
            · exact Or.inr ⟨failure, rejected, by
                simp only [commaResult, closes, Bool.false_eq_true, if_false,
                  constructorResult]⟩
        · exact Or.inr ⟨failure, rejected, by simp only [commaResult]⟩
      · simp only [commaPresent, Bool.false_eq_true, if_false]
        exact closeEnumBody_ordinary opening constructorsRev input

theorem enumConstructors_ne_invariant
    (opening : Token) (fuel : Nat)
    (constructorsRev : List EnumConstructor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    enumConstructors opening fuel constructorsRev input ≠ .invariant error := by
  intro failed
  rcases enumConstructors_ordinary opening fuel constructorsRev input
      inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Production enum-body fuel always yields an ordinary result. -/
theorem enumBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, enumBody input = .ok body next) ∨
      (∃ failure next, enumBody input = .reject failure next) := by
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    by_cases empty : isSymbol afterOpening .rightBrace
    · simpa only [enumBody, openingResult, empty, if_true] using
        closeEnumBody_ordinary opening [] afterOpening
    · rcases enumConstructor_ordinary afterOpening openingReply.2.1 with
        ⟨constructor, afterFirst, constructorResult⟩ |
        ⟨failure, rejected, constructorResult⟩
      · have constructorReply :=
          enumConstructor_elementTotalityContract.validFor afterOpening
            openingReply.2.1
        rw [constructorResult] at constructorReply
        simpa only [enumBody, openingResult, empty, Bool.false_eq_true,
          if_false, constructorResult] using
            enumConstructors_ordinary opening
              (afterFirst.remainingCount + 1) [constructor] afterFirst
                constructorReply.2.1 (by omega)
      · exact Or.inr ⟨failure, rejected, by
          simp only [enumBody, openingResult, empty, Bool.false_eq_true,
            if_false, constructorResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [enumBody, openingResult]⟩

theorem enumBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid enumBody :=
  enumBody_ordinary

theorem enumBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    enumBody input ≠ .invariant error :=
  enumBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.EnumInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumDeclSoundnessProperties`
-/

/-! Success soundness for complete algebraic enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem enumDeclBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected =>
      rw [firstResult] at result
      contradiction
  | invariant error =>
      rw [firstResult] at result
      contradiction

/-- Every successful enum declaration follows its exact retained grammar. -/
theorem enumDecl_success_sound (deriveAttribute : Option DeriveAttribute)
    {input next : State} {declaration : EnumDecl}
    (result : enumDecl deriveAttribute input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses deriveAttribute
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold enumDecl at result
  rcases enumDeclBind_success_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases enumDeclBind_success_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .enum .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (optionalGenericParameters_success_sound parametersResult)
    (EnumInternals.enumBody_success_sound bodyResult)

/-- Enum grammar soundness composes with the supplied derive contract. -/
theorem enumDecl_success_sound_and_validFor
    (deriveAttribute : Option DeriveAttribute)
    {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (deriveValid : Option.ValidFor DeriveAttribute.ValidFor input.file
      deriveAttribute)
    (deriveStartsBeforeCurrent : ∀ derive ∈ deriveAttribute,
      derive.span.startByte ≤ input.currentSpan.startByte)
    (result : enumDecl deriveAttribute input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses deriveAttribute
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      EnumDecl.ValidFor input.file declaration := by
  refine ⟨enumDecl_success_sound deriveAttribute result, ?_⟩
  have valid := enumDecl_validFor deriveAttribute inputValid deriveValid
    deriveStartsBeforeCurrent
  rw [result] at valid
  exact valid.1

/-- The no-derive enum parser has unconditional grammar and validity soundness. -/
theorem enumDecl_none_success_sound_and_validFor
    {input next : State} {declaration : EnumDecl}
    (inputValid : input.ValidFor)
    (result : enumDecl none input = .ok declaration next) :
    DeclarativeGrammar.EnumDeclParses none input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      EnumDecl.ValidFor input.file declaration := by
  exact enumDecl_success_sound_and_validFor none inputValid
    (by trivial) (by simp) result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumDeclarationOrdinaryRejectionSoundnessProperties`
-/

/-! Exact ordinary-rejection bridge for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

/-- Every rejected enum declaration records the first rejecting stage among
its marker, name, optional generic parameters, and body. -/
theorem enumDecl_reject_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute)
    {input rejected : State} {failure : Failure}
    (result : enumDecl deriveAttribute input = .reject failure rejected) :
    DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold enumDecl at result
  cases markerResult : contextual .enum .topItem input with
  | invariant error => simp [bind, markerResult] at result
  | reject markerFailure markerRejected =>
      have markerRejectedEq := contextual_reject_state_eq .enum .topItem
        markerResult
      subst markerRejected
      simp only [bind, markerResult] at result
      cases result
      exact .markerMissing
        (contextual_reject_tokenKindAbsentAt .enum .topItem markerResult)
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      have markerParsed := contextual_success_exactTokenParses .enum .topItem
        markerResult
      cases nameResult : identifier .topItem afterMarker with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected marker.span markerParsed
            (identifier_reject_sound .topItem nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .topItem nameResult
          cases parametersResult : optionalGenericParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject parametersFailure parametersRejected =>
              simp only [parametersResult] at result
              cases result
              exact .parametersRejected marker.span markerParsed nameParsed
                (optionalGenericParameters_reject_sound parametersResult)
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              have parametersParsed :=
                optionalGenericParameters_ordinaryOutcome_sound.1
                  parametersResult
              cases bodyResult : EnumInternals.enumBody afterParameters with
              | invariant error => simp [bodyResult] at result
              | reject bodyFailure bodyRejected =>
                  simp only [bodyResult] at result
                  cases result
                  exact .bodyRejected marker.span markerParsed nameParsed
                    parametersParsed
                    (EnumInternals.enumBody_reject_ordinaryOutcome_sound
                      bodyResult)
              | ok body output => simp [bodyResult, pure] at result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumDeclarationOrdinarySuccessSoundnessProperties`
-/

/-! Ordinary-success bridge for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful enum declaration follows the exact ordinary grammar for
the supplied, non-consuming derive attribute. -/
theorem enumDecl_success_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute)
    {input output : State} {declaration : EnumDecl}
    (result : enumDecl deriveAttribute input = .ok declaration output) :
    DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
      input.declarativeRemainder declaration output.declarativeRemainder :=
  enumDecl_success_sound deriveAttribute result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumDeclarationOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package enum-declaration success and exact four-stage rejection. -/
theorem enumDecl_ordinaryOutcome_sound
    (deriveAttribute : Option DeriveAttribute) :
    (∀ {input output : State} {declaration : EnumDecl},
      enumDecl deriveAttribute input = .ok declaration output →
        DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      enumDecl deriveAttribute input = .reject failure rejected →
        DeclarativeGrammar.EnumDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨enumDecl_success_ordinaryOutcome_sound deriveAttribute,
    enumDecl_reject_ordinaryOutcome_sound deriveAttribute⟩

/-- Re-export deterministic and exclusive outcomes for one supplied derive
attribute. -/
theorem enumDecl_ordinaryOutcomeSpec
    (deriveAttribute : Option DeriveAttribute) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute)
      DeclarativeGrammar.EnumDeclRejects :=
  DeclarativeGrammar.enumDeclDeterministicOutcomeSpec deriveAttribute

/-- Re-export exact enum-declaration outcomes at any fixed derive attribute. -/
theorem enumDecl_exactOutcomeSpec
    (deriveAttribute : Option DeriveAttribute) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.EnumDeclOrdinaryParses deriveAttribute)
      DeclarativeGrammar.EnumDeclRejects :=
  DeclarativeGrammar.enumDeclExactOutcomeSpec deriveAttribute

/-- At any fixed derive attribute, successful enum declarations fix their AST
and declarative remainder. -/
theorem enumDecl_success_result_unique
    (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State} {left right : EnumDecl}
    (leftResult : enumDecl deriveAttribute input = .ok left leftOutput)
    (rightResult : enumDecl deriveAttribute input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumDeclOrdinaryParses.result_unique deriveAttribute
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute leftResult)
    (enumDecl_success_ordinaryOutcome_sound deriveAttribute rightResult)

/-- At any fixed derive attribute, enum-declaration rejections have one
declarative endpoint. -/
theorem enumDecl_reject_output_unique
    (deriveAttribute : Option DeriveAttribute)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : enumDecl deriveAttribute input = .reject leftFailure leftOutput)
    (rightResult : enumDecl deriveAttribute input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.EnumDeclRejects.output_unique
    (enumDecl_reject_ordinaryOutcome_sound deriveAttribute leftResult)
    (enumDecl_reject_ordinaryOutcome_sound deriveAttribute rightResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.EnumDeclarationTotalityProperties`
-/

/-! Valid-input totality for complete canonical enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of an enum declaration has an ordinary outcome. -/
theorem enumDecl_invariantFreeOnValid
    (deriveAttribute : Option DeriveAttribute) :
    Parser.InvariantFreeOnValid (enumDecl deriveAttribute) := by
  unfold enumDecl
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .enum .topItem)
    (contextual_ordinary .enum .topItem).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .topItem)
    (identifier_ordinary .topItem).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    optionalGenericParameters_validFor
    optionalGenericParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    EnumInternals.enumBody_validFor
    EnumInternals.enumBody_invariantFreeOnValid
  intro body
  let startSpan := deriveAttribute.map (fun derive => derive.span)
    |>.getD marker.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover startSpan body.span
    value := {
      deriveAttribute
      name
      parameters
      bodySpan := body.span
      constructors := body.constructors
    }
  } : EnumDecl)

theorem enumDecl_ordinary
    (deriveAttribute : Option DeriveAttribute)
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next,
      enumDecl deriveAttribute input = .ok declaration next) ∨
      (∃ failure next,
        enumDecl deriveAttribute input = .reject failure next) :=
  enumDecl_invariantFreeOnValid deriveAttribute input inputValid

theorem enumDecl_ne_invariant
    (deriveAttribute : Option DeriveAttribute)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    enumDecl deriveAttribute input ≠ .invariant error :=
  (enumDecl_invariantFreeOnValid deriveAttribute).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
