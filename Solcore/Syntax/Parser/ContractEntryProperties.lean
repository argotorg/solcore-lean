import Solcore.Syntax.Parser.ContractEntry
import Solcore.Syntax.Parser.ParameterProperties
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ContractDeclarationValidity
import Solcore.Syntax.ParameterValidity

/-! Contracts for modifiers shared by constructors and fallback entries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

/-- Element provenance lifts directly to the complete parameter list. -/
theorem entryParameters_validFor_of_namedParameter
    (elementContract : namedParameter.ValidFor FunctionParameter.ValidFor) :
    entryParameters.ValidFor
      (DelimitedList.ValidFor FunctionParameter.ValidFor) := by
  unfold entryParameters
  exact delimited_validFor FunctionParameter.ValidFor .leftParen .rightParen
    true namedParameter .parameter .topLevel elementContract
      namedParameter_preservesTokensOnSuccess

/-- Contract-entry parameter lists retain every parameter's provenance. -/
theorem entryParameters_validFor :
    entryParameters.ValidFor
      (DelimitedList.ValidFor FunctionParameter.ValidFor) :=
  entryParameters_validFor_of_namedParameter namedParameter_validFor

/-- Contract-entry parameter lists preserve every ordinary token window. -/
theorem entryParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow entryParameters := by
  unfold entryParameters
  exact delimited_preservesTokenWindow .leftParen .rightParen true
    namedParameter .parameter .topLevel namedParameter_preservesTokenWindow

theorem entryParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess entryParameters :=
  entryParameters_preservesTokenWindow.preservesTokensOnSuccess

/-- A complete parameter list never rewinds its input cursor. -/
theorem entryParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess entryParameters := by
  unfold entryParameters
  exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel

/-- A complete parameter list starts at its opening parenthesis. -/
theorem entryParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess entryParameters (·.span) := by
  unfold entryParameters
  exact delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel

private theorem entryBind_ok_components {α β : Type} {first : Parser α}
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

private theorem getState_preservesTokenWindowForEntry :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForEntry
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

/-- An optional modifier retains a valid marker whenever it is present. -/
theorem optionalModifier_validFor (modifier : HardKeyword) :
    (optionalModifier modifier).ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold optionalModifier
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (keyword_validFor modifier .contractMember)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional modifier parsing preserves every ordinary token window. -/
theorem optionalModifier_preservesTokenWindow (modifier : HardKeyword) :
    Parser.PreservesTokenWindow (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_preservesTokenWindow getState_preservesTokenWindowForEntry
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow modifier .contractMember)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalModifier_preservesTokensOnSuccess (modifier : HardKeyword) :
    Parser.PreservesTokensOnSuccess (optionalModifier modifier) :=
  (optionalModifier_preservesTokenWindow modifier).preservesTokensOnSuccess

/-- Optional modifier parsing never rewinds the parser cursor. -/
theorem optionalModifier_cursorMonotoneOnSuccess (modifier : HardKeyword) :
    Parser.CursorMonotoneOnSuccess (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed modifier
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess modifier .contractMember)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present optional modifier starts at the current keyword token. -/
theorem optionalModifier_some_startsAtCurrentTokenOnSuccess
    (modifier : HardKeyword) {input final : State} {span : SourceSpan}
    (parsed : optionalModifier modifier input = .ok (some span) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = span.startByte := by
  unfold optionalModifier getState at parsed
  simp only [bind] at parsed
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at parsed
    rcases entryBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, finished⟩
    have starts := acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword modifier) .contractMember (· == .keyword modifier)
      input marker afterMarker markerResult
    cases finished
    exact starts
  · simp only [present] at parsed
    change Reply.ok none input = .ok (some span) final at parsed
    cases parsed

/-- Implicit-public handling retains only a valid optional payable marker. -/
theorem implicitPublicModifiers_validFor (declaration : HardKeyword) :
    (implicitPublicModifiers declaration).ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold implicitPublicModifiers
  apply Parser.bind_validFor_of_value (optionalModifier_validFor .publicKw)
  intro publicMarker input inputValid publicValid
  cases publicMarker with
  | none =>
      change (optionalModifier .payableKw input).ValidFor input _
      exact optionalModifier_validFor .payableKw input inputValid
  | some span =>
      simp only [Option.ValidFor] at publicValid
      let diagnostic : ParseDiagnostic := {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
      change (optionalModifier .payableKw (input.emit diagnostic)).ValidFor
        input _
      have emittedValid := inputValid.emit_validFor diagnostic publicValid
      exact (optionalModifier_validFor .payableKw
        (input.emit diagnostic) emittedValid).of_file_eq (by
          simp [State.emit])

/-- Implicit-public handling preserves every ordinary token window. -/
theorem implicitPublicModifiers_preservesTokenWindow
    (declaration : HardKeyword) :
    Parser.PreservesTokenWindow (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_preservesTokenWindow
    (optionalModifier_preservesTokenWindow .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      simp only
      exact optionalModifier_preservesTokenWindow .payableKw
  | some span =>
      simp only
      apply Parser.bind_preservesTokenWindow
        (emitDiagnostic_preservesTokenWindowForEntry _)
      intro _
      exact optionalModifier_preservesTokenWindow .payableKw

theorem implicitPublicModifiers_preservesTokensOnSuccess
    (declaration : HardKeyword) :
    Parser.PreservesTokensOnSuccess (implicitPublicModifiers declaration) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (implicitPublicModifiers_preservesTokenWindow declaration)

/-- Implicit-public handling never rewinds the parser cursor. -/
theorem implicitPublicModifiers_cursorMonotoneOnSuccess
    (declaration : HardKeyword) :
    Parser.CursorMonotoneOnSuccess (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalModifier_cursorMonotoneOnSuccess .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      simp only
      exact optionalModifier_cursorMonotoneOnSuccess .payableKw
  | some span =>
      simp only
      apply Parser.bind_cursorMonotoneOnSuccess
        (emitDiagnostic_cursorMonotoneOnSuccess _)
      intro _
      exact optionalModifier_cursorMonotoneOnSuccess .payableKw

/-- The state-indexed required-body parser retains its opening-brace start. -/
theorem requiredBlock_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (block .require) (·.span) := by
  intro input body next parsed
  unfold block at parsed
  exact coreBlock_startsAtCurrentTokenOnSuccess _ .require
    input body next parsed

end ContractEntryInternals

/-- A constructor's keyword-to-body cover is source-valid. -/
theorem constructorDecl_span_validOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    {input final : State} {declaration : ConstructorDecl}
    (inputValid : input.ValidFor)
    (parsed : constructorDecl input = .ok declaration final) :
    declaration.span.ValidFor input.file := by
  have stages := parsed
  unfold constructorDecl at stages
  rcases ContractEntryInternals.entryBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  have markerContract := keyword_validFor .constructorKw .contractMember
    input inputValid
  rw [markerResult] at markerContract
  have parametersContract := ContractEntryInternals.entryParameters_validFor
    afterMarker markerContract.2.1
  rw [parametersResult] at parametersContract
  have modifiersContract :=
    ContractEntryInternals.implicitPublicModifiers_validFor .constructorKw
      afterParameters parametersContract.2.1
  rw [modifiersResult] at modifiersContract
  have isolatedValid := isolateBlock_validFor statementValid
    (block .require) bodyValid
  have bodyContract := isolatedValid afterModifiers modifiersContract.2.1
  rw [bodyResult] at bodyContract
  have markerValidInput : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerContract.1
  have bodyValidInput : Block.ValidFor statementValid input.file body := by
    simpa [bodyContract.2.2, modifiersContract.2.2,
      parametersContract.2.2, markerContract.2.2] using bodyContract.1
  rcases isolateBlock_startsAtCurrentTokenOnSuccess (block .require)
      ContractEntryInternals.requiredBlock_startsAtCurrentTokenOnSuccess
      afterModifiers body afterBody bodyResult with
    ⟨opening, openingFound, bodyStart⟩
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
    (acceptToken_ok_state_shape (.keyword .constructorKw) .contractMember
      (fun kind => kind == .keyword .constructorKw) markerResult).1
  have openingAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some openingFound
  have openingAt : input.tokens[afterModifiers.cursor]? = some opening := by
    simpa [
      ContractEntryInternals.implicitPublicModifiers_preservesTokensOnSuccess
        .constructorKw afterParameters payableMarker afterModifiers
          modifiersResult,
      ContractEntryInternals.entryParameters_preservesTokensOnSuccess
        afterMarker parameters afterParameters parametersResult,
      keyword_preservesTokensOnSuccess .constructorKw .contractMember
        input marker afterMarker markerResult] using openingAtAfter
  have cursorOrder : input.cursor < afterModifiers.cursor :=
    Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.keyword .constructorKw)
        .contractMember (fun kind => kind == .keyword .constructorKw)
        markerResult)
      (Nat.le_trans
        (ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
          afterMarker parameters afterParameters parametersResult)
        (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
          .constructorKw afterParameters payableMarker afterModifiers
            modifiersResult))
  have separated := inputValid.token_end_le_token_start_of_getElem?_lt
    markerAt openingAt cursorOrder
  have ordered : marker.span.startByte ≤ body.span.endByte := by
    calc
      marker.span.startByte ≤ marker.span.endByte := markerValidInput.2.1
      _ ≤ opening.span.startByte := separated
      _ = body.span.startByte := bodyStart
      _ ≤ body.span.endByte := bodyValidInput.1.2.1
  cases finished
  exact SourceSpan.cover_validFor markerValidInput bodyValidInput.1 ordered

/-- Constructors retain valid inner syntax when their isolated body does. -/
theorem constructorDecl_validFor_of_span
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (isolateBlock (block .require)).ValidFor
      (Block.ValidFor statementValid))
    (spanValidOnSuccess : ∀ input declaration next,
      input.ValidFor → constructorDecl input = .ok declaration next →
      declaration.span.ValidFor input.file) :
    constructorDecl.ValidFor (ConstructorDecl.ValidFor statementValid) := by
  have weak : constructorDecl.ValidFor (fun _ _ => True) := by
    unfold constructorDecl
    apply Parser.bind_validFor
      (keyword_validFor .constructorKw .contractMember)
    intro marker
    apply Parser.bind_validFor
      ContractEntryInternals.entryParameters_validFor
    intro parameters
    apply Parser.bind_validFor
      (ContractEntryInternals.implicitPublicModifiers_validFor .constructorKw)
    intro payableMarker
    apply Parser.bind_validFor bodyValid
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : constructorDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold constructorDecl at stages
      rcases ContractEntryInternals.entryBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases ContractEntryInternals.entryBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases ContractEntryInternals.entryBind_ok_components rest with
        ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
      rcases ContractEntryInternals.entryBind_ok_components rest with
        ⟨body, afterBody, bodyResult, finished⟩
      have markerContract := keyword_validFor .constructorKw .contractMember
        input inputValid
      rw [markerResult] at markerContract
      have parametersContract :=
        ContractEntryInternals.entryParameters_validFor afterMarker
          markerContract.2.1
      rw [parametersResult] at parametersContract
      have modifiersContract :=
        ContractEntryInternals.implicitPublicModifiers_validFor .constructorKw
          afterParameters parametersContract.2.1
      rw [modifiersResult] at modifiersContract
      have bodyContract := bodyValid afterModifiers modifiersContract.2.1
      rw [bodyResult] at bodyContract
      have parametersValidInput : DelimitedList.ValidFor
          FunctionParameter.ValidFor input.file parameters := by
        simpa [parametersContract.2.2, markerContract.2.2] using
          parametersContract.1
      have payableValidInput : Option.ValidFor
          (fun file span => span.ValidFor file) input.file payableMarker := by
        simpa [modifiersContract.2.2, parametersContract.2.2,
          markerContract.2.2] using modifiersContract.1
      have bodyValidInput : Block.ValidFor statementValid input.file body := by
        simpa [bodyContract.2.2, modifiersContract.2.2,
          parametersContract.2.2, markerContract.2.2] using bodyContract.1
      have payableRetained : ∀ retained ∈ payableMarker,
          retained.ValidFor input.file := by
        cases payableMarker with
        | none => simp
        | some marker =>
            intro retained member
            have retainedEq : retained = marker := by simpa using member.symm
            subst retained
            simpa only [Option.ValidFor] using payableValidInput
      have outerValid := spanValidOnSuccess input declaration final inputValid
        parsed
      cases finished
      exact ⟨⟨outerValid, parametersValidInput.1,
        parametersValidInput.2, payableRetained, bodyValidInput.1,
        bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩

/-- Complete constructors retain only source-valid syntax. -/
theorem constructorDecl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid)) :
    constructorDecl.ValidFor (ConstructorDecl.ValidFor statementValid) :=
  constructorDecl_validFor_of_span statementValid
    (isolateBlock_validFor statementValid (block .require) bodyValid)
    (fun _ _ _ inputValid parsed =>
      constructorDecl_span_validOnSuccess statementValid bodyValid inputValid
        parsed)

/-- Constructor parsing preserves every ordinary token window. -/
theorem constructorDecl_preservesTokenWindow
    (bodyShape : Parser.PreservesTokenWindow (block .require)) :
    Parser.PreservesTokenWindow constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .constructorKw .contractMember)
  intro marker
  apply Parser.bind_preservesTokenWindow
    ContractEntryInternals.entryParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow
    (ContractEntryInternals.implicitPublicModifiers_preservesTokenWindow
      .constructorKw)
  intro payableMarker
  apply Parser.bind_preservesTokenWindow
    (isolateBlock_preservesTokenWindow (block .require) bodyShape)
  intro body
  exact Parser.pure_preservesTokenWindow _

theorem constructorDecl_preservesTokensOnSuccess
    (bodyShape : Parser.PreservesTokenWindow (block .require)) :
    Parser.PreservesTokensOnSuccess constructorDecl :=
  (constructorDecl_preservesTokenWindow bodyShape).preservesTokensOnSuccess

/-- Constructor parsing is cursor-monotone when its body parser is. -/
theorem constructorDecl_cursorMonotoneOnSuccess
    (bodyMonotone : Parser.CursorMonotoneOnSuccess (block .require)) :
    Parser.CursorMonotoneOnSuccess constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .constructorKw .contractMember)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
      .constructorKw)
  intro payableMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (isolateBlock_cursorMonotoneOnSuccess (block .require) bodyMonotone)
  intro body
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A constructor declaration starts at its `constructor` keyword. -/
theorem constructorDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess constructorDecl (·.span) := by
  unfold constructorDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .constructorKw)
      .contractMember (· == .keyword .constructorKw))
  intro marker input declaration final parsed
  rcases ContractEntryInternals.entryBind_ok_components parsed with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  rfl

/-- A fallback's keyword-to-body cover is source-valid in every parameter branch. -/
theorem fallbackDecl_span_validOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    {input final : State} {declaration : FallbackDecl}
    (inputValid : input.ValidFor)
    (parsed : fallbackDecl input = .ok declaration final) :
    declaration.span.ValidFor input.file := by
  have stages := parsed
  unfold fallbackDecl at stages
  rcases ContractEntryInternals.entryBind_ok_components stages with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases ContractEntryInternals.entryBind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  have markerContract := keyword_validFor .fallbackKw .contractMember
    input inputValid
  rw [markerResult] at markerContract
  have parametersContract := ContractEntryInternals.entryParameters_validFor
    afterMarker markerContract.2.1
  rw [parametersResult] at parametersContract
  have markerValidInput : marker.span.ValidFor input.file := by
    simpa only [Located.ValidFor] using markerContract.1
  have markerAt := State.getElem?_eq_some_of_peek?_eq_some
    (acceptToken_ok_state_shape (.keyword .fallbackKw) .contractMember
      (fun kind => kind == .keyword .fallbackKw) markerResult).1
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true] at rest
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    have modifiersContract :=
      ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw
        afterParameters parametersContract.2.1
    rw [modifiersResult] at modifiersContract
    have bodyContract := isolateBlock_validFor statementValid
      (block .require) bodyValid afterModifiers modifiersContract.2.1
    rw [bodyResult] at bodyContract
    have bodyValidInput : Block.ValidFor statementValid input.file body := by
      simpa [bodyContract.2.2, modifiersContract.2.2,
        parametersContract.2.2, markerContract.2.2] using bodyContract.1
    rcases isolateBlock_startsAtCurrentTokenOnSuccess (block .require)
        ContractEntryInternals.requiredBlock_startsAtCurrentTokenOnSuccess
        afterModifiers body afterBody bodyResult with
      ⟨opening, openingFound, bodyStart⟩
    have openingAtAfter :=
      State.getElem?_eq_some_of_peek?_eq_some openingFound
    have openingAt : input.tokens[afterModifiers.cursor]? = some opening := by
      simpa [
        ContractEntryInternals.implicitPublicModifiers_preservesTokensOnSuccess
          .fallbackKw afterParameters payableMarker afterModifiers
            modifiersResult,
        ContractEntryInternals.entryParameters_preservesTokensOnSuccess
          afterMarker parameters afterParameters parametersResult,
        keyword_preservesTokensOnSuccess .fallbackKw .contractMember
          input marker afterMarker markerResult] using openingAtAfter
    have cursorOrder : input.cursor < afterModifiers.cursor :=
      Nat.lt_of_lt_of_le
        (acceptToken_cursor_lt_onSuccess (.keyword .fallbackKw)
          .contractMember (fun kind => kind == .keyword .fallbackKw)
          markerResult)
        (Nat.le_trans
          (ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
            afterMarker parameters afterParameters parametersResult)
          (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
            .fallbackKw afterParameters payableMarker afterModifiers
              modifiersResult))
    have separated := inputValid.token_end_le_token_start_of_getElem?_lt
      markerAt openingAt cursorOrder
    have ordered : marker.span.startByte ≤ body.span.endByte := by
      calc
        marker.span.startByte ≤ marker.span.endByte := markerValidInput.2.1
        _ ≤ opening.span.startByte := separated
        _ = body.span.startByte := bodyStart
        _ ≤ body.span.endByte := bodyValidInput.1.2.1
    cases finished
    exact SourceSpan.cover_validFor markerValidInput bodyValidInput.1 ordered
  · simp only [empty, Bool.false_eq_true, if_false] at rest
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨_, afterValidation, validationResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    let diagnostic : ParseDiagnostic := {
      span := parameters.span
      kind := .constraintViolation .fallbackRequiresNoParameters
    }
    have diagnosticValid : diagnostic.span.ValidFor afterParameters.file := by
      simpa [diagnostic, parametersContract.2.2] using parametersContract.1.1
    have validationContract := emitDiagnostic_reply_validFor
      parametersContract.2.1 diagnostic diagnosticValid
    rw [validationResult] at validationContract
    have modifiersContract :=
      ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw
        afterValidation validationContract.2.1
    rw [modifiersResult] at modifiersContract
    have bodyContract := isolateBlock_validFor statementValid
      (block .require) bodyValid afterModifiers modifiersContract.2.1
    rw [bodyResult] at bodyContract
    have bodyValidInput : Block.ValidFor statementValid input.file body := by
      simpa [bodyContract.2.2, modifiersContract.2.2,
        validationContract.2.2, parametersContract.2.2,
        markerContract.2.2] using bodyContract.1
    rcases isolateBlock_startsAtCurrentTokenOnSuccess (block .require)
        ContractEntryInternals.requiredBlock_startsAtCurrentTokenOnSuccess
        afterModifiers body afterBody bodyResult with
      ⟨opening, openingFound, bodyStart⟩
    have openingAtAfter :=
      State.getElem?_eq_some_of_peek?_eq_some openingFound
    have openingAt : input.tokens[afterModifiers.cursor]? = some opening := by
      simpa [
        ContractEntryInternals.implicitPublicModifiers_preservesTokensOnSuccess
          .fallbackKw afterValidation payableMarker afterModifiers
            modifiersResult,
        emitDiagnostic_preservesTokensOnSuccess diagnostic afterParameters ()
          afterValidation validationResult,
        ContractEntryInternals.entryParameters_preservesTokensOnSuccess
          afterMarker parameters afterParameters parametersResult,
        keyword_preservesTokensOnSuccess .fallbackKw .contractMember
          input marker afterMarker markerResult] using openingAtAfter
    have cursorOrder : input.cursor < afterModifiers.cursor :=
      Nat.lt_of_lt_of_le
        (acceptToken_cursor_lt_onSuccess (.keyword .fallbackKw)
          .contractMember (fun kind => kind == .keyword .fallbackKw)
          markerResult)
        (Nat.le_trans
          (ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
            afterMarker parameters afterParameters parametersResult)
          (Nat.le_trans
            (emitDiagnostic_cursorMonotoneOnSuccess diagnostic afterParameters
              () afterValidation validationResult)
            (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
              .fallbackKw afterValidation payableMarker afterModifiers
                modifiersResult)))
    have separated := inputValid.token_end_le_token_start_of_getElem?_lt
      markerAt openingAt cursorOrder
    have ordered : marker.span.startByte ≤ body.span.endByte := by
      calc
        marker.span.startByte ≤ marker.span.endByte := markerValidInput.2.1
        _ ≤ opening.span.startByte := separated
        _ = body.span.startByte := bodyStart
        _ ≤ body.span.endByte := bodyValidInput.1.2.1
    cases finished
    exact SourceSpan.cover_validFor markerValidInput bodyValidInput.1 ordered

/-- Fallback entries retain valid inner syntax across parameter diagnostics. -/
theorem fallbackDecl_validFor_of_span
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (isolateBlock (block .require)).ValidFor
      (Block.ValidFor statementValid))
    (spanValidOnSuccess : ∀ input declaration next,
      input.ValidFor → fallbackDecl input = .ok declaration next →
      declaration.span.ValidFor input.file) :
    fallbackDecl.ValidFor (FallbackDecl.ValidFor statementValid) := by
  have weak : fallbackDecl.ValidFor (fun _ _ => True) := by
    unfold fallbackDecl
    apply Parser.bind_validFor
      (keyword_validFor .fallbackKw .contractMember)
    intro marker
    apply Parser.bind_validFor_of_value
      ContractEntryInternals.entryParameters_validFor
    intro parameters input inputValid parametersValid
    have remainderValid : (do
        let payableMarker ←
          ContractEntryInternals.implicitPublicModifiers .fallbackKw
        let body ← isolateBlock (block .require)
        pure (show FallbackDecl from {
          span := SourceSpan.cover marker.span body.span
          value := { parameters, payableMarker, body }
        })).ValidFor (fun _ _ => True) := by
      apply Parser.bind_validFor
        (ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw)
      intro payableMarker
      apply Parser.bind_validFor bodyValid
      intro body
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    by_cases empty : parameters.elements.isEmpty
    · simp only [empty, if_true]
      exact remainderValid input inputValid
    · simp only [empty, Bool.false_eq_true, if_false]
      let diagnostic : ParseDiagnostic := {
        span := parameters.span
        kind := .constraintViolation .fallbackRequiresNoParameters
      }
      have diagnosticValid : diagnostic.span.ValidFor input.file := by simpa [diagnostic] using parametersValid.1
      have emittedValid := inputValid.emit_validFor diagnostic diagnosticValid
      have remainderReply := remainderValid (input.emit diagnostic) emittedValid
      have retargeted := remainderReply.of_file_eq (other := input) (by
        simp [State.emit])
      simpa [diagnostic, emitDiagnostic, modifyState, bind, State.emit] using
        retargeted
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : fallbackDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold fallbackDecl at stages
      rcases ContractEntryInternals.entryBind_ok_components stages with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases ContractEntryInternals.entryBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      have markerContract := keyword_validFor .fallbackKw .contractMember
        input inputValid
      rw [markerResult] at markerContract
      have parametersContract :=
        ContractEntryInternals.entryParameters_validFor afterMarker
          markerContract.2.1
      rw [parametersResult] at parametersContract
      have parametersValidInput : DelimitedList.ValidFor
          FunctionParameter.ValidFor input.file parameters := by
        simpa [parametersContract.2.2, markerContract.2.2] using
          parametersContract.1
      have outerValid := spanValidOnSuccess input declaration final inputValid
        parsed
      by_cases empty : parameters.elements.isEmpty
      · simp only [empty, if_true] at rest
        rcases ContractEntryInternals.entryBind_ok_components rest with
          ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
        rcases ContractEntryInternals.entryBind_ok_components rest with
          ⟨body, afterBody, bodyResult, finished⟩
        have modifiersContract :=
          ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw
            afterParameters parametersContract.2.1
        rw [modifiersResult] at modifiersContract
        have bodyContract := bodyValid afterModifiers modifiersContract.2.1
        rw [bodyResult] at bodyContract
        have payableValidInput : Option.ValidFor
            (fun file span => span.ValidFor file) input.file payableMarker := by
          simpa [modifiersContract.2.2, parametersContract.2.2,
            markerContract.2.2] using modifiersContract.1
        have bodyValidInput : Block.ValidFor statementValid input.file body := by
          simpa [bodyContract.2.2, modifiersContract.2.2,
            parametersContract.2.2, markerContract.2.2] using bodyContract.1
        have payableRetained : ∀ retained ∈ payableMarker, retained.ValidFor input.file := by
          cases payableMarker <;> simp_all [Option.ValidFor]
        cases finished
        exact ⟨⟨outerValid, parametersValidInput.1,
          parametersValidInput.2, payableRetained, bodyValidInput.1,
          bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩
      · simp only [empty, Bool.false_eq_true, if_false] at rest
        rcases ContractEntryInternals.entryBind_ok_components rest with
          ⟨_, afterValidation, validationResult, rest⟩
        rcases ContractEntryInternals.entryBind_ok_components rest with
          ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
        rcases ContractEntryInternals.entryBind_ok_components rest with
          ⟨body, afterBody, bodyResult, finished⟩
        let diagnostic : ParseDiagnostic := {
          span := parameters.span
          kind := .constraintViolation .fallbackRequiresNoParameters
        }
        have diagnosticValid : diagnostic.span.ValidFor afterParameters.file := by
          simpa [diagnostic, parametersContract.2.2] using parametersContract.1.1
        have validationContract := emitDiagnostic_reply_validFor
          parametersContract.2.1 diagnostic diagnosticValid
        rw [validationResult] at validationContract
        have modifiersContract :=
          ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw
            afterValidation validationContract.2.1
        rw [modifiersResult] at modifiersContract
        have bodyContract := bodyValid afterModifiers modifiersContract.2.1
        rw [bodyResult] at bodyContract
        have payableValidInput : Option.ValidFor
            (fun file span => span.ValidFor file) input.file payableMarker := by
          simpa [modifiersContract.2.2, validationContract.2.2,
            parametersContract.2.2, markerContract.2.2] using
            modifiersContract.1
        have bodyValidInput : Block.ValidFor statementValid input.file body := by
          simpa [bodyContract.2.2, modifiersContract.2.2,
            validationContract.2.2, parametersContract.2.2,
            markerContract.2.2] using bodyContract.1
        have payableRetained : ∀ retained ∈ payableMarker, retained.ValidFor input.file := by
          cases payableMarker <;> simp_all [Option.ValidFor]
        cases finished
        exact ⟨⟨outerValid, parametersValidInput.1,
          parametersValidInput.2, payableRetained, bodyValidInput.1,
          bodyValidInput.2⟩, weakResult.2.1, weakResult.2.2⟩

/-- Complete fallback declarations retain only source-valid syntax. -/
theorem fallbackDecl_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid)) :
    fallbackDecl.ValidFor (FallbackDecl.ValidFor statementValid) :=
  fallbackDecl_validFor_of_span statementValid
    (isolateBlock_validFor statementValid (block .require) bodyValid)
    (fun _ _ _ inputValid parsed =>
      fallbackDecl_span_validOnSuccess statementValid bodyValid inputValid
        parsed)

/-- Fallback parsing preserves windows across its diagnostic branch. -/
theorem fallbackDecl_preservesTokenWindow
    (bodyShape : Parser.PreservesTokenWindow (block .require)) :
    Parser.PreservesTokenWindow fallbackDecl := by
  unfold fallbackDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .fallbackKw .contractMember)
  intro marker
  apply Parser.bind_preservesTokenWindow
    ContractEntryInternals.entryParameters_preservesTokenWindow
  intro parameters
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true]
    apply Parser.bind_preservesTokenWindow
      (ContractEntryInternals.implicitPublicModifiers_preservesTokenWindow
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_preservesTokenWindow
      (isolateBlock_preservesTokenWindow (block .require) bodyShape)
    intro body
    exact Parser.pure_preservesTokenWindow _
  · simp only [empty, Bool.false_eq_true, if_false]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindow _)
    intro _
    apply Parser.bind_preservesTokenWindow
      (ContractEntryInternals.implicitPublicModifiers_preservesTokenWindow
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_preservesTokenWindow
      (isolateBlock_preservesTokenWindow (block .require) bodyShape)
    intro body
    exact Parser.pure_preservesTokenWindow _

theorem fallbackDecl_preservesTokensOnSuccess
    (bodyShape : Parser.PreservesTokenWindow (block .require)) :
    Parser.PreservesTokensOnSuccess fallbackDecl :=
  (fallbackDecl_preservesTokenWindow bodyShape).preservesTokensOnSuccess

/-- Fallback parsing never rewinds, including parameter diagnostics. -/
theorem fallbackDecl_cursorMonotoneOnSuccess
    (bodyMonotone : Parser.CursorMonotoneOnSuccess (block .require)) :
    Parser.CursorMonotoneOnSuccess fallbackDecl := by
  unfold fallbackDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .fallbackKw .contractMember)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    ContractEntryInternals.entryParameters_cursorMonotoneOnSuccess
  intro parameters
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_cursorMonotoneOnSuccess
      (isolateBlock_cursorMonotoneOnSuccess (block .require) bodyMonotone)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [empty, Bool.false_eq_true, if_false]
    apply Parser.bind_cursorMonotoneOnSuccess
      (emitDiagnostic_cursorMonotoneOnSuccess _)
    intro _
    apply Parser.bind_cursorMonotoneOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_cursorMonotoneOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_cursorMonotoneOnSuccess
      (isolateBlock_cursorMonotoneOnSuccess (block .require) bodyMonotone)
    intro body
    exact Parser.pure_cursorMonotoneOnSuccess _

/-- A fallback declaration starts at its `fallback` keyword. -/
theorem fallbackDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess fallbackDecl (·.span) := by
  unfold fallbackDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .fallbackKw)
      .contractMember (· == .keyword .fallbackKw))
  intro marker input declaration final parsed
  rcases ContractEntryInternals.entryBind_ok_components parsed with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true] at rest
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    rfl
  · simp only [empty, Bool.false_eq_true, if_false] at rest
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨_, afterValidation, validationResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases ContractEntryInternals.entryBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    rfl

end Solcore.Syntax.Parser
