import Solcore.Syntax.Parser.Function
import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.ParameterProperties
import Solcore.Syntax.CollectionValidity
import Solcore.Syntax.ContractDeclarationValidity
import Solcore.Syntax.ParameterValidity
import Solcore.Syntax.Parser.NamedParameterTotalityProperties
import Solcore.Syntax.Parser.PublicCoreTermTotalityProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties
import Solcore.Syntax.DeclarativeConstructorDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ContractEntryInternals

def entryParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

/-- Parse one optional contract-entry modifier marker. -/
def optionalModifier (modifier : HardKeyword) : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state modifier then
    pure (some (← keyword modifier .contractMember).span)
  else
    pure none

def implicitPublicModifiers
    (declaration : HardKeyword) : Parser (Option SourceSpan) := do
  let publicMarker ← optionalModifier .publicKw
  match publicMarker with
  | some span =>
      let _ ← emitDiagnostic {
        span
        kind := .constraintViolation (.implicitPublicModifier declaration)
      }
  | none => pure ()
  optionalModifier .payableKw

end ContractEntryInternals

/-- Parse a contract constructor with an explicitly non-tail body. -/
def constructorDecl : Parser ConstructorDecl := do
  let marker ← keyword .constructorKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .constructorKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

/-- Parse a fallback entry point while retaining invalid parameters. -/
def fallbackDecl : Parser FallbackDecl := do
  let marker ← keyword .fallbackKw .contractMember
  let parameters ← ContractEntryInternals.entryParameters
  if parameters.elements.isEmpty then
    pure ()
  else
    let _ ← emitDiagnostic {
      span := parameters.span
      kind := .constraintViolation .fallbackRequiresNoParameters
    }
  let payableMarker ←
    ContractEntryInternals.implicitPublicModifiers .fallbackKw
  let body ← isolateBlock (block .require)
  pure {
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  }

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryDiagnosticReflectionProperties`
-/

/-! Backward diagnostic reflection for constructor and fallback entry leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

/-- Contract-entry parameter parsing cannot erase incoming diagnostics. -/
theorem entryParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess entryParameters := by
  simpa [entryParameters, functionParameters] using
    functionParameters_reflectsDiagnosticFreeOnSuccess

/-- One optional entry modifier cannot erase incoming diagnostics. -/
theorem optionalModifier_reflectsDiagnosticFreeOnSuccess
    (modifier : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess (optionalModifier modifier) := by
  unfold optionalModifier
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess modifier .contractMember)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/--
Implicit-public validation and its following optional payable marker never
remove diagnostics.  An explicit `public` success is therefore incompatible
with a diagnostic-free result.
-/
theorem implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
    (declaration : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (implicitPublicModifiers declaration) := by
  unfold implicitPublicModifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalModifier_reflectsDiagnosticFreeOnSuccess .publicKw)
  intro publicMarker
  cases publicMarker with
  | none =>
      exact optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw
  | some span =>
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
      intro emitted
      exact optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw

end ContractEntryInternals

/-- Constructor parsing reflects diagnostic freedom through its required body. -/
theorem constructorDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .constructorKw .contractMember)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ContractEntryInternals.entryParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
      .constructorKw)
  intro payableMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Fallback validation and parsing reflect diagnostic freedom through the body. -/
theorem fallbackDecl_reflectsDiagnosticFreeOnSuccess
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require))) :
    Parser.ReflectsDiagnosticFreeOnSuccess fallbackDecl := by
  unfold fallbackDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .fallbackKw .contractMember)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    ContractEntryInternals.entryParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw)
    intro payableMarker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess bodyReflects
    intro body
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryProperties`
-/

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

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryHelperTotalityProperties`
-/

/-! Totality for parameter and modifier helpers shared by contract entries. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractEntryInternals

theorem entryParameters_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ values next, entryParameters input = .ok values next) ∨
      (∃ failure next, entryParameters input = .reject failure next) := by
  simpa only [entryParameters] using
    delimited_ordinary .leftParen .rightParen true namedParameter
      .parameter .topLevel namedParameter_elementTotalityContract
      input inputValid

theorem entryParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid entryParameters :=
  entryParameters_ordinary

theorem entryParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    entryParameters input ≠ .invariant error :=
  entryParameters_invariantFreeOnValid.ne_invariant input inputValid error

theorem optionalModifier_ordinary
    (modifier : HardKeyword)
    (input : State) (_inputValid : input.ValidFor) :
    (∃ value next, optionalModifier modifier input = .ok value next) ∨
      (∃ failure next,
        optionalModifier modifier input = .reject failure next) := by
  by_cases present : isKeyword input modifier
  · rcases (keyword_ordinary modifier .contractMember) input with
      ⟨marker, next, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · exact Or.inl ⟨some marker.span, next, by
        simp only [optionalModifier, getState, bind, present, ↓reduceIte,
          markerResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalModifier, getState, bind, present, ↓reduceIte,
          markerResult]⟩
  · have absent : isKeyword input modifier = false := by
      cases found : isKeyword input modifier with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalModifier, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalModifier_invariantFreeOnValid (modifier : HardKeyword) :
    Parser.InvariantFreeOnValid (optionalModifier modifier) :=
  optionalModifier_ordinary modifier

theorem optionalModifier_ne_invariant
    (modifier : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalModifier modifier input ≠ .invariant error :=
  (optionalModifier_invariantFreeOnValid modifier).ne_invariant
    input inputValid error

/-- Public-marker diagnostics preserve validity before optional payable parsing. -/
theorem implicitPublicModifiers_ordinary
    (declaration : HardKeyword)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next,
      implicitPublicModifiers declaration input = .ok value next) ∨
      (∃ failure next,
        implicitPublicModifiers declaration input = .reject failure next) := by
  rcases optionalModifier_ordinary .publicKw input inputValid with
    ⟨publicMarker, afterPublic, publicResult⟩ |
    ⟨failure, rejected, publicResult⟩
  · have publicReply := optionalModifier_validFor .publicKw input inputValid
    rw [publicResult] at publicReply
    cases publicMarker with
    | none =>
        rcases optionalModifier_ordinary .payableKw afterPublic
            publicReply.2.1 with
          ⟨payable, final, payableResult⟩ |
          ⟨failure, rejected, payableResult⟩
        · exact Or.inl ⟨payable, final, by
            simp only [implicitPublicModifiers, bind, publicResult,
              payableResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [implicitPublicModifiers, bind, publicResult,
              payableResult]⟩
    | some span =>
        have spanValid : span.ValidFor afterPublic.file := by
          simpa [Option.ValidFor, publicReply.2.2] using publicReply.1
        let diagnostic : ParseDiagnostic := {
          span
          kind := .constraintViolation (.implicitPublicModifier declaration)
        }
        have emittedValid := publicReply.2.1.emit_validFor diagnostic spanValid
        rcases optionalModifier_ordinary .payableKw
            (afterPublic.emit diagnostic) emittedValid with
          ⟨payable, final, payableResult⟩ |
          ⟨failure, rejected, payableResult⟩
        · exact Or.inl ⟨payable, final, by
            simp only [implicitPublicModifiers, bind, publicResult,
              emitDiagnostic, modifyState, diagnostic, payableResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [implicitPublicModifiers, bind, publicResult,
              emitDiagnostic, modifyState, diagnostic, payableResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [implicitPublicModifiers, bind, publicResult]⟩

theorem implicitPublicModifiers_invariantFreeOnValid
    (declaration : HardKeyword) :
    Parser.InvariantFreeOnValid (implicitPublicModifiers declaration) :=
  implicitPublicModifiers_ordinary declaration

theorem implicitPublicModifiers_ne_invariant
    (declaration : HardKeyword)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implicitPublicModifiers declaration input ≠ .invariant error :=
  (implicitPublicModifiers_invariantFreeOnValid declaration).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser.ContractEntryInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryDeclarationTotalityProperties`
-/

/-! Valid-input totality for constructor and fallback declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem constructorDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid constructorDecl := by
  unfold constructorDecl
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .constructorKw .contractMember)
    (keyword_ordinary .constructorKw .contractMember).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    ContractEntryInternals.entryParameters_validFor
    ContractEntryInternals.entryParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (ContractEntryInternals.implicitPublicModifiers_validFor .constructorKw)
    (ContractEntryInternals.implicitPublicModifiers_invariantFreeOnValid
      .constructorKw)
  intro payableMarker
  apply Parser.bind_invariantFreeOnValid
    (isolateBlock_validFor CoreStatement.ValidFor (block .require)
      (block_canonical_validFor .require))
    (BlockInternals.isolateBlock_invariantFreeOnValid
      (block .require) (block_invariantFreeOnValid .require))
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  } : ConstructorDecl)

theorem constructorDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, constructorDecl input = .ok declaration next) ∨
      (∃ failure next, constructorDecl input = .reject failure next) :=
  constructorDecl_invariantFreeOnValid input inputValid

theorem constructorDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    constructorDecl input ≠ .invariant error :=
  constructorDecl_invariantFreeOnValid.ne_invariant input inputValid error

private theorem fallbackTail_invariantFreeOnValid
    (marker : Token) (parameters : DelimitedList FunctionParameter) :
    Parser.InvariantFreeOnValid (do
      let payableMarker ←
        ContractEntryInternals.implicitPublicModifiers .fallbackKw
      let body ← isolateBlock (block .require)
      pure ({
        span := SourceSpan.cover marker.span body.span
        value := { parameters, payableMarker, body }
      } : FallbackDecl)) := by
  apply Parser.bind_invariantFreeOnValid
    (ContractEntryInternals.implicitPublicModifiers_validFor .fallbackKw)
    (ContractEntryInternals.implicitPublicModifiers_invariantFreeOnValid
      .fallbackKw)
  intro payableMarker
  apply Parser.bind_invariantFreeOnValid
    (isolateBlock_validFor CoreStatement.ValidFor (block .require)
      (block_canonical_validFor .require))
    (BlockInternals.isolateBlock_invariantFreeOnValid
      (block .require) (block_invariantFreeOnValid .require))
  intro body
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover marker.span body.span
    value := { parameters, payableMarker, body }
  } : FallbackDecl)

/-- Parameter diagnostics preserve validity before parsing the fallback tail. -/
theorem fallbackDecl_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ declaration next, fallbackDecl input = .ok declaration next) ∨
      (∃ failure next, fallbackDecl input = .reject failure next) := by
  rcases (keyword_ordinary .fallbackKw .contractMember) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .fallbackKw .contractMember
      input inputValid
    rw [markerResult] at markerReply
    rcases ContractEntryInternals.entryParameters_ordinary afterMarker
        markerReply.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersReply := ContractEntryInternals.entryParameters_validFor
        afterMarker markerReply.2.1
      rw [parametersResult] at parametersReply
      by_cases empty : parameters.elements.isEmpty
      · rcases fallbackTail_invariantFreeOnValid marker parameters
            afterParameters parametersReply.2.1 with
          ⟨declaration, final, tailResult⟩ |
          ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨declaration, final, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, ↓reduceIte, pure] using tailResult⟩
        · exact Or.inr ⟨failure, rejected, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, ↓reduceIte, pure] using tailResult⟩
      · have parametersValidAfter : DelimitedList.ValidFor
            FunctionParameter.ValidFor afterParameters.file parameters := by
          simpa [parametersReply.2.2] using parametersReply.1
        let diagnostic : ParseDiagnostic := {
          span := parameters.span
          kind := .constraintViolation .fallbackRequiresNoParameters
        }
        have emittedValid := parametersReply.2.1.emit_validFor diagnostic
          parametersValidAfter.1
        rcases fallbackTail_invariantFreeOnValid marker parameters
            (afterParameters.emit diagnostic) emittedValid with
          ⟨declaration, final, tailResult⟩ |
          ⟨failure, rejected, tailResult⟩
        · exact Or.inl ⟨declaration, final, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, Bool.false_eq_true, ↓reduceIte, emitDiagnostic,
              modifyState, diagnostic] using tailResult⟩
        · exact Or.inr ⟨failure, rejected, by
            simpa only [fallbackDecl, bind, markerResult, parametersResult,
              empty, Bool.false_eq_true, ↓reduceIte, emitDiagnostic,
              modifyState, diagnostic] using tailResult⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [fallbackDecl, bind, markerResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [fallbackDecl, bind, markerResult]⟩

theorem fallbackDecl_invariantFreeOnValid :
    Parser.InvariantFreeOnValid fallbackDecl :=
  fallbackDecl_ordinary

theorem fallbackDecl_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    fallbackDecl input ≠ .invariant error :=
  fallbackDecl_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryModifierSoundnessProperties`
-/

/-! Diagnostic-free soundness for constructor and fallback modifiers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

private theorem contractEntryModifierSoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
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
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Contract-entry parameters reuse the exact function-parameter grammar. -/
theorem entryParameters_success_sound {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : entryParameters input = .ok parameters next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_success_sound diagnosticFree result

/-- Parameter grammar soundness composes with retained-source validity. -/
theorem entryParameters_success_sound_and_validFor {input next : State}
    {parameters : DelimitedList FunctionParameter} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : entryParameters input = .ok parameters next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
        parameters next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file
        parameters := by
  refine ⟨entryParameters_success_sound diagnosticFree result, ?_⟩
  have valid := entryParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- One optional contract-entry modifier preserves exact keyword priority. -/
theorem optionalModifier_success_sound (modifier : HardKeyword)
    {input next : State} {marker : Option SourceSpan}
    (result : optionalModifier modifier input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses modifier
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at result
    cases markerResult : keyword modifier .contractMember input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses modifier .contractMember
            markerResult)
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (keywordAbsentAt_of_isKeyword_eq_false modifier absent)

private theorem optionalModifier_none_success
    (modifier : HardKeyword) {input next : State}
    (result : optionalModifier modifier input = .ok none next) :
    next = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.keyword modifier) := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · simp only [present, if_true] at result
    cases markerResult : keyword modifier .contractMember input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        injection result with valueEq stateEq
        contradiction
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact ⟨rfl, keywordAbsentAt_of_isKeyword_eq_false modifier absent⟩

/--
Diagnostic-free implicit-public handling excludes `public` and retains the
exact optional `payable` token.
-/
theorem implicitPublicModifiers_success_sound (declaration : HardKeyword)
    {input next : State} {payableMarker : Option SourceSpan}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker next) :
    DeclarativeGrammar.ContractEntryModifiersParses
      input.declarativeRemainder payableMarker next.declarativeRemainder := by
  unfold implicitPublicModifiers at result
  rcases contractEntryModifierSoundness_bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  cases publicMarker with
  | none =>
      rcases optionalModifier_none_success .publicKw publicResult with
        ⟨rfl, publicAbsent⟩
      have payableGrammar := optionalModifier_success_sound .payableKw rest
      exact ⟨publicAbsent, payableGrammar⟩
  | some publicSpan =>
      rcases contractEntryModifierSoundness_bind_ok_components rest with
        ⟨emitted, afterDiagnostic, diagnosticResult, payableResult⟩
      have afterDiagnosticFree :=
        optionalModifier_reflectsDiagnosticFreeOnSuccess .payableKw
          afterDiagnostic payableMarker next payableResult diagnosticFree
      unfold emitDiagnostic modifyState at diagnosticResult
      cases diagnosticResult
      simp [State.emit] at afterDiagnosticFree

/-- Modifier grammar soundness composes with retained-source validity. -/
theorem implicitPublicModifiers_success_sound_and_validFor
    (declaration : HardKeyword) {input next : State}
    {payableMarker : Option SourceSpan} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker next) :
    DeclarativeGrammar.ContractEntryModifiersParses
        input.declarativeRemainder payableMarker next.declarativeRemainder ∧
      Option.ValidFor (fun file span => span.ValidFor file) input.file
        payableMarker := by
  refine ⟨implicitPublicModifiers_success_sound declaration diagnosticFree
    result, ?_⟩
  have valid := implicitPublicModifiers_validFor declaration input inputValid
  rw [result] at valid
  exact valid.1

end ContractEntryInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntryModifierOrdinaryOutcomeSoundnessProperties`
-/

/-!
Executable ordinary outcomes for recovery-aware contract-entry parameters and
fixed-order implicit-public modifiers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace ContractEntryInternals

private theorem contractEntryModifierOrdinaryOutcome_bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
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
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Contract-entry parameters are definitionally the public recovery-aware
function-parameter parser. -/
theorem entryParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : DelimitedList FunctionParameter}
    (result : entryParameters input = .ok parameters output) :
    DeclarativeGrammar.FunctionParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_success_ordinaryOutcome_sound result

/-- Contract-entry parameter rejection preserves the exact public
function-parameter rejection endpoint. -/
theorem entryParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : entryParameters input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  simpa only [entryParameters, functionParameters] using
    functionParameters_reject_ordinaryOutcome_sound result

/-- Every successful implicit-public modifier parse retains the optional
explicit `public` marker in its derivation and the optional `payable` marker
in its output.  Emitting the implicit-public diagnostic changes no
declarative remainder. -/
theorem implicitPublicModifiers_success_ordinaryOutcome_sound
    (declaration : HardKeyword) {input output : State}
    {payableMarker : Option SourceSpan}
    (result : implicitPublicModifiers declaration input =
      .ok payableMarker output) :
    DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
      input.declarativeRemainder payableMarker
        output.declarativeRemainder := by
  unfold implicitPublicModifiers at result
  rcases contractEntryModifierOrdinaryOutcome_bind_ok_components result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  have publicParsed := optionalModifier_success_sound .publicKw publicResult
  cases publicMarker with
  | none =>
      exact .parsed publicParsed
        (optionalModifier_success_sound .payableKw rest)
  | some publicSpan =>
      rcases contractEntryModifierOrdinaryOutcome_bind_ok_components rest with
        ⟨emitted, afterDiagnostic, diagnosticResult, payableResult⟩
      unfold emitDiagnostic modifyState at diagnosticResult
      cases diagnosticResult
      have payableParsed :=
        optionalModifier_success_sound .payableKw payableResult
      exact .parsed publicParsed (by
        simpa only [State.declarativeRemainder, State.emit] using
          payableParsed)

private theorem optionalModifier_ne_reject
    (modifier : HardKeyword) {input rejected : State} {failure : Failure}
    (result : optionalModifier modifier input = .reject failure rejected) :
    False := by
  unfold optionalModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input modifier
  · rcases keyword_eq_ok_of_isKeyword_eq_true modifier .contractMember
        present with ⟨token, markerResult⟩
    simp [present, markerResult, pure] at result
  · have absent : isKeyword input modifier = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Fixed-order implicit-public modifiers cannot reject.  A present explicit
`public` marker emits a diagnostic and continues to optional `payable`. -/
theorem implicitPublicModifiers_ne_reject
    (declaration : HardKeyword) {input rejected : State} {failure : Failure}
    (result : implicitPublicModifiers declaration input =
      .reject failure rejected) : False := by
  unfold implicitPublicModifiers at result
  cases publicResult : optionalModifier .publicKw input with
  | invariant error => simp [bind, publicResult] at result
  | reject publicFailure publicRejected =>
      exact optionalModifier_ne_reject .publicKw publicResult
  | ok publicMarker afterPublic =>
      simp only [bind, publicResult] at result
      cases publicMarker with
      | none =>
          exact optionalModifier_ne_reject .payableKw result
      | some publicSpan =>
          unfold emitDiagnostic modifyState at result
          exact optionalModifier_ne_reject .payableKw result

end ContractEntryInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ContractEntrySoundnessProperties`
-/

/-! Parametric diagnostic-free soundness for constructors and fallbacks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contractEntrySoundness_bind_ok_components {alpha beta : Type}
    {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
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
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/--
Every diagnostic-free constructor success retains its exact marker,
parameters, strict modifier policy, and parser-independent required body.
-/
theorem constructorDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ConstructorDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorDecl input = .ok declaration next) :
    DeclarativeGrammar.ConstructorDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold constructorDecl at result
  rcases contractEntrySoundness_bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases contractEntrySoundness_bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases contractEntrySoundness_bind_ok_components rest with
    ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
  rcases contractEntrySoundness_bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterModifiersFree := bodyReflects afterModifiers body next
    bodyResult diagnosticFree
  have afterParametersFree :=
    ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
      .constructorKw afterParameters payableMarker afterModifiers
      modifiersResult afterModifiersFree
  exact .parsed marker.span
    (keyword_success_exactTokenParses .constructorKw .contractMember
      markerResult)
    (ContractEntryInternals.entryParameters_success_sound
      afterParametersFree parametersResult)
    (ContractEntryInternals.implicitPublicModifiers_success_sound
      .constructorKw afterModifiersFree modifiersResult)
    (bodySound diagnosticFree bodyResult)

/-- Constructor grammar soundness composes with retained-source validity. -/
theorem constructorDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ConstructorDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : constructorDecl input = .ok declaration next) :
    DeclarativeGrammar.ConstructorDeclParses bodyParses
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      ConstructorDecl.ValidFor statementValid input.file declaration := by
  refine ⟨constructorDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := constructorDecl_validFor statementValid bodyValid input
    inputValid
  rw [result] at valid
  exact valid.1

/--
Every diagnostic-free fallback success uses an empty parameter list and
retains the exact strict modifier and required-body grammar.
-/
theorem fallbackDecl_success_sound
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FallbackDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : fallbackDecl input = .ok declaration next) :
    DeclarativeGrammar.FallbackDeclParses bodyParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold fallbackDecl at result
  rcases contractEntrySoundness_bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases contractEntrySoundness_bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  by_cases empty : parameters.elements.isEmpty
  · simp only [empty, if_true] at rest
    rcases contractEntrySoundness_bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases contractEntrySoundness_bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    have afterModifiersFree := bodyReflects afterModifiers body next
      bodyResult diagnosticFree
    have afterParametersFree :=
      ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw afterParameters payableMarker afterModifiers
        modifiersResult afterModifiersFree
    exact .parsed marker.span
      (keyword_success_exactTokenParses .fallbackKw .contractMember
        markerResult)
      (ContractEntryInternals.entryParameters_success_sound
        afterParametersFree parametersResult)
      (List.nil_of_isEmpty empty)
      (ContractEntryInternals.implicitPublicModifiers_success_sound
        .fallbackKw afterModifiersFree modifiersResult)
      (bodySound diagnosticFree bodyResult)
  · simp only [empty, Bool.false_eq_true, if_false] at rest
    rcases contractEntrySoundness_bind_ok_components rest with
      ⟨validation, afterValidation, validationResult, rest⟩
    rcases contractEntrySoundness_bind_ok_components rest with
      ⟨payableMarker, afterModifiers, modifiersResult, rest⟩
    rcases contractEntrySoundness_bind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    have afterModifiersFree := bodyReflects afterModifiers body next
      bodyResult diagnosticFree
    have afterValidationFree :=
      ContractEntryInternals.implicitPublicModifiers_reflectsDiagnosticFreeOnSuccess
        .fallbackKw afterValidation payableMarker afterModifiers
        modifiersResult afterModifiersFree
    unfold emitDiagnostic modifyState at validationResult
    cases validationResult
    simp [State.emit] at afterValidationFree

/-- Fallback grammar soundness composes with retained-source validity. -/
theorem fallbackDecl_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (bodyValid : (block .require).ValidFor
      (Block.ValidFor statementValid))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : FallbackDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : fallbackDecl input = .ok declaration next) :
    DeclarativeGrammar.FallbackDeclParses bodyParses
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      FallbackDecl.ValidFor statementValid input.file declaration := by
  refine ⟨fallbackDecl_success_sound bodyParses bodyReflects bodySound
    diagnosticFree result, ?_⟩
  have valid := fallbackDecl_validFor statementValid bodyValid input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
