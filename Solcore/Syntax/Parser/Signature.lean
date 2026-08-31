import Solcore.Syntax.Parser.ParameterProperties
import Solcore.Syntax.Parser.Predicate
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.SignatureValidity

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Syntactic location controlling whether contract modifiers are valid. -/
inductive FunctionLocation where
  | module
  | contract
  deriving Repr, BEq, DecidableEq

private def requireGenericParameters
    (values : DelimitedList Identifier) : Parser GenericParameters :=
  match values.elements with
  | head :: tail => pure {
      span := values.span
      elements := { head, tail }
    }
  | [] => fun _ => .invariant (.noProgress .topLevel values.span)

/-- Parse a nonempty generic parameter list `<a, b,>`. -/
def genericParameters : Parser GenericParameters := do
  let values ← delimited .less .greater false (identifier .parameter)
    .parameter .topLevel
  requireGenericParameters values

/-- Parse an optional generic parameter list selected by a leading `<`. -/
def optionalGenericParameters : Parser (Option GenericParameters) := do
  let state ← getState
  if isSymbol state .less then
    pure (some (← genericParameters))
  else
    pure none

private theorem requireGenericParameters_reply_validFor
    (values : DelimitedList Identifier) (input : State)
    (inputValid : input.ValidFor)
    (valuesValid : values.ValidFor Located.ValidFor input.file) :
    (requireGenericParameters values input).ValidFor input
      (NonemptyDelimitedList.ValidFor Located.ValidFor) := by
  unfold requireGenericParameters
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [Reply.ValidFor, NonemptyDelimitedList.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, rfl⟩
      intro element member
      apply valuesValid.2 element
      simpa [NonemptyList.toList, elements] using member

private theorem requireGenericParameters_preservesTokensOnSuccess
    (values : DelimitedList Identifier) :
    Parser.PreservesTokensOnSuccess (requireGenericParameters values) := by
  intro input result next parsed
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil =>
      simp only [elements] at parsed
      contradiction
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      rfl

private theorem requireGenericParameters_preservesTokenWindow
    (values : DelimitedList Identifier) :
    Parser.PreservesTokenWindow (requireGenericParameters values) := by
  intro input
  unfold requireGenericParameters
  cases values.elements <;> trivial

private theorem requireGenericParameters_cursorMonotoneOnSuccess
    (values : DelimitedList Identifier) :
    Parser.CursorMonotoneOnSuccess (requireGenericParameters values) := by
  intro input result next parsed
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil =>
      simp only [elements] at parsed
      contradiction
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- Generic parameter parsing preserves delimiter and identifier provenance. -/
theorem genericParameters_validFor :
    genericParameters.ValidFor
      (NonemptyDelimitedList.ValidFor Located.ValidFor) := by
  unfold genericParameters
  apply Parser.bind_validFor_of_value
    (delimited_validFor Located.ValidFor .less .greater false
      (identifier .parameter) .parameter .topLevel
      (identifier_validFor .parameter)
      (identifier_preservesTokensOnSuccess .parameter))
  intro values input inputValid valuesValid
  exact requireGenericParameters_reply_validFor values input inputValid
    valuesValid

/-- Generic parameter parsing preserves every ordinary token window. -/
theorem genericParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow genericParameters := by
  unfold genericParameters
  apply Parser.bind_preservesTokenWindow
  · exact delimited_preservesTokenWindow .less .greater false
      (identifier .parameter) .parameter .topLevel
      (identifier_preservesTokenWindow .parameter)
  · exact requireGenericParameters_preservesTokenWindow

/-- Generic parameter parsing preserves the immutable lexer token carrier. -/
theorem genericParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess genericParameters := by
  unfold genericParameters
  apply Parser.bind_preservesTokensOnSuccess
  · exact delimited_preservesTokensOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel
      (identifier_preservesTokensOnSuccess .parameter)
  · exact requireGenericParameters_preservesTokensOnSuccess

/-- Generic parameter parsing never moves the parser cursor backwards. -/
theorem genericParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess genericParameters := by
  unfold genericParameters
  apply Parser.bind_cursorMonotoneOnSuccess
  · exact delimited_cursorMonotoneOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel
  · exact requireGenericParameters_cursorMonotoneOnSuccess

/-- A generic parameter list starts at its opening angle bracket. -/
theorem genericParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess genericParameters (·.span) := by
  unfold genericParameters
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel)
  intro values input result next parsed
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil =>
      simp only [elements] at parsed
      contradiction
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      rfl

private theorem someGenericParameters_validFor :
    (do
      let values ← genericParameters
      pure (some values)).ValidFor
        (Option.ValidFor
          (NonemptyDelimitedList.ValidFor Located.ValidFor)) := by
  apply Parser.bind_validFor_of_value genericParameters_validFor
  intro values input inputValid valuesValid
  exact ⟨valuesValid, inputValid, rfl⟩

private theorem someGenericParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess (do
      let values ← genericParameters
      pure (some values)) := by
  apply Parser.bind_preservesTokensOnSuccess
  · exact genericParameters_preservesTokensOnSuccess
  · intro values
    exact Parser.pure_preservesTokensOnSuccess (some values)

private theorem someGenericParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow (do
      let values ← genericParameters
      pure (some values)) := by
  apply Parser.bind_preservesTokenWindow genericParameters_preservesTokenWindow
  intro values
  exact Parser.pure_preservesTokenWindow (some values)

private theorem someGenericParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess (do
      let values ← genericParameters
      pure (some values)) := by
  apply Parser.bind_cursorMonotoneOnSuccess
  · exact genericParameters_cursorMonotoneOnSuccess
  · intro values
    exact Parser.pure_cursorMonotoneOnSuccess (some values)

private theorem getState_bind_apply {α : Type}
    (next : State → Parser α) (input : State) :
    ((getState >>= next) input) = next input input := by
  rfl

/-- Optional generic parameters retain provenance whenever they are present. -/
theorem optionalGenericParameters_validFor :
    optionalGenericParameters.ValidFor
      (Option.ValidFor
        (NonemptyDelimitedList.ValidFor Located.ValidFor)) := by
  intro input inputValid
  unfold optionalGenericParameters
  rw [getState_bind_apply]
  split
  · exact someGenericParameters_validFor input inputValid
  · exact ⟨trivial, inputValid, rfl⟩

/-- Optional generic parameter parsing preserves every token window. -/
theorem optionalGenericParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow optionalGenericParameters := by
  intro input
  unfold optionalGenericParameters
  rw [getState_bind_apply]
  split
  · exact someGenericParameters_preservesTokenWindow input
  · exact ⟨rfl, rfl⟩

/-- Optional generic parameter parsing preserves the lexer token carrier. -/
theorem optionalGenericParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess optionalGenericParameters := by
  intro input values next parsed
  unfold optionalGenericParameters at parsed
  rw [getState_bind_apply] at parsed
  split at parsed
  · exact someGenericParameters_preservesTokensOnSuccess input values next
      parsed
  · cases parsed
    rfl

/-- Optional generic parameter parsing never rewinds the parser cursor. -/
theorem optionalGenericParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess optionalGenericParameters := by
  intro input values next parsed
  unfold optionalGenericParameters at parsed
  rw [getState_bind_apply] at parsed
  split at parsed
  · exact someGenericParameters_cursorMonotoneOnSuccess input values next
      parsed
  · cases parsed
    exact Nat.le_refl _

def functionParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

/-- Function parameter lists retain delimiter and parameter provenance. -/
theorem functionParameters_validFor :
    functionParameters.ValidFor
      (DelimitedList.ValidFor FunctionParameter.ValidFor) := by
  unfold functionParameters
  exact delimited_validFor FunctionParameter.ValidFor .leftParen .rightParen
    true namedParameter .parameter .topLevel namedParameter_validFor
      namedParameter_preservesTokensOnSuccess

/-- Function parameter lists preserve every ordinary token window. -/
theorem functionParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow functionParameters := by
  unfold functionParameters
  exact delimited_preservesTokenWindow .leftParen .rightParen true
    namedParameter .parameter .topLevel namedParameter_preservesTokenWindow

theorem functionParameters_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess functionParameters :=
  functionParameters_preservesTokenWindow.preservesTokensOnSuccess

/-- Function parameter lists never rewind the parser cursor. -/
theorem functionParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess functionParameters := by
  unfold functionParameters
  exact delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel

/-- Function parameter lists start at their opening parenthesis. -/
theorem functionParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess functionParameters (·.span) := by
  unfold functionParameters
  exact delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel

/-- Parse one optional function-modifier marker. -/
def optionalFunctionModifier
    (keywordValue : HardKeyword) : Parser (Option SourceSpan) := do
  let state ← getState
  if isKeyword state keywordValue then
    pure (some (← keyword keywordValue .parameter).span)
  else
    pure none

private def emitModifierOutsideContract (location : FunctionLocation)
    (keywordValue : HardKeyword) (marker : Option SourceSpan) : Parser Unit :=
  match location, marker with
  | .module, some span => emitDiagnostic {
      span
      kind := .constraintViolation (.modifierOutsideContract keywordValue)
    }
  | _, _ => pure ()

private def finishFunctionModifiers (location : FunctionLocation)
    (publicMarker payableMarker : Option SourceSpan) :
    Parser FunctionModifiers := do
  let _ ← emitModifierOutsideContract location .publicKw publicMarker
  let _ ← emitModifierOutsideContract location .payableKw payableMarker
  pure { publicMarker, payableMarker }

/-- Parse optional public/payable markers and enforce their location policy. -/
def functionModifiers
    (location : FunctionLocation) : Parser FunctionModifiers := do
  let publicMarker ← optionalFunctionModifier .publicKw
  let payableMarker ← optionalFunctionModifier .payableKw
  finishFunctionModifiers location publicMarker payableMarker

/-- Parse an optional canonical function return-type clause. -/
def returnClause : Parser (Option ReturnClause) := do
  let state ← getState
  if isContextual state .returns then
    let marker ← contextual .returns .typeExpr
    let types ← delimited .leftParen .rightParen true typeExpr
      .typeExpr .typeExpr
    pure (some {
      span := SourceSpan.cover marker.span types.span
      types
    })
  else
    pure none

private def signatureEnd (parameters : DelimitedList FunctionParameter)
    (modifiers : FunctionModifiers) (returnsClause : Option ReturnClause)
    (whereClause : Option WhereClause) : SourceSpan :=
  match whereClause with
  | some clause => clause.span
  | none => match returnsClause with
    | some clause => clause.span
    | none => match modifiers.payableMarker with
      | some span => span
      | none => match modifiers.publicMarker with
        | some span => span
        | none => parameters.span

/-- Parse a complete named-function signature, excluding its body. -/
def functionSignature
    (location : FunctionLocation) : Parser FunctionSignature := do
  let functionToken ← keyword .functionKw .topItem
  let name ← identifier .topItem
  let genericParameters ← optionalGenericParameters
  let parameters ← functionParameters
  let modifiers ← functionModifiers location
  let returnsClause ← returnClause
  let whereClause ← whereClause
  pure {
    span := SourceSpan.cover functionToken.span
      (signatureEnd parameters modifiers returnsClause whereClause)
    name
    genericParameters
    parameters
    modifiers
    returnsClause
    whereClause
  }

private theorem signatureBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
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

/-- Optional return clauses retain their marker, delimiters, and result types. -/
theorem returnClause_validFor :
    returnClause.ValidFor (Option.ValidFor ReturnClause.ValidFor) := by
  have weak : returnClause.ValidFor (fun _ _ => True) := by
    unfold returnClause
    apply Parser.bind_validFor getState_validFor
    intro observed
    by_cases present : isContextual observed .returns
    · simp only [present, if_true]
      apply Parser.bind_validFor (contextual_validFor .returns .typeExpr)
      intro marker
      apply Parser.bind_validFor
        (delimited_validFor TypeExpr.ValidFor .leftParen .rightParen true
          typeExpr .typeExpr .typeExpr typeExpr_validFor
          typeExpr_preservesTokensOnSuccess)
      intro types
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    · simp only [present]
      exact Parser.pure_validFor none (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : returnClause input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold returnClause getState at stages
      simp only [bind] at stages
      by_cases present : isContextual input .returns
      · simp only [present, if_true] at stages
        rcases signatureBind_ok_components stages with
          ⟨marker, afterMarker, markerResult, rest⟩
        rcases signatureBind_ok_components rest with
          ⟨types, afterTypes, typesResult, finished⟩
        have markerValid := contextual_validFor .returns .typeExpr input
          inputValid
        rw [markerResult] at markerValid
        have typesValid := delimited_validFor TypeExpr.ValidFor .leftParen
          .rightParen true typeExpr .typeExpr .typeExpr typeExpr_validFor
          typeExpr_preservesTokensOnSuccess afterMarker markerValid.2.1
        rw [typesResult] at typesValid
        have markerSpanValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerValid.1
        have typesValidInput :
            DelimitedList.ValidFor TypeExpr.ValidFor input.file types := by
          simpa [markerValid.2.2] using typesValid.1
        have markerShape := acceptToken_ok_state_shape
          (.contextual .returns) .typeExpr (·.isContextual .returns)
          markerResult
        have markerAdvanced : input.advance? = some (marker, afterMarker) := by
          unfold State.advance?
          rw [markerShape.1, markerShape.2]
          rfl
        rcases delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen
            true typeExpr .typeExpr .typeExpr afterMarker types afterTypes
            typesResult with ⟨opening, openingFound, typesStart⟩
        have markerBeforeTypes :=
          inputValid.consumed_end_le_peek_start_after_advance markerAdvanced
            openingFound
        have ordered : marker.span.startByte ≤ types.span.endByte :=
          Nat.le_trans markerSpanValid.2.1
            (Nat.le_trans markerBeforeTypes (by
              rw [typesStart]
              exact typesValidInput.1.2.1))
        have outerValid := SourceSpan.cover_validFor markerSpanValid
          typesValidInput.1 ordered
        cases finished
        exact ⟨by
            simpa only [Option.ValidFor] using
              (show ReturnClause.ValidFor input.file {
                span := SourceSpan.cover marker.span types.span
                types
              } from ⟨outerValid, typesValidInput.1, typesValidInput.2⟩),
          weakResult.2.1, weakResult.2.2⟩
      · simp only [present, Bool.false_eq_true, if_false] at stages
        cases stages
        exact ⟨trivial, inputValid, rfl⟩

private theorem getState_preservesTokenWindowForSignature :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForSignature
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

/-- Optional return clauses preserve every ordinary token window. -/
theorem returnClause_preservesTokenWindow :
    Parser.PreservesTokenWindow returnClause := by
  unfold returnClause
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForSignature
  intro observed
  by_cases present : isContextual observed .returns
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (contextual_preservesTokenWindow .returns .typeExpr)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (delimited_preservesTokenWindow .leftParen .rightParen true typeExpr
        .typeExpr .typeExpr typeExpr_preservesTokenWindow)
    intro types
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem returnClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess returnClause :=
  returnClause_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional return clauses never rewind the parser cursor. -/
theorem returnClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess returnClause := by
  unfold returnClause
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isContextual observed .returns
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (contextual_cursorMonotoneOnSuccess .returns .typeExpr)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true typeExpr
        .typeExpr .typeExpr)
    intro types
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present return clause starts at its current `returns` token. -/
theorem returnClause_some_startsAtCurrentTokenOnSuccess
    {input next : State} {clause : ReturnClause}
    (parsed : returnClause input = .ok (some clause) next) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = clause.span.startByte := by
  unfold returnClause getState at parsed
  simp only [bind] at parsed
  by_cases present : isContextual input .returns
  · simp only [present, if_true] at parsed
    rcases signatureBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases signatureBind_ok_components rest with
      ⟨types, afterTypes, typesResult, finished⟩
    rcases contextual_startsAtCurrentTokenOnSuccess .returns .typeExpr input
        marker afterMarker markerResult with ⟨token, found, start⟩
    cases finished
    exact ⟨token, found, start⟩
  · simp only [present, Bool.false_eq_true, if_false] at parsed
    change Reply.ok none input = .ok (some clause) next at parsed
    simp at parsed

/-- An optional modifier retains a valid marker whenever it is present. -/
theorem optionalFunctionModifier_validFor (keywordValue : HardKeyword) :
    (optionalFunctionModifier keywordValue).ValidFor
      (Option.ValidFor (fun file span => span.ValidFor file)) := by
  unfold optionalFunctionModifier
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isKeyword observed keywordValue
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (keyword_validFor keywordValue .parameter)
    intro marker input inputValid markerValid
    exact ⟨by simpa only [Option.ValidFor, Located.ValidFor] using markerValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional function modifiers preserve every ordinary token window. -/
theorem optionalFunctionModifier_preservesTokenWindow
    (keywordValue : HardKeyword) :
    Parser.PreservesTokenWindow (optionalFunctionModifier keywordValue) := by
  unfold optionalFunctionModifier
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForSignature
  intro observed
  by_cases present : isKeyword observed keywordValue
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow keywordValue .parameter)
    intro marker
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem optionalFunctionModifier_preservesTokensOnSuccess
    (keywordValue : HardKeyword) :
    Parser.PreservesTokensOnSuccess (optionalFunctionModifier keywordValue) :=
  (optionalFunctionModifier_preservesTokenWindow keywordValue
    ).preservesTokensOnSuccess

/-- Optional function modifiers never rewind the parser cursor. -/
theorem optionalFunctionModifier_cursorMonotoneOnSuccess
    (keywordValue : HardKeyword) :
    Parser.CursorMonotoneOnSuccess (optionalFunctionModifier keywordValue) := by
  unfold optionalFunctionModifier
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isKeyword observed keywordValue
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (keyword_cursorMonotoneOnSuccess keywordValue .parameter)
    intro marker
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

private theorem functionModifiers_value_validFor
    {file : SourceFile} (publicMarker payableMarker : Option SourceSpan)
    (publicValid : Option.ValidFor (fun file span => span.ValidFor file)
      file publicMarker)
    (payableValid : Option.ValidFor (fun file span => span.ValidFor file)
      file payableMarker) :
    FunctionModifiers.ValidFor file { publicMarker, payableMarker } := by
  cases publicMarker <;> cases payableMarker <;>
    simp_all [FunctionModifiers.ValidFor, Option.ValidFor]

private theorem finishFunctionModifiers_validForAt
    (location : FunctionLocation)
    (publicMarker payableMarker : Option SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (publicValid : Option.ValidFor (fun file span => span.ValidFor file)
      input.file publicMarker)
    (payableValid : Option.ValidFor (fun file span => span.ValidFor file)
      input.file payableMarker) :
    (finishFunctionModifiers location publicMarker payableMarker input
      ).ValidFor input FunctionModifiers.ValidFor := by
  have modifiersValid := functionModifiers_value_validFor publicMarker
    payableMarker publicValid payableValid
  cases location with
  | contract =>
      unfold finishFunctionModifiers emitModifierOutsideContract
      simp only [bind, Reply.ValidFor]
      exact ⟨modifiersValid, inputValid, rfl⟩
  | module =>
      cases publicMarker with
      | none =>
          cases payableMarker with
          | none =>
              unfold finishFunctionModifiers emitModifierOutsideContract
              simp only [bind, Reply.ValidFor]
              exact ⟨modifiersValid, inputValid, rfl⟩
          | some payableSpan =>
              simp only [Option.ValidFor] at payableValid
              let diagnostic : ParseDiagnostic := {
                span := payableSpan
                kind := .constraintViolation
                  (.modifierOutsideContract .payableKw)
              }
              have emittedValid := inputValid.emit_validFor diagnostic
                payableValid
              unfold finishFunctionModifiers emitModifierOutsideContract
                emitDiagnostic modifyState
              simp only [bind, Reply.ValidFor]
              exact ⟨modifiersValid, emittedValid, rfl⟩
      | some publicSpan =>
          simp only [Option.ValidFor] at publicValid
          cases payableMarker with
          | none =>
              let diagnostic : ParseDiagnostic := {
                span := publicSpan
                kind := .constraintViolation
                  (.modifierOutsideContract .publicKw)
              }
              have emittedValid := inputValid.emit_validFor diagnostic
                publicValid
              unfold finishFunctionModifiers emitModifierOutsideContract
                emitDiagnostic modifyState
              simp only [bind, Reply.ValidFor]
              exact ⟨modifiersValid, emittedValid, rfl⟩
          | some payableSpan =>
              simp only [Option.ValidFor] at payableValid
              let publicDiagnostic : ParseDiagnostic := {
                span := publicSpan
                kind := .constraintViolation
                  (.modifierOutsideContract .publicKw)
              }
              let payableDiagnostic : ParseDiagnostic := {
                span := payableSpan
                kind := .constraintViolation
                  (.modifierOutsideContract .payableKw)
              }
              have afterPublic := inputValid.emit_validFor publicDiagnostic
                publicValid
              have afterPayable := afterPublic.emit_validFor payableDiagnostic
                payableValid
              unfold finishFunctionModifiers emitModifierOutsideContract
                emitDiagnostic modifyState
              simp only [bind, Reply.ValidFor]
              exact ⟨modifiersValid, afterPayable, rfl⟩

/-- Function modifiers retain every written marker and valid diagnostic. -/
theorem functionModifiers_validFor (location : FunctionLocation) :
    (functionModifiers location).ValidFor FunctionModifiers.ValidFor := by
  intro input inputValid
  unfold functionModifiers
  cases publicResult : optionalFunctionModifier .publicKw input with
  | invariant error => simp only [bind, publicResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := optionalFunctionModifier_validFor .publicKw input inputValid
      rw [publicResult] at valid
      simpa only [bind, publicResult, Reply.ValidFor] using valid
  | ok publicMarker afterPublic =>
      have publicContract := optionalFunctionModifier_validFor .publicKw input
        inputValid
      rw [publicResult] at publicContract
      simp only [bind, publicResult]
      cases payableResult : optionalFunctionModifier .payableKw afterPublic with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := optionalFunctionModifier_validFor .payableKw
            afterPublic publicContract.2.1
          rw [payableResult] at valid
          have transported := valid.of_file_eq publicContract.2.2
          change failure.span.ValidFor input.file ∧
            rejected.ValidFor ∧ rejected.file = input.file
          exact transported
      | ok payableMarker afterPayable =>
          have payableContract := optionalFunctionModifier_validFor .payableKw
            afterPublic publicContract.2.1
          rw [payableResult] at payableContract
          have publicValid : Option.ValidFor
              (fun file span => span.ValidFor file) afterPayable.file
              publicMarker := by
            simpa [payableContract.2.2, publicContract.2.2] using
              publicContract.1
          have payableValid : Option.ValidFor
              (fun file span => span.ValidFor file) afterPayable.file
              payableMarker := by
            simpa [payableContract.2.2] using payableContract.1
          exact (finishFunctionModifiers_validForAt location publicMarker
            payableMarker afterPayable payableContract.2.1 publicValid
            payableValid).of_file_eq
              (payableContract.2.2.trans publicContract.2.2)

private theorem emitModifierOutsideContract_preservesTokenWindow
    (location : FunctionLocation) (keywordValue : HardKeyword)
    (marker : Option SourceSpan) : Parser.PreservesTokenWindow
      (emitModifierOutsideContract location keywordValue marker) := by
  unfold emitModifierOutsideContract
  cases location <;> cases marker <;>
    first | exact Parser.pure_preservesTokenWindow ()
          | exact emitDiagnostic_preservesTokenWindowForSignature _

private theorem finishFunctionModifiers_preservesTokenWindow
    (location : FunctionLocation) (publicMarker payableMarker : Option SourceSpan) :
    Parser.PreservesTokenWindow
      (finishFunctionModifiers location publicMarker payableMarker) := by
  unfold finishFunctionModifiers
  apply Parser.bind_preservesTokenWindow
    (emitModifierOutsideContract_preservesTokenWindow location .publicKw publicMarker)
  intro _
  apply Parser.bind_preservesTokenWindow
    (emitModifierOutsideContract_preservesTokenWindow location .payableKw payableMarker)
  intro _
  exact Parser.pure_preservesTokenWindow _

/-- Function modifiers preserve every ordinary token window. -/
theorem functionModifiers_preservesTokenWindow (location : FunctionLocation) :
    Parser.PreservesTokenWindow (functionModifiers location) := by
  unfold functionModifiers
  apply Parser.bind_preservesTokenWindow
    (optionalFunctionModifier_preservesTokenWindow .publicKw)
  intro publicMarker
  apply Parser.bind_preservesTokenWindow
    (optionalFunctionModifier_preservesTokenWindow .payableKw)
  exact finishFunctionModifiers_preservesTokenWindow location publicMarker

theorem functionModifiers_preservesTokensOnSuccess (location : FunctionLocation) :
    Parser.PreservesTokensOnSuccess (functionModifiers location) :=
  (functionModifiers_preservesTokenWindow location).preservesTokensOnSuccess

private theorem emitModifierOutsideContract_cursorMonotoneOnSuccess
    (location : FunctionLocation) (keywordValue : HardKeyword)
    (marker : Option SourceSpan) : Parser.CursorMonotoneOnSuccess
      (emitModifierOutsideContract location keywordValue marker) := by
  unfold emitModifierOutsideContract
  cases location <;> cases marker <;>
    first | exact Parser.pure_cursorMonotoneOnSuccess ()
          | exact emitDiagnostic_cursorMonotoneOnSuccess _

/-- Function modifiers never rewind the parser cursor. -/
theorem functionModifiers_cursorMonotoneOnSuccess (location : FunctionLocation) :
    Parser.CursorMonotoneOnSuccess (functionModifiers location) := by
  unfold functionModifiers finishFunctionModifiers
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalFunctionModifier_cursorMonotoneOnSuccess .publicKw)
  intro publicMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalFunctionModifier_cursorMonotoneOnSuccess .payableKw)
  intro payableMarker
  apply Parser.bind_cursorMonotoneOnSuccess
    (emitModifierOutsideContract_cursorMonotoneOnSuccess location .publicKw publicMarker)
  intro _
  apply Parser.bind_cursorMonotoneOnSuccess
    (emitModifierOutsideContract_cursorMonotoneOnSuccess location .payableKw payableMarker)
  intro _
  exact Parser.pure_cursorMonotoneOnSuccess _

end Solcore.Syntax.Parser
