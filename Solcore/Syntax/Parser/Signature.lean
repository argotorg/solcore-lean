import Solcore.Syntax.Parser.Parameter
import Solcore.Syntax.Parser.Predicate
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

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

private def functionParameters : Parser (DelimitedList FunctionParameter) :=
  delimited .leftParen .rightParen true namedParameter
    .parameter .topLevel

private def emitModifierOutsideContract (location : FunctionLocation)
    (keywordValue : HardKeyword) (marker : Option SourceSpan) : Parser Unit :=
  match location, marker with
  | .module, some span => emitDiagnostic {
      span
      kind := .constraintViolation (.modifierOutsideContract keywordValue)
    }
  | _, _ => pure ()

private def functionModifiers
    (location : FunctionLocation) : Parser FunctionModifiers := do
  let state ← getState
  let publicMarker ←
    if isKeyword state .publicKw then
      pure (some (← keyword .publicKw .parameter).span)
    else
      pure none
  let state ← getState
  let payableMarker ←
    if isKeyword state .payableKw then
      pure (some (← keyword .payableKw .parameter).span)
    else
      pure none
  let _ ← emitModifierOutsideContract location .publicKw publicMarker
  let _ ← emitModifierOutsideContract location .payableKw payableMarker
  pure { publicMarker, payableMarker }

private def returnClause : Parser (Option ReturnClause) := do
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

end Solcore.Syntax.Parser
