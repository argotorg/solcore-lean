import Solcore.Syntax.Parser.Name

/-! External compile consumers for canonical name provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @acceptToken_ok_state_shape
example := @symbol_ok_state_shape
example := @identifier_ok_state_shape

example (file : SourceFile) (name : QualifiedName)
    (valid : QualifiedName.ValidFor file name) :
    name.span.ValidFor file :=
  valid.1

example (file : SourceFile) (name : QualifiedName)
    (valid : QualifiedName.ValidFor file name)
    (component : Identifier)
    (member : component ∈ name.value.components.toList) :
    component.span.ValidFor file :=
  valid.2 component member

example (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor :=
  qualifiedName_validFor context phase

example := @qualifiedName_ok_state_shape
example := @qualifiedName_preservesTokensOnSuccess
example := @qualifiedName_preservesTokenWindow
example := @qualifiedName_startsAtCurrentTokenOnSuccess
example := @qualifiedName_cursor_lt_onSuccess
example := @qualifiedName_cursorMonotoneOnSuccess

example (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor ∧
      Parser.PreservesTokensOnSuccess (qualifiedName context phase) ∧
      Parser.CursorMonotoneOnSuccess (qualifiedName context phase) ∧
      Parser.StartsAtCurrentTokenOnSuccess
        (qualifiedName context phase) (·.span) :=
  ⟨qualifiedName_validFor context phase,
    qualifiedName_preservesTokensOnSuccess context phase,
    qualifiedName_cursorMonotoneOnSuccess context phase,
    qualifiedName_startsAtCurrentTokenOnSuccess context phase⟩

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedName.ValidFor input.file name ∧ next.ValidFor ∧
      next.file = input.file ∧ input.cursor < next.cursor ∧
      next.tokens = input.tokens ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = name.span.startByte := by
  have valid := qualifiedName_validFor context phase input inputValid
  rw [result] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2,
    qualifiedName_cursor_lt_onSuccess context phase result,
    qualifiedName_preservesTokensOnSuccess context phase
      input name next result,
    qualifiedName_startsAtCurrentTokenOnSuccess context phase
      input name next result⟩

end Tests
