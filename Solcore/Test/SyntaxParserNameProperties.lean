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
example := @qualifiedName_cursor_lt_onSuccess
example := @qualifiedName_cursorMonotoneOnSuccess

end Tests
