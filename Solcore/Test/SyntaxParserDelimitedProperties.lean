import Solcore.Syntax.Parser.Delimited

/-! External consumers for delimited parser provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DelimitedList.ValidFor
example := @Parser.PreservesTokensOnSuccess
example := @delimitedWithPolicy_validFor
example := @delimited_validFor
example := @delimitedNoTrailing_validFor
example := @delimitedWithPolicy_preservesTokensOnSuccess
example := @delimited_preservesTokensOnSuccess
example := @delimitedNoTrailing_preservesTokensOnSuccess
example := @delimitedWithPolicy_cursor_lt_onSuccess
example := @delimitedWithPolicy_cursorMonotoneOnSuccess
example := @delimited_cursorMonotoneOnSuccess
example := @delimitedNoTrailing_cursorMonotoneOnSuccess
example := @delimitedWithPolicy_startsAtCurrentTokenOnSuccess
example := @delimited_startsAtCurrentTokenOnSuccess
example := @delimitedNoTrailing_startsAtCurrentTokenOnSuccess

example {α : Type} (file : SourceFile) (values : DelimitedList α)
    (elementValid : SourceFile → α → Prop)
    (valid : DelimitedList.ValidFor elementValid file values)
    (element : α) (member : element ∈ values.elements) :
    values.span.ValidFor file ∧ elementValid file element :=
  ⟨valid.1, valid.2 element member⟩

example (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (identifier context) := by
  intro input value next result
  rcases identifier_ok_state_shape context result with
    ⟨_token, _found, _span, tokensEq, _cursor⟩
  exact tokensEq

end Tests
