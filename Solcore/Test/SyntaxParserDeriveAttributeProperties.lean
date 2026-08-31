import Solcore.Syntax.Parser.DeriveCarrierProperties

/-! External compile consumers for canonical derive-attribute contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeriveAttribute.ValidFor

example (file : SourceFile) (value : DeriveAttribute)
    (valid : DeriveAttribute.ValidFor file value) :
    value.span.ValidFor file ∧
      value.value.targets.ValidFor QualifiedName.ValidFor file :=
  valid

example : deriveAttribute.ValidFor DeriveAttribute.ValidFor :=
  deriveAttribute_validFor

example : Parser.PreservesTokensOnSuccess deriveAttribute :=
  deriveAttribute_preservesTokensOnSuccess

example {input next : State} {value : DeriveAttribute}
    (parsed : deriveAttribute input = .ok value next) :
    input.cursor < next.cursor :=
  deriveAttribute_cursor_lt_onSuccess parsed

example : Parser.CursorMonotoneOnSuccess deriveAttribute :=
  deriveAttribute_cursorMonotoneOnSuccess

end Tests
