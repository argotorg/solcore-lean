import Solcore.Syntax.Parser.Derive

/-! External compile consumers for canonical derive-target contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example : deriveTarget.ValidFor QualifiedName.ValidFor :=
  deriveTarget_validFor

example : Parser.PreservesTokenWindow deriveTarget :=
  deriveTarget_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess deriveTarget :=
  deriveTarget_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess deriveTarget :=
  deriveTarget_cursorMonotoneOnSuccess

example {input next : State} {target : DeriveTarget}
    (parsed : deriveTarget input = .ok target next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = target.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor :=
  deriveTarget_ok_state_shape parsed

end Tests
