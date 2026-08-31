import Solcore.Syntax.Parser.LiteralProperties

/-! External consumers for canonical literal parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example : coreLiteral.ValidFor Located.ValidFor :=
  coreLiteral_validFor

example : booleanIdentifier.ValidFor Located.ValidFor :=
  booleanIdentifier_validFor

example : Parser.PreservesTokenWindow coreLiteral :=
  coreLiteral_preservesTokenWindow

example : Parser.PreservesTokenWindow booleanIdentifier :=
  booleanIdentifier_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess coreLiteral :=
  coreLiteral_preservesTokensOnSuccess

example : Parser.PreservesTokensOnSuccess booleanIdentifier :=
  booleanIdentifier_preservesTokensOnSuccess

example := @coreLiteral_cursor_lt_onSuccess
example := @booleanIdentifier_cursor_lt_onSuccess

example : Parser.CursorMonotoneOnSuccess coreLiteral :=
  coreLiteral_cursorMonotoneOnSuccess

example : Parser.CursorMonotoneOnSuccess booleanIdentifier :=
  booleanIdentifier_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess coreLiteral (·.span) :=
  coreLiteral_startsAtCurrentTokenOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess booleanIdentifier (·.span) :=
  booleanIdentifier_startsAtCurrentTokenOnSuccess

end Tests
