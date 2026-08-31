import Solcore.Syntax.Parser.Type

/-! External consumers for proxy-type parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Parser.StartsAtCurrentTokenOnSuccess
example := @Parser.bind_startsAtCurrentTokenOnSuccess_of_first
example := @Parser.orElse_startsAtCurrentTokenOnSuccess
example := @symbol_startsAtCurrentTokenOnSuccess
example := @TypeExpr.ValidFor.span_valid

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span)) :
    (parseProxyType nested).ValidFor TypeExpr.ValidFor :=
  parseProxyType_validFor nested nestedValid nestedStarts

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseProxyType nested) :=
  parseProxyType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseProxyType nested) :=
  parseProxyType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess (parseProxyType nested) (·.span) :=
  parseProxyType_startsAtCurrentTokenOnSuccess nested

end Tests
