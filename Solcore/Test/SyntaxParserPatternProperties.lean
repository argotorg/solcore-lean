import Solcore.Syntax.Parser.PatternProperties

/-! External consumers for canonical pattern parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example (expressionValid : SourceFile → Expr → Prop) :
    PatternInternals.wildcardPattern.ValidFor
      (Pattern.ValidFor expressionValid) :=
  PatternInternals.wildcardPattern_validFor expressionValid

example : Parser.PreservesTokenWindow
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_preservesTokenWindow

example : Parser.PreservesTokensOnSuccess
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess
    PatternInternals.wildcardPattern :=
  PatternInternals.wildcardPattern_cursorMonotoneOnSuccess

example : Parser.StartsAtCurrentTokenOnSuccess
    PatternInternals.wildcardPattern (·.span) :=
  PatternInternals.wildcardPattern_startsAtCurrentTokenOnSuccess

end Tests
