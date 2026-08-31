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

example := PatternInternals.literalPattern_validFor
example := PatternInternals.literalPattern_preservesTokenWindow
example := PatternInternals.literalPattern_preservesTokensOnSuccess
example := PatternInternals.literalPattern_cursorMonotoneOnSuccess
example := PatternInternals.literalPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.booleanBinderPattern_validFor
example := PatternInternals.booleanBinderPattern_preservesTokenWindow
example := PatternInternals.booleanBinderPattern_preservesTokensOnSuccess
example := PatternInternals.booleanBinderPattern_cursorMonotoneOnSuccess
example := PatternInternals.booleanBinderPattern_startsAtCurrentTokenOnSuccess
example := PatternInternals.patternName_validFor
example := PatternInternals.patternName_preservesTokenWindow
example := PatternInternals.patternName_preservesTokensOnSuccess
example := PatternInternals.patternName_cursorMonotoneOnSuccess
example := PatternInternals.patternName_startsAtCurrentTokenOnSuccess
example := PatternInternals.requirePatternArguments_validFor
example := PatternInternals.constructorArguments_validFor
example := PatternInternals.constructorArguments_preservesTokenWindow
example := PatternInternals.constructorArguments_preservesTokensOnSuccess
example := PatternInternals.constructorArguments_cursorMonotoneOnSuccess
example := PatternInternals.constructorArguments_startsAtCurrentTokenOnSuccess
example := PatternInternals.optionalConstructorArguments_validFor
example := PatternInternals.optionalConstructorArguments_preservesTokenWindow
example :=
  PatternInternals.optionalConstructorArguments_preservesTokensOnSuccess
example := PatternInternals.optionalConstructorArguments_cursorMonotoneOnSuccess
example := PatternInternals.dotConstructorPattern_validFor
example := PatternInternals.dotConstructorPattern_preservesTokenWindow
example := PatternInternals.dotConstructorPattern_preservesTokensOnSuccess
example := PatternInternals.dotConstructorPattern_cursorMonotoneOnSuccess
example := PatternInternals.dotConstructorPattern_startsAtCurrentTokenOnSuccess

end Tests
