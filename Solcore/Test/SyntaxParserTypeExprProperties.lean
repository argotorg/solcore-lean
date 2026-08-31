import Solcore.Syntax.Parser.Type

/-! External consumers for recursive type-expression and tuple contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TypeExpr.ValidFor

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseMappingType nested).ValidFor TypeExpr.ValidFor :=
  parseMappingType_validFor nested nestedValid nestedStarts
    nestedPreserves nestedMonotone

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseMappingType nested) :=
  parseMappingType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseMappingType nested) :=
  parseMappingType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseMappingType nested) (·.span) :=
  parseMappingType_startsAtCurrentTokenOnSuccess nested

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseComptimeType nested).ValidFor TypeExpr.ValidFor :=
  parseComptimeType_validFor nested nestedValid nestedStarts
    nestedPreserves nestedMonotone

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseComptimeType nested) :=
  parseComptimeType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseComptimeType nested) :=
  parseComptimeType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseComptimeType nested) (·.span) :=
  parseComptimeType_startsAtCurrentTokenOnSuccess nested

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseTupleType nested).ValidFor TypeExpr.ValidFor :=
  parseTupleType_validFor nested nestedValid nestedPreserves

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseTupleType nested) :=
  parseTupleType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseTupleType nested) :=
  parseTupleType_cursorMonotoneOnSuccess nested

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseTupleType nested) (·.span) :=
  parseTupleType_startsAtCurrentTokenOnSuccess nested

example {file : SourceFile} {span : SourceSpan} {elements : List TypeExpr}
    (spanValid : span.ValidFor file)
    (elementsValid : ∀ element ∈ elements,
      TypeExpr.ValidFor file element) :
    TypeExpr.ValidFor file { span, value := .tuple elements } :=
  .tuple spanValid elementsValid

end Tests
