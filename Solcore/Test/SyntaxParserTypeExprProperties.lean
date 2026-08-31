import Solcore.Syntax.Parser.Type

/-! External consumers for recursive type-expression and tuple contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TypeExpr.ValidFor

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

example {file : SourceFile} {span : SourceSpan} {elements : List TypeExpr}
    (spanValid : span.ValidFor file)
    (elementsValid : ∀ element ∈ elements,
      TypeExpr.ValidFor file element) :
    TypeExpr.ValidFor file { span, value := .tuple elements } :=
  .tuple spanValid elementsValid

end Tests
