import Solcore.Syntax.Parser.Operator
import Solcore.Syntax.Parser.Delimited

/-! External consumers for selector-name provenance and shape contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @SelectorName.ValidFor
example := @operatorSelector_validFor
example := @selectorName_validFor
example := @operatorSelector_preservesTokensOnSuccess
example := @selectorName_preservesTokensOnSuccess
example := @operatorSelector_startsAtCurrentTokenOnSuccess
example := @selectorName_startsAtCurrentTokenOnSuccess
example := @operatorSelector_cursor_lt_onSuccess
example := @operatorSelector_cursorMonotoneOnSuccess
example := @selectorName_cursor_lt_onSuccess
example := @selectorName_cursorMonotoneOnSuccess

example (context : ParseContext) :
    (operatorSelector context).ValidFor SelectorName.ValidFor ∧
      Parser.PreservesTokensOnSuccess (operatorSelector context) ∧
      Parser.CursorMonotoneOnSuccess (operatorSelector context) ∧
      Parser.StartsAtCurrentTokenOnSuccess
        (operatorSelector context) (·.span) :=
  ⟨operatorSelector_validFor context,
    operatorSelector_preservesTokensOnSuccess context,
    operatorSelector_cursorMonotoneOnSuccess context,
    operatorSelector_startsAtCurrentTokenOnSuccess context⟩

example (context : ParseContext) :
    (selectorName context).ValidFor SelectorName.ValidFor ∧
      Parser.PreservesTokensOnSuccess (selectorName context) ∧
      Parser.CursorMonotoneOnSuccess (selectorName context) ∧
      Parser.StartsAtCurrentTokenOnSuccess (selectorName context) (·.span) :=
  ⟨selectorName_validFor context,
    selectorName_preservesTokensOnSuccess context,
    selectorName_cursorMonotoneOnSuccess context,
    selectorName_startsAtCurrentTokenOnSuccess context⟩

example (file : SourceFile) (span : SourceSpan) (name : Identifier)
    (valid : SelectorName.ValidFor file {
      span
      value := .identifier name
    }) :
    span.ValidFor file ∧ name.span.ValidFor file :=
  valid

example (context : ParseContext) :
    (delimited .leftBrace .rightBrace true (selectorName context)
      context .topLevel).ValidFor
        (DelimitedList.ValidFor SelectorName.ValidFor) :=
  delimited_validFor SelectorName.ValidFor .leftBrace .rightBrace true
    (selectorName context) context .topLevel
    (selectorName_validFor context)
    (selectorName_preservesTokensOnSuccess context)

end Tests
