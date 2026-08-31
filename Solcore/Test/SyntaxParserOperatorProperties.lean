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
