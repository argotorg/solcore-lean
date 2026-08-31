import Solcore.Syntax.Parser.Yul.Common

/-! External consumers for common inline-Yul parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @YulNameSequence.ValidFor
example := @yulNames_validFor
example := @yulNames_ok_state_shape
example := @yulNames_preservesTokensOnSuccess
example := @yulNames_cursorMonotoneOnSuccess
example := @yulNames_startsAtCurrentTokenOnSuccess
example := @YulParsedBlock.ValidFor
example := @yulBlock_validFor
example := @yulBlock_ok_state_shape
example := @yulBlock_preservesTokensOnSuccess
example := @yulBlock_cursor_lt_onSuccess
example := @yulBlock_cursorMonotoneOnSuccess
example := @yulBlock_startsAtCurrentTokenOnSuccess
example := @yulParameters_validFor
example := @yulParameters_preservesTokensOnSuccess
example := @yulParameters_cursor_lt_onSuccess
example := @yulParameters_cursorMonotoneOnSuccess
example := @yulParameters_startsAtCurrentTokenOnSuccess

example (file : SourceFile) (values : YulNameSequence)
    (valid : YulNameSequence.ValidFor file values)
    (name : YulIdentifier) (member : name ∈ values.names.toList) :
    values.span.ValidFor file ∧ name.span.ValidFor file :=
  ⟨valid.1, valid.2 name member⟩

end Tests
