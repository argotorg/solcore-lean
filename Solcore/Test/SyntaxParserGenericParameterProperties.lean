import Solcore.Syntax.Parser.Signature

/-! External consumers for generic-parameter provenance and shape laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @NonemptyList.ValidFor
example := @NonemptyDelimitedList.ValidFor
example := @Option.ValidFor

example : genericParameters.ValidFor
    (NonemptyDelimitedList.ValidFor Located.ValidFor) :=
  genericParameters_validFor

example : Parser.PreservesTokensOnSuccess genericParameters :=
  genericParameters_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess genericParameters :=
  genericParameters_cursorMonotoneOnSuccess

example : optionalGenericParameters.ValidFor
    (Option.ValidFor
      (NonemptyDelimitedList.ValidFor Located.ValidFor)) :=
  optionalGenericParameters_validFor

example : Parser.PreservesTokensOnSuccess optionalGenericParameters :=
  optionalGenericParameters_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess optionalGenericParameters :=
  optionalGenericParameters_cursorMonotoneOnSuccess

example (file : SourceFile) (values : GenericParameters)
    (valid : NonemptyDelimitedList.ValidFor Located.ValidFor file values) :
    values.span.ValidFor file ∧
      values.elements.head.span.ValidFor file := by
  refine ⟨valid.1, valid.2 values.elements.head ?_⟩
  simp [NonemptyList.toList]

end Tests
