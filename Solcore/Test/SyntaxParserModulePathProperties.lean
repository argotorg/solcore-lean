import Solcore.Syntax.Parser.ModulePath

/-! External consumers for module-path provenance and shape contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @qualifiedName_ok_state_shape
example := @qualifiedName_preservesTokensOnSuccess
example := @ModulePath.ValidFor
example := @modulePath_validFor
example := @modulePath_preservesTokensOnSuccess
example := @modulePath_startsAtCurrentTokenOnSuccess
example := @modulePath_cursor_lt_onSuccess
example := @modulePath_cursorMonotoneOnSuccess

example (file : SourceFile) (path : ModulePath)
    (valid : ModulePath.ValidFor file path) :
    path.span.ValidFor file ∧
      (∀ component ∈ path.value.components.toList,
        component.span.ValidFor file) :=
  ⟨valid.1, valid.2.2⟩

example (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor :=
  modulePath_validFor context

example (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor ∧
      Parser.PreservesTokensOnSuccess (modulePath context) ∧
      Parser.CursorMonotoneOnSuccess (modulePath context) ∧
      Parser.StartsAtCurrentTokenOnSuccess (modulePath context) (·.span) :=
  ⟨modulePath_validFor context,
    modulePath_preservesTokensOnSuccess context,
    modulePath_cursorMonotoneOnSuccess context,
    modulePath_startsAtCurrentTokenOnSuccess context⟩

example (context : ParseContext) {input next : State} {path : ModulePath}
    (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    ModulePath.ValidFor input.file path ∧ next.ValidFor ∧
      next.file = input.file ∧ input.cursor < next.cursor ∧
      next.tokens = input.tokens ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = path.span.startByte := by
  have valid := modulePath_validFor context input inputValid
  rw [result] at valid
  exact ⟨valid.1, valid.2.1, valid.2.2,
    modulePath_cursor_lt_onSuccess context result,
    modulePath_preservesTokensOnSuccess context input path next result,
    modulePath_startsAtCurrentTokenOnSuccess context input path next result⟩

end Tests
