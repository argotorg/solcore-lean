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

example (file : SourceFile) (path : ModulePath)
    (valid : ModulePath.ValidFor file path) :
    path.span.ValidFor file ∧
      (∀ component ∈ path.value.components.toList,
        component.span.ValidFor file) :=
  ⟨valid.1, valid.2.2⟩

example (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor :=
  modulePath_validFor context

end Tests
