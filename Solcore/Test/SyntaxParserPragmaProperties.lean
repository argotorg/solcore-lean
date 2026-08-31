import Solcore.Syntax.Parser.Pragma

/-! External consumers for provisional pragma provenance contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @PragmaDecl.ValidFor
example := @pragmaDecl_validFor
example := @pragmaDecl_preservesTokensOnSuccess
example := @pragmaDecl_startsAtCurrentTokenOnSuccess
example := @pragmaDecl_cursor_lt_onSuccess
example := @pragmaDecl_cursorMonotoneOnSuccess

example :
    pragmaDecl.ValidFor PragmaDecl.ValidFor ∧
      Parser.PreservesTokensOnSuccess pragmaDecl ∧
      Parser.CursorMonotoneOnSuccess pragmaDecl ∧
      Parser.StartsAtCurrentTokenOnSuccess pragmaDecl (·.span) :=
  ⟨pragmaDecl_validFor, pragmaDecl_preservesTokensOnSuccess,
    pragmaDecl_cursorMonotoneOnSuccess,
    pragmaDecl_startsAtCurrentTokenOnSuccess⟩

example (file : SourceFile) (declaration : PragmaDecl)
    (valid : PragmaDecl.ValidFor file declaration) :
    declaration.span.ValidFor file ∧
      declaration.value.name.span.ValidFor file :=
  ⟨valid.1, valid.2.1⟩

example (file : SourceFile) (declaration : PragmaDecl)
    (valid : PragmaDecl.ValidFor file declaration)
    (item : Identifier) (member : item ∈ declaration.value.items) :
    item.span.ValidFor file :=
  valid.2.2 item member

end Tests
