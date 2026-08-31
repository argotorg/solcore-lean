import Solcore.Syntax.ModuleValidity

/-! External consumers for canonical module declaration validity. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

example := @ModulePath.ValidFor
example := @SelectorName.ValidFor
example := @SelectedImport.ValidFor
example := @HidingClause.ValidFor
example := @ImportDecl.ValidFor
example := @ConstructorSelection.ValidFor
example := @ExportName.ValidFor
example := @LocalExportItem.ValidFor
example := @ExportSelection.ValidFor
example := @ExportDecl.ValidFor
example := @PragmaDecl.ValidFor

example (file : SourceFile) (declaration : ImportDecl)
    (valid : ImportDecl.ValidFor file declaration) :
    declaration.span.ValidFor file :=
  valid.1

example (file : SourceFile) (declaration : ExportDecl)
    (valid : ExportDecl.ValidFor file declaration) :
    declaration.span.ValidFor file :=
  valid.1

end Tests
