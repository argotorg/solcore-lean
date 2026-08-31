import Solcore.Syntax.Parser.ImportProperties

/-! External consumers for canonical import parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := selectedAlias_validFor
example := selectedAlias_preservesTokenWindow
example := selectedAlias_preservesTokensOnSuccess
example := selectedAlias_cursorMonotoneOnSuccess
example := hidingClause_validFor
example := hidingClause_preservesTokenWindow
example := hidingClause_preservesTokensOnSuccess
example := hidingClause_cursorMonotoneOnSuccess
example := hidingClause_startsAtCurrentTokenOnSuccess
example := optionalHiding_validFor
example := optionalHiding_preservesTokenWindow
example := optionalHiding_preservesTokensOnSuccess
example := optionalHiding_cursorMonotoneOnSuccess
example := @importTerminator_validFor
example := @importTerminator_preservesTokenWindow
example := @importTerminator_preservesTokensOnSuccess
example := @importTerminator_cursorMonotoneOnSuccess
example := @finishImport_preservesTokenWindow
example := @finishImport_preservesTokensOnSuccess
example := @finishImport_cursorMonotoneOnSuccess
example := @finishImport_keepsStartByte
example := @plainImport_preservesTokenWindow
example := @plainImport_cursorMonotoneOnSuccess
example := @namespaceImport_preservesTokenWindow
example := @namespaceImport_cursorMonotoneOnSuccess
example := @wildcardImport_preservesTokenWindow
example := @wildcardImport_cursorMonotoneOnSuccess
example := @plainImport_keepsStartByte
example := @namespaceImport_keepsStartByte
example := @wildcardImport_keepsStartByte
example := @selectiveImport_preservesTokenWindow
example := @selectiveImport_cursorMonotoneOnSuccess
example := importDecl_preservesTokenWindow
example := importDecl_preservesTokensOnSuccess
example := importDecl_cursorMonotoneOnSuccess
example := @selectiveImport_keepsStartByte
example := importDecl_startsAtCurrentTokenOnSuccess
example := selectedImport_validFor
example := selectedImport_preservesTokenWindow
example := selectedImport_preservesTokensOnSuccess
example := selectedImport_cursorMonotoneOnSuccess
example := selectedImport_startsAtCurrentTokenOnSuccess
example := selectedImports_validFor
example := selectedImports_preservesTokenWindow
example := selectedImports_preservesTokensOnSuccess
example := selectedImports_cursorMonotoneOnSuccess
example := selectedImports_startsAtCurrentTokenOnSuccess

end Tests
