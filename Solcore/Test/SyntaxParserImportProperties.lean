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
example := selectedImport_validFor
example := selectedImport_preservesTokenWindow
example := selectedImport_preservesTokensOnSuccess
example := selectedImport_cursorMonotoneOnSuccess
example := selectedImport_startsAtCurrentTokenOnSuccess

end Tests
