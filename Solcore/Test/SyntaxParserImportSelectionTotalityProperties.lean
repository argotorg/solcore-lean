import Solcore.Syntax.Parser.ImportSelectionTotalityProperties

/-! External consumers for selected-import totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportSelectionTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ImportInternals

example := @selectedAlias_ordinary
example := @selectedAlias_ne_invariant
example := @selectedImport_ordinary
example := @selectedImport_ne_invariant
example := @selectedImport_cursor_lt_onSuccess
example := @selectedImport_elementTotalityContract
example := @requireSelected_ordinary_of_delimited_success
example := @requireSelected_ne_invariant_of_delimited_success
example := @requireSelectorNames_ordinary_of_delimited_success
example := @requireSelectorNames_ne_invariant_of_delimited_success
example := @selectedImports_ordinary
example := @selectedImports_invariantFreeOnValid
example := @selectedImports_ne_invariant
example := @hidingClause_ordinary
example := @hidingClause_invariantFreeOnValid
example := @hidingClause_ne_invariant
example := @optionalHiding_ordinary
example := @optionalHiding_invariantFreeOnValid
example := @optionalHiding_ne_invariant

example : ElementTotalityContract selectedImport :=
  selectedImport_elementTotalityContract

end Solcore.Test.SyntaxParserImportSelectionTotalityProperties
