import Solcore.Syntax.Parser.FilePlainTopItemTotalityProperties
import Solcore.Syntax.Parser.ImportTotalityProperties

/-! External consumers for complete import-declaration totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImportTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ImportInternals

example := @wildcardImport_ordinary
example := @wildcardImport_ne_invariant
example := @wildcardImport_invariantFreeOnValid
example := @selectiveImport_ordinary
example := @selectiveImport_ne_invariant
example := @selectiveImport_invariantFreeOnValid
example := @importDecl_ordinary
example := @importDecl_ne_invariant
example := @importDecl_invariantFreeOnValid

/-- The result has exactly the type required by plain top-item dispatch. -/
example : Parser.InvariantFreeOnValid importDecl :=
  importDecl_invariantFreeOnValid

/-- The import field can be populated without an adapter theorem. -/
example (rest : FileInternals.PlainTopItemTotalityContract) :
    FileInternals.PlainTopItemTotalityContract := {
  rest with
  importDecl := importDecl_invariantFreeOnValid
}

end Solcore.Test.SyntaxParserImportTotalityProperties
