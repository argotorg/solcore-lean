import Solcore.Syntax.Parser.ExportCanonicalTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExportCanonicalTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example : Parser.InvariantFreeOnValid exportDecl :=
  exportDecl_invariantFreeOnValid

example (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    exportDecl input ≠ .invariant error :=
  exportDecl_ne_invariant input inputValid error

end Solcore.Test.SyntaxParserExportCanonicalTotalityProperties
