import Solcore.Syntax.Parser.EnumDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @enumDecl_ordinary
example := @enumDecl_invariantFreeOnValid
example := @enumDecl_ne_invariant

end Solcore.Test.SyntaxParserEnumDeclarationTotalityProperties
