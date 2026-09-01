import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @functionDecl_ordinary
example := @functionDecl_invariantFreeOnValid
example := @functionDecl_ne_invariant

end Solcore.Test.SyntaxParserFunctionDeclarationTotalityProperties
