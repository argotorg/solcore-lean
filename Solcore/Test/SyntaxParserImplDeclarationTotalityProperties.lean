import Solcore.Syntax.Parser.ImplDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.implDeclAfterDefault_ordinary
example := @ImplInternals.implDeclAfterDefault_invariantFreeOnValid
example := @ImplInternals.implDeclAfterDefault_ne_invariant
example := @implDecl_ordinary
example := @implDecl_invariantFreeOnValid
example := @implDecl_ne_invariant

end Solcore.Test.SyntaxParserImplDeclarationTotalityProperties
