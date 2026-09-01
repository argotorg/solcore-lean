import Solcore.Syntax.Parser.TraitDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @traitDecl_ordinary
example := @traitDecl_invariantFreeOnValid
example := @traitDecl_ne_invariant

end Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties
