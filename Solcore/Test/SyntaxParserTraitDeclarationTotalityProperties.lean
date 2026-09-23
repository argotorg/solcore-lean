import Solcore.Syntax.Parser.Trait

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @traitDecl_ordinary
example := @traitDecl_invariantFreeOnValid
example := @traitDecl_ne_invariant

end Solcore.Test.SyntaxParserTraitDeclarationTotalityProperties
