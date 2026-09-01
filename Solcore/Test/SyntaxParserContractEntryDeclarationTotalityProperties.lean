import Solcore.Syntax.Parser.ContractEntryDeclarationTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractEntryDeclarationTotalityProperties

open Solcore.Syntax.Parser

example := @constructorDecl_ordinary
example := @constructorDecl_invariantFreeOnValid
example := @constructorDecl_ne_invariant
example := @fallbackDecl_ordinary
example := @fallbackDecl_invariantFreeOnValid
example := @fallbackDecl_ne_invariant

end Solcore.Test.SyntaxParserContractEntryDeclarationTotalityProperties
