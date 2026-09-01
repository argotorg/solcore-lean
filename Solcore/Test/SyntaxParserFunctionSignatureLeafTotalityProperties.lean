import Solcore.Syntax.Parser.FunctionSignatureLeafTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureLeafTotalityProperties

open Solcore.Syntax.Parser

example := @functionParameters_invariantFreeOnValid
example := @optionalFunctionModifier_invariantFreeOnValid
example := @functionModifiers_invariantFreeOnValid
example := @returnClause_invariantFreeOnValid

end Solcore.Test.SyntaxParserFunctionSignatureLeafTotalityProperties
