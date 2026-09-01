import Solcore.Syntax.Parser.FunctionSignatureTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureTotalityProperties

open Solcore.Syntax.Parser

example := @functionSignature_ordinary
example := @functionSignature_invariantFreeOnValid
example := @functionSignature_ne_invariant
example := @functionSignature_elementTotalityContract

end Solcore.Test.SyntaxParserFunctionSignatureTotalityProperties
