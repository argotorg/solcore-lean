import Solcore.Syntax.Parser.GenericParametersTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserGenericParametersTotalityProperties

open Solcore.Syntax.Parser

example := @genericParameters_ordinary
example := @genericParameters_invariantFreeOnValid
example := @genericParameters_ne_invariant
example := @optionalGenericParameters_ordinary
example := @optionalGenericParameters_invariantFreeOnValid
example := @optionalGenericParameters_ne_invariant

end Solcore.Test.SyntaxParserGenericParametersTotalityProperties
