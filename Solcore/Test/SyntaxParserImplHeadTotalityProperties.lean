import Solcore.Syntax.Parser.ImplHeadTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplHeadTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.requireImplArguments_ok_of_delimited_false_ok
example := @ImplInternals.implDefaultMarker_invariantFreeOnValid
example := @ImplInternals.implDefaultMarker_ne_invariant

end Solcore.Test.SyntaxParserImplHeadTotalityProperties
