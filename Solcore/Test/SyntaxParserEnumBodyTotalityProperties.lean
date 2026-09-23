import Solcore.Syntax.Parser.Enum

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumBodyTotalityProperties

open Solcore.Syntax.Parser

example := @EnumInternals.enumConstructors_ordinary
example := @EnumInternals.enumConstructors_ne_invariant
example := @EnumInternals.enumBody_ordinary
example := @EnumInternals.enumBody_invariantFreeOnValid
example := @EnumInternals.enumBody_ne_invariant

end Solcore.Test.SyntaxParserEnumBodyTotalityProperties
