import Solcore.Syntax.Parser.EnumElementTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserEnumElementTotalityProperties

open Solcore.Syntax.Parser

example := @EnumInternals.enumConstructorFields_ordinary
example := @EnumInternals.enumConstructorFields_invariantFreeOnValid
example := @EnumInternals.enumConstructor_ordinary
example := @EnumInternals.enumConstructor_invariantFreeOnValid
example := @EnumInternals.enumConstructor_cursor_lt_onSuccess
example := @EnumInternals.enumConstructor_elementTotalityContract

end Solcore.Test.SyntaxParserEnumElementTotalityProperties
