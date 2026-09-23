import Solcore.Syntax.Parser.Impl

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplBodyTotalityProperties

open Solcore.Syntax.Parser

example := @ImplInternals.implMethod_ordinary
example := @ImplInternals.implMethod_invariantFreeOnValid
example := @ImplInternals.implMethod_ne_invariant
example := @ImplInternals.implMethod_cursor_lt_onSuccess
example := @ImplInternals.implMethods_ordinary_of_remainingCount_lt
example := @ImplInternals.implMethods_production_ordinary
example := @ImplInternals.implMethods_production_invariantFreeOnValid
example := @ImplInternals.implMethods_production_ne_invariant
example := @ImplInternals.implMethods_ne_invariant_of_remainingCount_lt
example := @ImplInternals.implBody_ordinary
example := @ImplInternals.implBody_invariantFreeOnValid
example := @ImplInternals.implBody_ne_invariant

end Solcore.Test.SyntaxParserImplBodyTotalityProperties
