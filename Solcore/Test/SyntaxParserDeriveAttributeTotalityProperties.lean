import Solcore.Syntax.Parser.DeriveAttributeTotalityProperties

/-! External consumers for canonical derive-attribute totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveAttributeTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeriveAttributeInternals.valid_ordinary
example := @DeriveAttributeInternals.valid_ne_invariant
example := @deriveAttribute_ordinary
example := @deriveAttribute_ne_invariant
example := @deriveAttribute_elementTotalityContract

example : ElementTotalityContract deriveAttribute :=
  deriveAttribute_elementTotalityContract

example (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    deriveAttribute input ≠ .invariant error :=
  deriveAttribute_ne_invariant input valid error

end Solcore.Test.SyntaxParserDeriveAttributeTotalityProperties
