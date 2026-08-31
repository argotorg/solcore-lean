import Solcore.Syntax.Parser.TraitProperties

/-! External compile consumers for canonical trait parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TraitInternals.traitMethod_validFor
example := @TraitInternals.TraitBody.ValidFor
example := @TraitInternals.traitMethods_validFor
example := @TraitInternals.traitBody_validFor
example := @TraitInternals.traitBody_startsAtCurrentTokenOnSuccess
example := @TraitInternals.traitMethod_preservesTokenWindow
example := @TraitInternals.traitMethods_preservesTokenWindow
example := @TraitInternals.traitMethods_cursorMonotoneOnSuccess
example := @TraitInternals.traitBody_preservesTokenWindow
example := @TraitInternals.traitBody_cursorMonotoneOnSuccess
example := @traitDecl_preservesTokenWindow
example := @traitDecl_validFor
example := @traitDecl_preservesTokensOnSuccess
example := @traitDecl_cursorMonotoneOnSuccess
example := @traitDecl_startsAtCurrentTokenOnSuccess

end Tests
