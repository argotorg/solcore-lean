import Solcore.Syntax.Parser.TraitBodyTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTraitBodyTotalityProperties

open Solcore.Syntax.Parser

example := @TraitInternals.traitMethod_ordinary
example := @TraitInternals.traitMethod_invariantFreeOnValid
example := @TraitInternals.traitMethod_ne_invariant
example := @TraitInternals.traitMethod_elementTotalityContract
example := @TraitInternals.traitMethods_ordinary_of_remainingCount_lt
example := @TraitInternals.traitMethods_production_ordinary
example := @TraitInternals.traitMethods_production_invariantFreeOnValid
example := @TraitInternals.traitMethods_production_ne_invariant
example := @TraitInternals.traitMethods_ne_invariant_of_remainingCount_lt
example := @TraitInternals.traitBody_ordinary
example := @TraitInternals.traitBody_invariantFreeOnValid
example := @TraitInternals.traitBody_ne_invariant

end Solcore.Test.SyntaxParserTraitBodyTotalityProperties
