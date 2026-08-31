import Solcore.Syntax.Parser.PragmaTotalityProperties

/-! External consumers for pragma-parser totality laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPragmaTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.PragmaInternals

example := @pragmaItemsTail_ordinary_of_remainingCount_lt
example := @pragmaItemsTail_production_ordinary
example := @pragmaItemsTail_production_ne_invariant
example := @pragmaItems_ordinary
example := @pragmaItems_ne_invariant
example := @pragmaDecl_ordinary
example := @pragmaDecl_ne_invariant

example (state : State) (error : ParserInvariantError) :
    pragmaDecl state ≠ .invariant error :=
  pragmaDecl_ne_invariant state error

end Solcore.Test.SyntaxParserPragmaTotalityProperties
