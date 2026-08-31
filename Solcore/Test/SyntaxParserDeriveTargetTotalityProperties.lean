import Solcore.Syntax.Parser.DeriveTargetTotalityProperties

/-! External consumers for canonical derive-target totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserDeriveTargetTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.DeriveTargetInternals

example := @deriveComponent_ordinary
example := @deriveComponent_ne_invariant
example := @deriveComponent_ok_cursor_window
example := @deriveTargetTail_ordinary_of_remainingCount_lt
example := @deriveTargetTail_production_ordinary
example := @deriveTargetTail_ne_invariant_of_remainingCount_lt
example := @deriveTarget_ordinary
example := @deriveTarget_ne_invariant
example := @deriveTarget_elementTotalityContract

example : ElementTotalityContract deriveTarget :=
  deriveTarget_elementTotalityContract

example (state : State) (error : ParserInvariantError) :
    deriveTarget state ≠ .invariant error :=
  deriveTarget_ne_invariant state error

end Solcore.Test.SyntaxParserDeriveTargetTotalityProperties
