import Solcore.Syntax.Parser.TypeAlias

/-! External consumers for type-alias recovery totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeAliasRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.TypeAliasInternals

example := @recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt
example := @recoverTypeAliasValueAux_production_exists_ok
example := @recoverTypeAliasValueAux_ordinary_of_remainingCount_lt
example := @recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt
example := @recoverTypeAliasValueAux_production_ordinary
example := @recoverTypeAliasValueAux_production_ne_invariant
example := @recoverTypeAliasValue_ordinary
example := @recoverTypeAliasValue_ne_invariant

example (state : State) (error : ParserInvariantError) :
    recoverTypeAliasValue state ≠ .invariant error :=
  recoverTypeAliasValue_ne_invariant state error

example : Parser.PreservesTokenWindow recoverTypeAliasValue :=
  recoverTypeAliasValue_preservesTokenWindow

end Solcore.Test.SyntaxParserTypeAliasRecoveryTotalityProperties
