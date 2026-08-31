import Solcore.Syntax.Parser.InvariantFreeProperties

/-! External consumers for compositional invariant-freedom laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserInvariantFreeProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Parser.InvariantFreeOnValid
example := @Parser.InvariantFreeOnValid.ne_invariant
example := @Parser.invariantFreeOnValid_of_ne_invariant
example := @Parser.invariantFreeOnValid_iff_ne_invariant
example := @Parser.Ordinary.invariantFreeOnValid
example := @Parser.pure_invariantFreeOnValid
example := @Parser.bind_invariantFreeOnValid
example := @Parser.orElse_invariantFreeOnValid
example := @Parser.getState_invariantFreeOnValid
example := @Parser.modifyState_invariantFreeOnValid
example := @Parser.emitDiagnostic_invariantFreeOnValid
example := @Parser.rejectAt_invariantFreeOnValid

example {alpha : Type} {parser : Parser alpha}
    (ordinary : Parser.Ordinary parser) :
    Parser.InvariantFreeOnValid parser :=
  ordinary.invariantFreeOnValid

example {alpha : Type} {parser : Parser alpha}
    (free : Parser.InvariantFreeOnValid parser)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  free.ne_invariant input valid error

end Solcore.Test.SyntaxParserInvariantFreeProperties
