import Solcore.Syntax.Parser.FilePlainTopItemTotalityProperties

/-! External consumers for conditional plain top-item totality. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFilePlainTopItemTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FileInternals

example := @mapTopItem_invariantFreeOnValid
example := @PlainTopItemTotalityContract
example := @plainTopItem_invariantFreeOnValid
example := @plainTopItem_ne_invariant

example (contract : PlainTopItemTotalityContract)
    (input : State) (valid : input.ValidFor)
    (error : ParserInvariantError) :
    plainTopItem input ≠ .invariant error :=
  plainTopItem_ne_invariant contract input valid error

end Solcore.Test.SyntaxParserFilePlainTopItemTotalityProperties
