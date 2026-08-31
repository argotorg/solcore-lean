import Solcore.Syntax.Parser.Expression.AtomRecoveryTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserExpressionAtomRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals

example := @recoverAtomAux_exists_ok_of_remainingCount_lt
example := @recoverAtomAux_production_exists_ok
example := @recoverAtomAux_ne_invariant_of_remainingCount_lt
example : Parser.Ordinary recoverAtom := recoverAtom_ordinary
example := @recoverAtom_invariantFreeOnValid
example := @recoverAtom_ne_invariant

end Solcore.Test.SyntaxParserExpressionAtomRecoveryTotalityProperties
