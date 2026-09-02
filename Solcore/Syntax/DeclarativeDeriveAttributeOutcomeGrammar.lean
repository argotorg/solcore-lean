import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveAttributeValidOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for the public derive-attribute
parser's prioritized transactional choice.

The recovered path always starts again at the original input.  The rejected
remainder from the normal path is retained only as evidence that fallback was
selected.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary public success from the preferred normal path, or from recovery
selected by an exact normal-path rejection and retried at the original input. -/
inductive DeriveAttributeOrdinaryParses :
    Remainder → Syntax.DeriveAttribute → Remainder → Prop where
  | normal {input output : Remainder} {value : Syntax.DeriveAttribute}
      (parsed : DeriveAttributeParses input value output) :
      DeriveAttributeOrdinaryParses input value output
  | recovered {input validRejected output : Remainder}
      {value : Syntax.DeriveAttribute}
      (validRejection : DeriveAttributeValidRejects input validRejected)
      (parsed : DeriveAttributeRecoveredParses input value output) :
      DeriveAttributeOrdinaryParses input value output

/-- Exact public rejection when the normal path rejects and recovery, retried
at the original input, also rejects.  The public endpoint is recovery's
rejected remainder; the normal rejected remainder remains explicit evidence. -/
inductive DeriveAttributeRejects : Remainder → Remainder → Prop where
  | both {input validRejected recoveredRejected : Remainder}
      (validRejection : DeriveAttributeValidRejects input validRejected)
      (recoveredRejection : DeriveAttributeRecoveredRejects input
        recoveredRejected) :
      DeriveAttributeRejects input recoveredRejected

end Solcore.Syntax.DeclarativeGrammar
