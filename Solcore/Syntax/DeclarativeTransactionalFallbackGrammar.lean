import Solcore.Syntax.DeclarativeGrammar

/-!
Implementation-independent outcomes for prioritized transactional fallback.

The preferred branch runs first.  Only its exact rejection permits the
fallback branch to run from the original remainder.  When both branches
reject, the wrapper also rejects at that original remainder.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of a preferred branch or of a fallback selected by an
exact preferred-branch rejection. -/
inductive TransactionalFallbackOrdinaryParses {alpha : Type}
    (primaryParses : Remainder → alpha → Remainder → Prop)
    (primaryRejects : Remainder → Remainder → Prop)
    (fallbackParses : Remainder → alpha → Remainder → Prop) :
    Remainder → alpha → Remainder → Prop where
  | primary {input output : Remainder} {value : alpha}
      (parsed : primaryParses input value output) :
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output
  | fallback {input primaryRejected output : Remainder} {value : alpha}
      (primaryRejection : primaryRejects input primaryRejected)
      (parsed : fallbackParses input value output) :
      TransactionalFallbackOrdinaryParses primaryParses primaryRejects
        fallbackParses input value output

/-- Exact rejection when both transactional alternatives reject.  Intermediate
rejected remainders are retained as evidence, while the wrapper rejects at its
original input remainder. -/
inductive TransactionalFallbackRejects
    (primaryRejects fallbackRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | both {input primaryRejected fallbackRejected : Remainder}
      (primaryRejection : primaryRejects input primaryRejected)
      (fallbackRejection : fallbackRejects input fallbackRejected) :
      TransactionalFallbackRejects primaryRejects fallbackRejects input input

end Solcore.Syntax.DeclarativeGrammar
