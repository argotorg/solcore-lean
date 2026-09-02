import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Reusable full-functionality contract for declarative parser outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/--
A deterministic ordinary outcome whose successful value and rejecting
remainder are also unique. This strengthens `DeterministicOutcomeSpec`, whose
base contract intentionally fixes only successful remainders and branch
exclusion.
-/
structure ExactDeterministicOutcomeSpec {α : Type}
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (rejects : Remainder → Remainder → Prop)
    extends DeterministicOutcomeSpec ordinaryParses rejects where
  successValueUnique : ∀ {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder},
    ordinaryParses input left afterLeft →
    ordinaryParses input right afterRight →
    left = right
  rejectOutputUnique : ∀ {input left right : Remainder},
    rejects input left → rejects input right → left = right

namespace ExactDeterministicOutcomeSpec

/-- Exact outcome functionality fixes the successful value and remainder. -/
theorem successResultUnique {α : Type}
    {ordinaryParses : Remainder → α → Remainder → Prop}
    {rejects : Remainder → Remainder → Prop}
    (spec : ExactDeterministicOutcomeSpec ordinaryParses rejects)
    {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder}
    (leftParsed : ordinaryParses input left afterLeft)
    (rightParsed : ordinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨spec.successValueUnique leftParsed rightParsed,
    spec.successOutputUnique leftParsed rightParsed⟩

end ExactDeterministicOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
