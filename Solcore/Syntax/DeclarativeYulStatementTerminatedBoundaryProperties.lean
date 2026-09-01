import Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryProperties
import Solcore.Syntax.DeclarativeYulStatementTerminatedOutcomeProperties

/-! Lift Yul recovery-boundary exclusion through optional termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery boundary that excludes core success also excludes every
optionally terminated success, since termination begins with that same core
success. -/
theorem YulStatementRejects.disjointTerminatedOrdinary
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    (coreBoundaryDisjoint : ∀ {input rejected},
      YulStatementRejects input rejected →
        ¬ ∃ statement output, coreOrdinary input statement output)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementTerminatedOrdinaryParses coreOrdinary input statement
        output := by
  rintro ⟨statement, output, afterCore, coreParsed, semicolonParsed⟩
  exact coreBoundaryDisjoint rejection ⟨statement, afterCore, coreParsed⟩

end Solcore.Syntax.DeclarativeGrammar
