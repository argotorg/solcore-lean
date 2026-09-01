import Solcore.Syntax.DeclarativeCoreBlockIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTermPublicOutcomeProperties

/-! Public ordinary outcomes for isolated Core blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary isolated-block success over the public raw-block outcomes. -/
abbrev IsolatedCoreBlockPublicOrdinaryParses
    (policy : CoreBlockTailPolicy) :=
  IsolatedCoreBlockOrdinaryParses
    (CoreBlockPublicOrdinaryParses policy)
    (CoreBlockPublicRejects policy)

/-- Exact external rejection of a public isolated block. -/
abbrev IsolatedCoreBlockPublicRejects (policy : CoreBlockTailPolicy) :=
  IsolatedCoreBlockRejects (CoreBlockPublicRejects policy)

/-- Deterministic ordinary outcomes of public block isolation. -/
theorem isolatedCoreBlockPublicOutcomeSpec (policy : CoreBlockTailPolicy) :
    DeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses policy)
      (IsolatedCoreBlockPublicRejects policy) :=
  isolatedCoreBlockDeterministicOutcomeSpec
    (coreBlockPublicOutcomeSpec policy)

end Solcore.Syntax.DeclarativeGrammar
