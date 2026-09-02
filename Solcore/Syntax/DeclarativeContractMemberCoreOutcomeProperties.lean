import Solcore.Syntax.DeclarativeContractMemberCoreRejectionProperties
import Solcore.Syntax.DeclarativeContractMemberCoreSuccessProperties

/-! Deterministic broad outcomes for attribute-free contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Attribute-free contract members have deterministic successful remainders,
and their exact selected-branch rejections exclude success. -/
theorem contractMemberCoreDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects where
  successOutputUnique := ContractMemberCoreOrdinaryParses.output_unique
  successRejectDisjoint := ContractMemberCoreRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
