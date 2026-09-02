import Solcore.Syntax.DeclarativeContractDeriveAttachmentProperties
import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeProperties
import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeGrammar
import Solcore.Syntax.DeclarativeDeriveAttributeOutcomeProperties

/-!
Deterministic broad ordinary outcomes for public contract-member dispatch.
Pure derive attachment neither consumes input nor introduces a rejection stage.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {input : Remainder} {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False := by
  unfold ContractMemberCoreTokenPresentAt at present
  exact absent present

/-- Public contract-member success has one final remainder. -/
theorem ContractMemberOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | plain leftHashAbsent leftCoreParsed =>
      cases rightParsed with
      | plain rightHashAbsent rightCoreParsed =>
          exact contractMemberCoreDeterministicOutcomeSpec.successOutputUnique
            leftCoreParsed rightCoreParsed
      | derived rightHashPresent rightDeriveParsed rightCoreParsed
          rightAttached =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDeriveParsed leftCoreParsed leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightCoreParsed =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDeriveParsed rightCoreParsed
          rightAttached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              leftDeriveParsed rightDeriveParsed
          cases afterDeriveEq
          exact contractMemberCoreDeterministicOutcomeSpec.successOutputUnique
            leftCoreParsed rightCoreParsed

/-- Every exact public contract-member rejection excludes plain and
derive-prefixed success. -/
theorem ContractMemberRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : ContractMemberRejects input rejected) :
    ¬ ∃ member output, ContractMemberOrdinaryParses input member output := by
  rintro ⟨member, output, successful⟩
  cases rejection with
  | plainCoreRejected rejectedHashAbsent coreRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact contractMemberCoreDeterministicOutcomeSpec
            |>.successRejectDisjoint coreRejected ⟨_, _, coreParsed⟩
      | derived successfulHashPresent deriveParsed coreParsed attached =>
          exact absent_conflicts_token rejectedHashAbsent
            successfulHashPresent
  | deriveRejected rejectedHashPresent deriveRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent deriveParsed coreParsed attached =>
          exact deriveAttributeDeterministicOutcomeSpec
            |>.successRejectDisjoint deriveRejected ⟨_, _, deriveParsed⟩
  | derivedCoreRejected rejectedHashPresent rejectedDeriveParsed coreRejected =>
      cases successful with
      | plain successfulHashAbsent coreParsed =>
          exact absent_conflicts_token successfulHashAbsent
            rejectedHashPresent
      | derived successfulHashPresent successfulDeriveParsed coreParsed
          attached =>
          have afterDeriveEq :=
            deriveAttributeDeterministicOutcomeSpec.successOutputUnique
              rejectedDeriveParsed successfulDeriveParsed
          cases afterDeriveEq
          exact contractMemberCoreDeterministicOutcomeSpec
            |>.successRejectDisjoint coreRejected ⟨_, _, coreParsed⟩

/-- Public contract-member outcomes have deterministic successful remainders
and exact rejection/success exclusion. -/
theorem contractMemberDeterministicOutcomeSpec :
    DeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects where
  successOutputUnique := ContractMemberOrdinaryParses.output_unique
  successRejectDisjoint := ContractMemberRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
