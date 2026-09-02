import Solcore.Syntax.DeclarativeContractMemberWithAttributeOutcomeProperties
import Solcore.Syntax.DeclarativeDeriveAttributeExactnessProperties

/-!
Exactness transport through public contract-member derive attachment.

The only explicit premise is exactness of the attribute-free core dispatcher.
The derive parser and pure attachment relation are already exact.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {input : Remainder}
    {kind : TokenKind}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : ContractMemberCoreTokenPresentAt input kind) : False :=
  absent present

/-- The derive-attachment layer preserves exact success values whenever its
attribute-free core has exact outcomes. -/
theorem ContractMemberOrdinaryParses.value_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | plain leftHashAbsent leftCore =>
      cases rightParsed with
      | plain rightHashAbsent rightCore =>
          exact coreOutcomes.successValueUnique leftCore rightCore
      | derived rightHashPresent rightDerive rightCore rightAttached =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | derived leftHashPresent leftDerive leftCore leftAttached =>
      cases rightParsed with
      | plain rightHashAbsent rightCore =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | derived rightHashPresent rightDerive rightCore rightAttached =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique
              leftDerive rightDerive with
            ⟨deriveEq, afterDeriveEq⟩
          subst deriveEq
          subst afterDeriveEq
          rcases coreOutcomes.successResultUnique leftCore rightCore with
            ⟨coreEq, outputEq⟩
          subst coreEq
          exact leftAttached.output_unique rightAttached

/-- Under an exact core contract, the derive-attachment layer fixes its
contract-member AST and final remainder. -/
theorem ContractMemberOrdinaryParses.result_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_core coreOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- The derive-attachment layer preserves exact first-failure endpoints
whenever its attribute-free core has exact outcomes. -/
theorem ContractMemberRejects.output_unique_of_core
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects)
    {input left right : Remainder}
    (leftRejects : ContractMemberRejects input left)
    (rightRejects : ContractMemberRejects input right) : left = right := by
  cases leftRejects with
  | plainCoreRejected leftHashAbsent leftCoreRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact coreOutcomes.rejectOutputUnique leftCoreRejects
            rightCoreRejects
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
      | derivedCoreRejected rightHashPresent rightDerive rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token leftHashAbsent rightHashPresent)
  | deriveRejected leftHashPresent leftDeriveRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact deriveAttributeExactOutcomeSpec.rejectOutputUnique
            leftDeriveRejects rightDeriveRejects
      | derivedCoreRejected rightHashPresent rightDerive rightCoreRejects =>
          exact False.elim
            (deriveAttributeExactOutcomeSpec.successRejectDisjoint
              leftDeriveRejects ⟨_, _, rightDerive⟩)
  | derivedCoreRejected leftHashPresent leftDerive leftCoreRejects =>
      cases rightRejects with
      | plainCoreRejected rightHashAbsent rightCoreRejects =>
          exact False.elim
            (absent_conflicts_token rightHashAbsent leftHashPresent)
      | deriveRejected rightHashPresent rightDeriveRejects =>
          exact False.elim
            (deriveAttributeExactOutcomeSpec.successRejectDisjoint
              rightDeriveRejects ⟨_, _, leftDerive⟩)
      | derivedCoreRejected rightHashPresent rightDerive
            rightCoreRejects =>
          rcases deriveAttributeExactOutcomeSpec.successResultUnique
              leftDerive rightDerive with
            ⟨deriveEq, afterDeriveEq⟩
          subst deriveEq
          subst afterDeriveEq
          exact coreOutcomes.rejectOutputUnique leftCoreRejects
            rightCoreRejects

/-- Exact contract for the complete public contract-member derive layer,
parameterized only by exactness of its attribute-free core. -/
theorem contractMemberExactOutcomeSpecOfCore
    (coreOutcomes : ExactDeterministicOutcomeSpec
      ContractMemberCoreOrdinaryParses ContractMemberCoreRejects) :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects where
  toDeterministicOutcomeSpec := contractMemberDeterministicOutcomeSpec
  successValueUnique :=
    ContractMemberOrdinaryParses.value_unique_of_core coreOutcomes
  rejectOutputUnique :=
    ContractMemberRejects.output_unique_of_core coreOutcomes

end Solcore.Syntax.DeclarativeGrammar
