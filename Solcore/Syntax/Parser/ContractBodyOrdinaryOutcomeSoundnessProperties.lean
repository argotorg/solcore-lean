import Solcore.Syntax.DeclarativeContractBodyExactnessProperties
import Solcore.Syntax.Parser.ContractBodyTailOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ContractBodyTailOrdinarySuccessSoundnessProperties

/-! Complete broad executable outcomes for recovery-aware contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful public contract-body parse has exact braces, covered
span, source-order direct/recovered members, and final remainder. -/
theorem contractBody_success_ordinaryOutcome_sound
    {input output : State} {body : ContractBody}
    (result : contractBody input = .ok body output) :
    DeclarativeGrammar.ContractBodyOrdinaryParses input.declarativeRemainder
      body.span body.members output.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      rcases contractMembers_success_ordinaryOutcome_sound_strong opening
          (afterOpening.remainingCount + 1) [] afterOpening body output result
          with ⟨members, closingSpan, bodyEq, tailParsed⟩
      rw [bodyEq]
      simpa using
        (DeclarativeGrammar.ContractBodyOrdinaryParses.parsed opening.span
          closingSpan
          (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
          tailParsed)

/-- Every public contract-body rejection records an opening-brace failure or
the exact first rejection of the recovery-aware member loop. -/
theorem contractBody_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : contractBody input = .reject failure rejected) :
    DeclarativeGrammar.ContractBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold contractBody at result
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at result
  | reject openingFailure openingRejected =>
      simp only [openingResult] at result
      have rejectedEq : openingRejected = rejected := by injection result
      rw [← rejectedEq,
        symbol_reject_state_eq .leftBrace .topItem openingResult]
      exact .openingMissing
        (symbol_reject_tokenKindAbsentAt .leftBrace .topItem openingResult)
  | ok opening afterOpening =>
      simp only [openingResult] at result
      exact .tailRejected opening.span
        (symbol_success_exactTokenParses .leftBrace .topItem openingResult)
        (contractMembers_reject_ordinaryOutcome_sound opening
          (afterOpening.remainingCount + 1) [] afterOpening failure rejected
          result)

/-- Package unconditional public contract-body success and exact rejection. -/
theorem contractBody_ordinaryOutcome_sound :
    (∀ {input output : State} {body : ContractBody},
      contractBody input = .ok body output →
        DeclarativeGrammar.ContractBodyOrdinaryParses
          input.declarativeRemainder body.span body.members
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      contractBody input = .reject failure rejected →
        DeclarativeGrammar.ContractBodyRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨contractBody_success_ordinaryOutcome_sound,
    contractBody_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive broad contract-body outcomes. -/
theorem contractBody_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyDeterministicOutcomeSpec

/-- Exact derive-aware member outcomes lift through contract-body recovery. -/
theorem contractBody_exactOutcomeSpec_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpecOfMember memberOutcomes

/-- Exact attribute-free member outcomes lift through derive attachment and
contract-body recovery. -/
theorem contractBody_exactOutcomeSpec_of_core
    (coreOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      DeclarativeGrammar.ContractMemberCoreRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
      DeclarativeGrammar.ContractBodyRejects :=
  DeclarativeGrammar.contractBodyExactOutcomeSpecOfCore coreOutcomes

/-- Under exact member outcomes, two executable bodies have the same value
and declarative remainder. -/
theorem contractBody_success_result_unique_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects)
    {input leftOutput rightOutput : State}
    {left right : ContractBody}
    (leftResult : contractBody input = .ok left leftOutput)
    (rightResult : contractBody input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder := by
  rcases (contractBody_exactOutcomeSpec_of_member memberOutcomes)
      |>.successResultUnique
        (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
          input.declarativeRemainder (left.span, left.members)
            leftOutput.declarativeRemainder from
          contractBody_success_ordinaryOutcome_sound leftResult)
        (show DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
          input.declarativeRemainder (right.span, right.members)
            rightOutput.declarativeRemainder from
          contractBody_success_ordinaryOutcome_sound rightResult) with
    ⟨bodyEq, outputEq⟩
  constructor
  · cases left
    cases right
    simp_all
  · exact outputEq

/-- Under exact member outcomes, two body rejections have one declarative
endpoint. -/
theorem contractBody_reject_output_unique_of_member
    (memberOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberOrdinaryParses
      DeclarativeGrammar.ContractMemberRejects)
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : contractBody input = .reject leftFailure leftOutput)
    (rightResult : contractBody input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (contractBody_exactOutcomeSpec_of_member memberOutcomes).rejectOutputUnique
    (contractBody_reject_ordinaryOutcome_sound leftResult)
    (contractBody_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
