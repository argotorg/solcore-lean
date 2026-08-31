import Solcore.Syntax.Parser.ContractBodyTotalityProperties
import Solcore.Syntax.Parser.DeriveAttributeTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.TypeAliasTotalityProperties

/-! Conditional totality for canonical contract-member dispatch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Mapping a successful declaration cannot introduce an invariant reply. -/
theorem mapMember_invariantFreeOnValid {alpha : Type}
    (parser : Parser alpha) (wrap : alpha → ContractMember)
    (invariantFree : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (mapMember parser wrap) := by
  intro input inputValid
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · left
    exact ⟨wrap value, next, by
      unfold mapMember
      simp only [bind, result, pure]⟩
  · right
    exact ⟨failure, next, by
      unfold mapMember
      simp only [bind, result]⟩

/-- The five declaration parsers selected by contract-member dispatch. -/
structure ContractMemberTotalityContract : Prop where
  field : Parser.InvariantFreeOnValid (contractField expression)
  function : Parser.InvariantFreeOnValid (functionDecl .contract)
  constructor : Parser.InvariantFreeOnValid constructorDecl
  fallback : Parser.InvariantFreeOnValid fallbackDecl
  enum : Parser.InvariantFreeOnValid (enumDecl none)

/-- The state-selected plain member parser inherits exactly those five inputs. -/
theorem contractMemberParser_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) (state : State) :
    Parser.InvariantFreeOnValid (contractMemberParser state) := by
  unfold contractMemberParser
  split
  · exact mapMember_invariantFreeOnValid _ wrapField contract.field
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractFunction
      contract.function
  split
  · exact mapMember_invariantFreeOnValid _ wrapConstructor
      contract.constructor
  split
  · exact mapMember_invariantFreeOnValid _ wrapFallback contract.fallback
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractTypeAlias
      typeAlias_invariantFreeOnValid
  split
  · exact mapMember_invariantFreeOnValid _ wrapContractEnum contract.enum
  · exact Parser.rejectAt_invariantFreeOnValid
      (alpha := ContractMember) { head := .topItem, tail := [] }
      .contractMember

/-- Plain contract-member dispatch is invariant-free on valid input. -/
theorem contractMemberCore_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) :
    Parser.InvariantFreeOnValid contractMemberCore := by
  intro input inputValid
  exact contractMemberParser_invariantFreeOnValid contract input
    input inputValid

/-- Attaching a derive attribute is a total state update. -/
theorem attachContractDerive_invariantFreeOnValid
    (derive : DeriveAttribute) (member : ContractMember) :
    Parser.InvariantFreeOnValid (attachContractDerive derive member) := by
  intro input _inputValid
  rcases member with ⟨span, comments, value⟩
  cases value <;> left <;>
    simp [attachContractDerive, emitDiagnostic, modifyState, bind, pure]

/-- Derive-aware member dispatch inherits only the same five branch inputs. -/
theorem contractMemberWithAttribute_invariantFreeOnValid
    (contract : ContractMemberTotalityContract) :
    Parser.InvariantFreeOnValid contractMemberWithAttribute := by
  intro input inputValid
  unfold contractMemberWithAttribute
  by_cases attributed : isSymbol input .hash
  · simp only [attributed, if_true]
    have deriveReply := deriveAttribute_validFor input inputValid
    rcases deriveAttribute_ordinary input inputValid with
      ⟨derive, afterDerive, deriveResult⟩ |
      ⟨failure, rejected, deriveResult⟩
    · rw [deriveResult] at deriveReply
      have memberReply := contractMemberCore_canonical_contract.validFor
        afterDerive deriveReply.2.1
      rcases contractMemberCore_invariantFreeOnValid contract afterDerive
          deriveReply.2.1 with
        ⟨member, next, memberResult⟩ |
        ⟨failure, rejected, memberResult⟩
      · rw [memberResult] at memberReply
        rcases attachContractDerive_invariantFreeOnValid derive member next
            memberReply.2.1 with
          ⟨attached, final, attachedResult⟩ |
          ⟨failure, rejected, attachedResult⟩
        · left
          exact ⟨attached, final, by
            simp only [deriveResult, memberResult, attachedResult]⟩
        · right
          exact ⟨failure, rejected, by
            simp only [deriveResult, memberResult, attachedResult]⟩
      · right
        exact ⟨failure, rejected, by
          simp only [deriveResult, memberResult]⟩
    · right
      exact ⟨failure, rejected, by simp only [deriveResult]⟩
  · simpa [attributed] using
      contractMemberCore_invariantFreeOnValid contract input inputValid

/-- No invariant can escape derive-aware member parsing under five inputs. -/
theorem contractMemberWithAttribute_ne_invariant
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractMemberWithAttribute input ≠ .invariant error :=
  (contractMemberWithAttribute_invariantFreeOnValid contract).ne_invariant
    input inputValid error

/-- Convert the five-field contract to the contract-body loop premise. -/
theorem contractMemberInvariantFree_of_totalityContract
    (contract : ContractMemberTotalityContract) :
    ContractMemberInvariantFreeOnValid := by
  intro input inputValid error
  exact contractMemberWithAttribute_ne_invariant contract input inputValid error

/-- Contract-body parsing is ordinary under exactly the five member inputs. -/
theorem contractBody_ordinary_of_memberTotalityContract
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) :=
  contractBody_ordinary
    (contractMemberInvariantFree_of_totalityContract contract) input inputValid

/-- Contract-body invariants are unreachable under the same five inputs. -/
theorem contractBody_ne_invariant_of_memberTotalityContract
    (contract : ContractMemberTotalityContract)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error :=
  contractBody_ne_invariant
    (contractMemberInvariantFree_of_totalityContract contract)
    input inputValid error

end Solcore.Syntax.Parser.ContractInternals
