import Solcore.Semantics.CheckedCoreContract

/-! Exact recognition and decoding laws for checked Core contract entries. -/

set_option autoImplicit false

namespace Solcore.Semantics

namespace CoreContractEntryProfile

@[simp] theorem ofResultType?_resultType
    (profile : CoreContractEntryProfile) :
    ofResultType? profile.resultType = some profile := by
  cases profile <;> rfl

theorem resultType_injective :
    Function.Injective CoreContractEntryProfile.resultType := by
  intro left right equal
  cases left <;> cases right <;>
    simp [resultType] at equal ⊢

@[simp] theorem decode?_returnWord
    (word : Core.Word) :
    decode? .returnWord (.word word) =
      some (.returned (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_returned
    (word : Core.Word) :
    decode? .wordOutcomeV1
        (.inLeft (.sum .word .word) (.word word)) =
      some (.returned (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_reverted
    (word : Core.Word) :
    decode? .wordOutcomeV1
        (.inRight .word (.inLeft .word (.word word))) =
      some (.reverted (encodeWordBytesBE word)) := by
  rfl

@[simp] theorem decode?_wordOutcomeV1_trapped
    (reason : Core.Word) :
    decode? .wordOutcomeV1
        (.inRight .word (.inRight .word (.word reason))) =
      some (.trapped reason) := by
  rfl

end CoreContractEntryProfile

namespace CheckedCoreContract

theorem ofCode?_of_resultType
    (code : CheckedHostCoreProgram)
    (profile : CoreContractEntryProfile)
    (resultType_eq : code.program.resultType = profile.resultType) :
    ofCode? code = some ⟨code, profile, resultType_eq⟩ := by
  cases profile <;>
    simp [ofCode?, CoreContractEntryProfile.ofResultType?,
      CoreContractEntryProfile.resultType, resultType_eq]

theorem decodeCompletion?_eq_some_decodeCompletion
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    contract.decodeCompletion? value =
      some (contract.decodeCompletion typing) := by
  have populated : contract.decodeCompletion? value ≠ none := by
    apply contract.entryProfile.decode?_ne_none_of_hasType
    rw [← contract.resultType_eq]
    exact typing
  cases decoded : contract.decodeCompletion? value with
  | none => exact False.elim (populated decoded)
  | some outcome =>
      simp [decodeCompletion, decoded]

end CheckedCoreContract

end Solcore.Semantics
