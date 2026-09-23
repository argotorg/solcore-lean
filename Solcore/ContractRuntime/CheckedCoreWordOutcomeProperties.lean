import Solcore.ContractRuntime.CheckedCoreWordOutcome
import Solcore.ContractRuntime.CoreContractEntryProfileProperties

/-! Exact laws for Word-preserving checked-Core completion decoding. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

namespace CheckedCoreWordOutcome

@[simp] theorem toFrameOutcome_returned (data : Core.Word) :
    (returned data).toFrameOutcome =
      FrameOutcome.returned (encodeWordBytesBE data) :=
  rfl

@[simp] theorem toFrameOutcome_reverted (data : Core.Word) :
    (reverted data).toFrameOutcome =
      FrameOutcome.reverted (encodeWordBytesBE data) :=
  rfl

@[simp] theorem toFrameOutcome_trapped (reason : Core.Word) :
    (trapped reason).toFrameOutcome = FrameOutcome.trapped reason :=
  rfl

end CheckedCoreWordOutcome

namespace CoreContractEntryProfile

@[simp] theorem decodeWordOutcome?_returnWord (word : Core.Word) :
    decodeWordOutcome? .returnWord (.word word) =
      some (.returned word) :=
  rfl

@[simp] theorem decodeWordOutcome?_wordOutcomeV1_returned
    (word : Core.Word) :
    decodeWordOutcome? .wordOutcomeV1
        (.inLeft (.sum .word .word) (.word word)) =
      some (.returned word) :=
  rfl

@[simp] theorem decodeWordOutcome?_wordOutcomeV1_reverted
    (word : Core.Word) :
    decodeWordOutcome? .wordOutcomeV1
        (.inRight .word (.inLeft .word (.word word))) =
      some (.reverted word) :=
  rfl

@[simp] theorem decodeWordOutcome?_wordOutcomeV1_trapped
    (reason : Core.Word) :
    decodeWordOutcome? .wordOutcomeV1
        (.inRight .word (.inRight .word (.word reason))) =
      some (.trapped reason) :=
  rfl

/-- Forgetting the Word view agrees exactly with the established decoder. -/
theorem decode?_eq_map_decodeWordOutcome?
    (profile : CoreContractEntryProfile)
    (value : Core.Value) :
    profile.decode? value =
      (profile.decodeWordOutcome? value).map
        CheckedCoreWordOutcome.toFrameOutcome := by
  cases profile <;>
    simp only [CoreContractEntryProfile.decode?, decodeWordOutcome?] <;>
    split <;> simp_all [CheckedCoreWordOutcome.toFrameOutcome]

/-- Typed decoding commutes exactly with forgetting the Word-level payload. -/
theorem decodeTyped_eq_toFrameOutcome_decodeWordOutcome
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decodeTyped typing =
      (profile.decodeWordOutcome typing).toFrameOutcome := by
  cases profile with
  | returnWord =>
      cases typing with
      | word => rfl
  | wordOutcomeV1 =>
      cases typing with
      | inLeft payloadTyping =>
          cases payloadTyping with
          | word => rfl
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => rfl
          | inRight innerTyping =>
              cases innerTyping with
              | word => rfl

/-- A typed profile result is returned by its executable Word decoder. -/
theorem decodeWordOutcome?_eq_some_decodeWordOutcome
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decodeWordOutcome? value =
      some (profile.decodeWordOutcome typing) := by
  have populated : profile.decodeWordOutcome? value ≠ none :=
    profile.decodeWordOutcome?_ne_none_of_hasType typing
  cases decoded : profile.decodeWordOutcome? value with
  | none => exact False.elim (populated decoded)
  | some outcome =>
      simp [CoreContractEntryProfile.decodeWordOutcome, decoded]

end CoreContractEntryProfile

namespace CheckedCoreContract

/-- Contract decoding inherits the exact profile-level option coherence. -/
theorem decodeCompletion?_eq_map_decodeWordOutcome?
    (contract : CheckedCoreContract)
    (value : Core.Value) :
    contract.decodeCompletion? value =
      (contract.decodeWordOutcome? value).map
        CheckedCoreWordOutcome.toFrameOutcome :=
  contract.entryProfile.decode?_eq_map_decodeWordOutcome? value

/-- A typed contract result is always returned by its executable Word decoder. -/
theorem decodeWordOutcome?_eq_some_decodeWordOutcome
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    contract.decodeWordOutcome? value =
      some (contract.decodeWordOutcome typing) := by
  have profileTyping :
      Core.HostRuntimeValueHasType world value
        contract.entryProfile.resultType
        contract.code.program.dataDefinitions := by
    rw [← contract.resultType_eq]
    exact typing
  simpa [CheckedCoreContract.decodeWordOutcome?,
    CheckedCoreContract.decodeWordOutcome] using
      contract.entryProfile.decodeWordOutcome?_eq_some_decodeWordOutcome
        profileTyping

/-- Typed contract decoding agrees exactly after canonical Word-byte encoding. -/
theorem decodeCompletion_eq_toFrameOutcome_decodeWordOutcome
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    contract.decodeCompletion typing =
      (contract.decodeWordOutcome typing).toFrameOutcome := by
  have coherence :=
    contract.decodeCompletion?_eq_map_decodeWordOutcome? value
  rw [contract.decodeCompletion?_eq_some_decodeCompletion typing,
    contract.decodeWordOutcome?_eq_some_decodeWordOutcome typing] at coherence
  exact Option.some.inj coherence

end CheckedCoreContract

end Solcore.ContractRuntime
