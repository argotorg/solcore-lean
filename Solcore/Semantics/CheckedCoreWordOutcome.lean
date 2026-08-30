import Solcore.Semantics.CheckedCoreContract

/-! Word-preserving completion decoding for checked Core contract profiles. -/

set_option autoImplicit false

namespace Solcore.Semantics

/--
The exact Word payload carried by every currently supported checked-Core
completion convention.
-/
inductive CheckedCoreWordOutcome where
  | returned (data : Core.Word)
  | reverted (data : Core.Word)
  | trapped (reason : Core.Word)
  deriving Repr, BEq, DecidableEq

namespace CheckedCoreWordOutcome

/-- Forget only the Word-level view, retaining the canonical byte encoding. -/
def toFrameOutcome : CheckedCoreWordOutcome → FrameOutcome Core.Word
  | .returned data => .returned (encodeWordBytesBE data)
  | .reverted data => .reverted (encodeWordBytesBE data)
  | .trapped reason => .trapped reason

end CheckedCoreWordOutcome

namespace CoreContractEntryProfile

/-- Decode a runtime value while retaining its exact Word payload. -/
def decodeWordOutcome?
    (profile : CoreContractEntryProfile)
    (value : Core.Value) : Option CheckedCoreWordOutcome :=
  match profile, value with
  | .returnWord, .word word =>
      some (.returned word)
  | .wordOutcomeV1, .inLeft (.sum .word .word) (.word word) =>
      some (.returned word)
  | .wordOutcomeV1, .inRight .word (.inLeft .word (.word word)) =>
      some (.reverted word)
  | .wordOutcomeV1, .inRight .word (.inRight .word (.word reason)) =>
      some (.trapped reason)
  | _, _ => none

/-- A value of the profile result type always has an exact Word outcome. -/
theorem decodeWordOutcome?_ne_none_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decodeWordOutcome? value ≠ none := by
  cases profile with
  | returnWord =>
      cases typing with
      | word => simp [decodeWordOutcome?]
  | wordOutcomeV1 =>
      cases typing with
      | inLeft payloadTyping =>
          cases payloadTyping with
          | word => simp [decodeWordOutcome?]
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => simp [decodeWordOutcome?]
          | inRight innerTyping =>
              cases innerTyping with
              | word => simp [decodeWordOutcome?]

/-- The executable Word decoder is populated for every typed profile value. -/
theorem decodeWordOutcome?_isSome_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    (profile.decodeWordOutcome? value).isSome = true :=
  Option.isSome_iff_ne_none.mpr
    (profile.decodeWordOutcome?_ne_none_of_hasType typing)

/-- Decode a typed profile value without an invalid-value fallback branch. -/
def decodeWordOutcome
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    CheckedCoreWordOutcome :=
  (profile.decodeWordOutcome? value).get
    (profile.decodeWordOutcome?_isSome_of_hasType typing)

end CoreContractEntryProfile

namespace CheckedCoreContract

/-- Run the contract-owned decoder while retaining its exact Word payload. -/
def decodeWordOutcome?
    (contract : CheckedCoreContract)
    (value : Core.Value) : Option CheckedCoreWordOutcome :=
  contract.entryProfile.decodeWordOutcome? value

/-- Decode a checked contract result without an invalid-value fallback. -/
def decodeWordOutcome
    (contract : CheckedCoreContract)
    {world : Core.StoreTyping}
    {value : Core.Value}
    (typing :
      Core.HostRuntimeValueHasType world value
        contract.code.program.resultType
        contract.code.program.dataDefinitions) :
    CheckedCoreWordOutcome :=
  contract.entryProfile.decodeWordOutcome (by
    rw [← contract.resultType_eq]
    exact typing)

end CheckedCoreContract

end Solcore.Semantics
