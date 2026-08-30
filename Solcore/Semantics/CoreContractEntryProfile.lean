import Solcore.Core.HostSafety
import Solcore.Semantics.FrameOutcome
import Solcore.Semantics.RuntimeScalars

/-! Typed completion conventions for syntax-independent checked Core contracts. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Initial checked-Core entry conventions understood by the top-level runner. -/
inductive CoreContractEntryProfile where
  | returnWord
  | wordOutcomeV1
  deriving Repr, BEq, DecidableEq

namespace CoreContractEntryProfile

/-- The Core result type required by one entry convention. -/
def resultType : CoreContractEntryProfile → Core.Ty
  | .returnWord => .word
  | .wordOutcomeV1 => .sum .word (.sum .word .word)

/-- Recognize exactly the result types supported by the initial contract ABI. -/
def ofResultType? : Core.Ty → Option CoreContractEntryProfile
  | .word => some .returnWord
  | .sum .word (.sum .word .word) => some .wordOutcomeV1
  | _ => none

/-- Decode one runtime value according to its contract-owned entry convention. -/
def decode?
    (profile : CoreContractEntryProfile)
    (value : Core.Value) : Option (FrameOutcome Core.Word) :=
  match profile, value with
  | .returnWord, .word word =>
      some (.returned (encodeWordBytesBE word))
  | .wordOutcomeV1, .inLeft (.sum .word .word) (.word word) =>
      some (.returned (encodeWordBytesBE word))
  | .wordOutcomeV1, .inRight .word (.inLeft .word (.word word)) =>
      some (.reverted (encodeWordBytesBE word))
  | .wordOutcomeV1, .inRight .word (.inRight .word (.word reason)) =>
      some (.trapped reason)
  | _, _ => none

/-- A host-runtime value of the profile's result type always decodes. -/
theorem decode?_ne_none_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    profile.decode? value ≠ none := by
  cases profile with
  | returnWord =>
      cases typing with
      | word => simp [decode?]
  | wordOutcomeV1 =>
      cases typing with
      | inLeft payloadTyping =>
          cases payloadTyping with
          | word => simp [decode?]
      | inRight payloadTyping =>
          cases payloadTyping with
          | inLeft innerTyping =>
              cases innerTyping with
              | word => simp [decode?]
          | inRight innerTyping =>
              cases innerTyping with
              | word => simp [decode?]

/-- The typed decoder's executable option is always populated. -/
theorem decode?_isSome_of_hasType
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    (profile.decode? value).isSome = true :=
  Option.isSome_iff_ne_none.mpr
    (profile.decode?_ne_none_of_hasType typing)

/-- Decode a well-typed completion without an invalid-value fallback branch. -/
def decodeTyped
    (profile : CoreContractEntryProfile)
    {world : Core.StoreTyping}
    {value : Core.Value}
    {definitions : Core.DataEnvironment}
    (typing :
      Core.HostRuntimeValueHasType world value profile.resultType definitions) :
    FrameOutcome Core.Word :=
  (profile.decode? value).get
    (profile.decode?_isSome_of_hasType typing)

end CoreContractEntryProfile

end Solcore.Semantics
