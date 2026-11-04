import Solcore.ContractRuntime.StorageDriver
import Solcore.Core.HostMachine
import Solcore.Core.Internal.HostPreservation
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.Internal.ScalarLaws
import Solcore.ContractRuntime.Internal.FrameLaws
import Solcore.ContractRuntime.Internal.DriverLaws
import Solcore.ContractRuntime.Internal.WorldStateLaws

/-!
# Laws of storage-backed host handling

Input data reads, the context, each request's response and effect on the context, and the storage
driver's run, down to `CheckedHostCoreProgram.runWithStorage`.
-/

section
-- leanmerge: from Solcore.ContractRuntime.ContractCallFailure
/-! Internal failure reasons for dispatching one checked contract-word call. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.ContractCallFailureProperties`
-/

/-! Exact codes and response injection for internal call-dispatch failures. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ContractCallFailure

theorem code_injective : Function.Injective code := by
  intro left right equal
  cases left <;> cases right <;> simp_all [code]

theorem code_eq_iff (left right : ContractCallFailure) :
    left.code = right.code ↔ left = right :=
  ⟨fun equal => code_injective equal, congrArg code⟩

theorem result_injective : Function.Injective result := by
  intro left right equal
  cases left <;> cases right <;> simp_all [result, code]

@[simp] theorem code_insufficientBalance :
    insufficientBalance.code = ⟨3, by decide⟩ :=
  rfl

@[simp] theorem code_balanceOverflow :
    balanceOverflow.code = ⟨4, by decide⟩ :=
  rfl

@[simp] theorem code_nonceOverflow :
    nonceOverflow.code = ⟨5, by decide⟩ :=
  rfl

@[simp] theorem code_addressCollision :
    addressCollision.code = ⟨6, by decide⟩ :=
  rfl

@[simp] theorem result_value (failure : ContractCallFailure) :
    failure.result.value =
      .inRight .word
        (.inRight .word (.inRight .word (.word failure.code))) :=
  rfl

end Solcore.ContractRuntime.ContractCallFailure
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageInputData
/-! Bounded raw input bytes shared by one handled execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageInputDataProperties`
-/

/-! Exact length and byte-lookup laws for bounded raw input data. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

namespace InputData

@[simp] theorem mk_bytes
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).bytes = bytes :=
  rfl

@[simp] theorem mk_size_lt_wordModulus
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).size_lt_wordModulus =
      size_lt_wordModulus :=
  rfl

/-- Every position in the bounded byte sequence has an exact Core Word index. -/
theorem exists_word_offset_of_lt_size
    (input : InputData) (index : Nat)
    (inBounds : index < input.bytes.size) :
    ∃ offset : Core.Word, offset.val = index :=
  ⟨⟨index, Nat.lt_trans inBounds input.size_lt_wordModulus⟩, rfl⟩

@[simp] theorem sizeWord_val (input : InputData) :
    input.sizeWord.val = input.bytes.size :=
  rfl

@[simp] theorem mk_sizeWord
    (bytes : Bytes) (size_lt_wordModulus : bytes.size < Core.wordModulus) :
    (InputData.mk bytes size_lt_wordModulus).sizeWord =
      ⟨bytes.size, size_lt_wordModulus⟩ :=
  rfl

theorem byte?_eq_some_iff
    (input : InputData) (offset result : Core.Word) :
    input.byte? offset = some result ↔
      ∃ byte,
        input.bytes.data[offset.val]? = some byte ∧
          result.val = byte.toNat := by
  cases lookup : input.bytes.data[offset.val]? with
  | none => simp [byte?, lookup]
  | some byte =>
      constructor
      · intro observed
        have resultEq :
            result = ⟨byte.toNat,
              Nat.lt_trans byte.toFin.isLt (by decide)⟩ := by
          exact (Option.some.inj
            (by simpa [byte?, lookup] using observed)).symm
        exact ⟨byte, rfl, congrArg Fin.val resultEq⟩
      · rintro ⟨found, foundLookup, valueEq⟩
        have foundEq : found = byte := by
          exact (Option.some.inj foundLookup).symm
        subst found
        have resultEq :
            result = ⟨byte.toNat,
              Nat.lt_trans byte.toFin.isLt (by decide)⟩ :=
          Fin.ext valueEq
        subst result
        simp [byte?, lookup]

@[simp] theorem byte?_eq_none_iff
    (input : InputData) (offset : Core.Word) :
    input.byte? offset = none ↔
      input.bytes.data[offset.val]? = none := by
  cases lookup : input.bytes.data[offset.val]? <;>
    simp [byte?, lookup]

theorem byte?_result_lt_256
    (input : InputData) (offset result : Core.Word)
    (read : input.byte? offset = some result) :
    result.val < 256 := by
  obtain ⟨byte, _, resultValue⟩ :=
    (byte?_eq_some_iff input offset result).mp read
  rw [resultValue]
  exact byte.toFin.isLt

@[simp] theorem byte?_eq_some_zero_of_lookup_zero
    (input : InputData) (offset : Core.Word)
    (lookup : input.bytes.data[offset.val]? = some 0) :
    input.byte? offset = some Core.Word.zero := by
  apply (byte?_eq_some_iff input offset Core.Word.zero).2
  exact ⟨0, lookup, rfl⟩

@[simp] theorem byte?_eq_none_of_size_le
    (input : InputData) (offset : Core.Word)
    (outOfBounds : input.bytes.size ≤ offset.val) :
    input.byte? offset = none := by
  rw [byte?_eq_none_iff]
  apply Array.getElem?_eq_none
  simpa only [ByteArray.size_data] using outOfBounds

theorem byte?_eq_some_of_lt_size
    (input : InputData) (offset : Core.Word)
    (inBounds : offset.val < input.bytes.size) :
    ∃ result,
      input.byte? offset = some result ∧
        result.val =
          (input.bytes.data[offset.val]'(by
            simpa only [ByteArray.size_data] using inBounds)).toNat := by
  let byte := input.bytes.data[offset.val]'(by
    simpa only [ByteArray.size_data] using inBounds)
  have lookup : input.bytes.data[offset.val]? = some byte := by
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨by simpa only [ByteArray.size_data] using inBounds, rfl⟩
  let result : Core.Word :=
    ⟨byte.toNat, Nat.lt_trans byte.toFin.isLt (by decide)⟩
  refine ⟨result, ?_, rfl⟩
  exact (byte?_eq_some_iff input offset result).2
    ⟨byte, lookup, rfl⟩

theorem exists_byte?_eq_some_iff_lt_sizeWord
    (input : InputData) (offset : Core.Word) :
    (∃ result, input.byte? offset = some result) ↔
      offset.val < input.sizeWord.val := by
  constructor
  · rintro ⟨result, present⟩
    obtain ⟨byte, lookup, _⟩ :=
      (byte?_eq_some_iff input offset result).1 present
    have inBounds : offset.val < input.bytes.data.size :=
      (Array.getElem?_eq_some_iff.mp lookup).1
    simpa only [sizeWord_val, ByteArray.size_data] using inBounds
  · intro inBounds
    obtain ⟨result, present, _⟩ :=
      byte?_eq_some_of_lt_size input offset (by simpa using inBounds)
    exact ⟨result, present⟩

theorem byte?_eq_none_iff_sizeWord_le
    (input : InputData) (offset : Core.Word) :
    input.byte? offset = none ↔ input.sizeWord.val ≤ offset.val := by
  constructor
  · intro absent
    exact Nat.le_of_not_gt fun inBounds => by
      obtain ⟨result, present⟩ :=
        (exists_byte?_eq_some_iff_lt_sizeWord input offset).2 inBounds
      rw [present] at absent
      cases absent
  · intro outOfBounds
    exact byte?_eq_none_of_size_le input offset (by simpa using outOfBounds)

@[simp] theorem byte?_sizeWord (input : InputData) :
    input.byte? input.sizeWord = none :=
  (byte?_eq_none_iff_sizeWord_le input input.sizeWord).2 (Nat.le_refl _)

/-- The strict Word decoder succeeds exactly on 32-byte inputs. -/
theorem exists_decodeWordBytesBE?_eq_some_iff_size_eq_32
    (bytes : Bytes) :
    (∃ word, decodeWordBytesBE? bytes = some word) ↔ bytes.size = 32 := by
  unfold decodeWordBytesBE? RuntimeScalar.Internal.wordDigitsOfBytes?
  split
  next lengthEq =>
    simp [lengthEq]
  next lengthNe =>
    simp [lengthNe]

/-- A fully bounded half-open Word window has exactly 32 bytes. -/
theorem extract_wordBE_window_size
    (input : InputData) (offset : Core.Word)
    (full : offset.val + 32 ≤ input.bytes.size) :
    (input.bytes.extract offset.val (offset.val + 32)).size = 32 := by
  simp only [ByteArray.size_extract]
  rw [Nat.min_eq_left full]
  omega

/-- A returned Word is precisely the canonical decoding of the selected window. -/
theorem wordBE?_eq_some_iff
    (input : InputData) (offset word : Core.Word) :
    input.wordBE? offset = some word ↔
      offset.val + 32 ≤ input.sizeWord.val ∧
        input.bytes.extract offset.val (offset.val + 32) =
          encodeWordBytesBE word := by
  unfold wordBE?
  split
  next full =>
    constructor
    · intro success
      refine ⟨by simpa using full, ?_⟩
      exact (encodeWordBytesBE_of_decodeWordBytesBE?_eq_some
        _ word success).symm
    · rintro ⟨_, selected⟩
      rw [selected]
      simp
  next incomplete =>
    constructor
    · intro impossible
      contradiction
    · rintro ⟨full, _⟩
      exact (incomplete (by simpa using full)).elim

/-- Word observation succeeds exactly when the complete natural-number window exists. -/
theorem exists_wordBE?_eq_some_iff_full_window
    (input : InputData) (offset : Core.Word) :
    (∃ word, input.wordBE? offset = some word) ↔
      offset.val + 32 ≤ input.sizeWord.val := by
  constructor
  · rintro ⟨word, success⟩
    exact (wordBE?_eq_some_iff input offset word).1 success |>.1
  · intro full
    have extractedSize :
        (input.bytes.extract offset.val (offset.val + 32)).size = 32 :=
      extract_wordBE_window_size input offset (by simpa using full)
    obtain ⟨word, decoded⟩ :=
      (exists_decodeWordBytesBE?_eq_some_iff_size_eq_32
        (input.bytes.extract offset.val (offset.val + 32))).2 extractedSize
    refine ⟨word, ?_⟩
    unfold wordBE?
    rw [if_pos (by simpa using full)]
    exact decoded

/-- Absence means exactly that fewer than 32 bytes remain at the exact offset. -/
@[simp] theorem wordBE?_eq_none_iff
    (input : InputData) (offset : Core.Word) :
    input.wordBE? offset = none ↔
      input.sizeWord.val < offset.val + 32 := by
  constructor
  · intro absent
    apply Nat.lt_of_not_ge
    intro full
    obtain ⟨word, present⟩ :=
      (exists_wordBE?_eq_some_iff_full_window input offset).2 full
    rw [present] at absent
    contradiction
  · intro incomplete
    unfold wordBE?
    rw [if_neg]
    exact Nat.not_le_of_gt (by simpa using incomplete)

/-- Every successful observation selected an exact 32-byte carrier. -/
theorem wordBE?_extract_size_of_eq_some
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) :
    (input.bytes.extract offset.val (offset.val + 32)).size = 32 := by
  apply extract_wordBE_window_size input offset
  simpa using (wordBE?_eq_some_iff input offset word).1 success |>.1

/-- Every byte in a successful window remains below the exact input size. -/
theorem wordBE?_position_lt_sizeWord
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32) :
    offset.val + index.val < input.sizeWord.val := by
  have full := (wordBE?_eq_some_iff input offset word).1 success |>.1
  omega

/-- Each successful-window position has a lossless Core Word representation. -/
theorem exists_word_offset_of_wordBE?_eq_some
    (input : InputData) (offset word : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32) :
    ∃ position : Core.Word, position.val = offset.val + index.val := by
  apply exists_word_offset_of_lt_size input
  simpa using wordBE?_position_lt_sizeWord input offset word success index

/-- Single-byte observation agrees with the corresponding encoded Word byte. -/
theorem wordBE?_byte?_eq_encoded_byte
    (input : InputData) (offset word position : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32)
    (positionEq : position.val = offset.val + index.val) :
    input.byte? position =
      some (Core.Word.ofNatModulo
        ((encodeWordBytesBE word)[index.val]'(by simp)).toNat) := by
  have full := (wordBE?_eq_some_iff input offset word).1 success |>.1
  have windowEq := (wordBE?_eq_some_iff input offset word).1 success |>.2
  let byte := (encodeWordBytesBE word)[index.val]'(by simp)
  have selectedLookup :
      (input.bytes.extract offset.val (offset.val + 32)).data[index.val]? =
        some byte := by
    rw [windowEq]
    apply Array.getElem?_eq_some_iff.mpr
    exact ⟨by simp, rfl⟩
  have extractIndex :
      index.val <
        min (offset.val + 32) input.bytes.data.size - offset.val := by
    rw [ByteArray.size_data]
    rw [Nat.min_eq_left (by simpa using full)]
    omega
  have sourceLookup :
      input.bytes.data[offset.val + index.val]? = some byte := by
    simpa only [ByteArray.data_extract, Array.getElem?_extract,
      if_pos extractIndex] using selectedLookup
  have lookup : input.bytes.data[position.val]? = some byte := by
    simpa only [positionEq] using sourceLookup
  apply (byte?_eq_some_iff input position _).2
  refine ⟨byte, lookup, ?_⟩
  simp only [Core.Word.ofNatModulo]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_trans byte.toFin.isLt (by decide)

/-- Single-byte observation agrees with Core's big-endian `Word.byteAt`. -/
theorem wordBE?_byte?_eq_byteAt
    (input : InputData) (offset word position : Core.Word)
    (success : input.wordBE? offset = some word) (index : Fin 32)
    (positionEq : position.val = offset.val + index.val) :
    input.byte? position =
      some ((Core.Word.ofNatModulo index.val).byteAt word) := by
  rw [← encodeWordBytesBE_getElem_byteAt word index]
  exact wordBE?_byte?_eq_encoded_byte
    input offset word position success index positionEq

end InputData

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.ContractWordCallInput
/-! Exact fixed-width input derivation for the internal contract-word call. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver.InputData

@[simp] theorem ofWord_bytes (word : Core.Word) :
    (ofWord word).bytes = encodeWordBytesBE word :=
  rfl

@[simp] theorem ofWord_sizeWord_val (word : Core.Word) :
    (ofWord word).sizeWord.val = 32 := by
  simp [ofWord]

@[simp] theorem ofWord_wordBE?_zero (word : Core.Word) :
    (ofWord word).wordBE? Core.Word.zero = some word := by
  rw [wordBE?_eq_some_iff]
  constructor
  · simp [Core.Word.zero, ofWord]
  · change (encodeWordBytesBE word).extract 0 32 = encodeWordBytesBE word
    rw [← encodeWordBytesBE_size word]
    exact ByteArray.extract_zero_size

end Solcore.ContractRuntime.HostStorageDriver.InputData
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageExecutionInputs
/-! Immutable inputs shared by one combined handled storage execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageExecutionInputsProperties`
-/

/-! Exact projections of immutable combined-storage execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

@[simp] theorem ExecutionInputs.mk_codeAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).codeAddress =
      codeAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_callValue
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).callValue =
      callValue :=
  rfl

@[simp] theorem ExecutionInputs.mk_callerAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).callerAddress =
      callerAddress :=
  rfl

@[simp] theorem ExecutionInputs.mk_inputData
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).inputData =
      inputData :=
  rfl

@[simp] theorem ExecutionInputs.mk_currentAddress
    (codeAddress : Address) (callValue : Core.Word) (callerAddress : Address)
    (inputData : InputData) (currentAddress : Address) :
    (ExecutionInputs.mk codeAddress callValue callerAddress inputData
      currentAddress).currentAddress = currentAddress :=
  rfl

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageContext
/-! Mutable context threaded by handled storage execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageContextRebase`
-/

/-! Proof-preserving replacement of one storage context's working world. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver.Context

universe u v

@[simp] theorem rebaseWorking_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem rebaseWorking_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

@[simp] theorem rebaseWorking_workingWorld
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.working.1 =
      world :=
  rfl

@[simp] theorem rebaseWorking_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState) (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorking world account present).context.values.working.2 =
      context.context.values.working.2 :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.storageAddress =
      context.context.storageAddress :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.checkpoint =
      context.context.values.checkpoint :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_workingWorld
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.working.1 =
      world :=
  rfl

@[simp] theorem rebaseWorkingWithEffects_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (world : WorldState)
    (effects : FrameEffectJournal RollbackState TraceState)
    (account : Account)
    (present :
      world.account? context.context.storageAddress = some account) :
    (context.rebaseWorkingWithEffects world effects account present).context.values.working.2 =
      effects :=
  rfl

end Solcore.ContractRuntime.HostStorageDriver.Context
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageHandler
/-! Canonical host handler for storage and immutable execution inputs. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageHandlerProperties`
-/

/-! Exact request laws for the canonical storage host handler. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

@[simp] theorem handler_supports_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (topic payload : Core.Word) :
    (@handler RollbackState TraceState inputs).supports
        (.emitLogWord topic payload) = false :=
  rfl

/-- The legacy policy cannot claim that an effect-dropping log is supported. -/
theorem handler_not_supports_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (topic payload : Core.Word) :
    (@handler RollbackState TraceState inputs).supports
        (.emitLogWord topic payload) ≠ true := by
  simp

@[simp] theorem handleRequest_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    handleRequest inputs context (.storageRead slot) =
      (context, context.readStorage slot) :=
  rfl

@[simp] theorem handleSuspension_storageRead
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageRead slot, continuation, store⟩ =
      (context,
        ⟨.ret (.word (context.readStorage slot)), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    handleRequest inputs context (.storageWrite slot value) =
      (context.writeStorage slot value, ()) :=
  rfl

@[simp] theorem handleSuspension_storageWrite
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageWrite slot value, continuation, store⟩ =
      (context.writeStorage slot value,
        ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .storageAddress =
      (context, addressToWord context.context.storageAddress) :=
  rfl

@[simp] theorem handleSuspension_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.storageAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .codeAddress =
      (context, addressToWord inputs.codeAddress) :=
  rfl

@[simp] theorem handleSuspension_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.codeAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.codeAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .callValue =
      (context, inputs.callValue) :=
  rfl

@[simp] theorem handleSuspension_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.callValue, continuation, store⟩ =
      (context,
        ⟨.ret (.word inputs.callValue), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .callerAddress =
      (context, addressToWord inputs.callerAddress) :=
  rfl

@[simp] theorem handleSuspension_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.callerAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.callerAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word) :
    handleRequest inputs context (.inputDataByte? offset) =
      (context, inputs.inputData.byte? offset) :=
  rfl

@[simp] theorem handleSuspension_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        (Core.HostSuspension.mk (.inputDataByte? offset) continuation store).resume
          (inputs.inputData.byte? offset)) :=
  rfl

theorem handleSuspension_inputDataByte?_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (absent : inputs.inputData.byte? offset = none) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inLeft .word .unit), continuation, store⟩) := by
  rw [handleSuspension_inputDataByte?, absent]
  rfl

theorem handleSuspension_inputDataByte?_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset byte : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (present : inputs.inputData.byte? offset = some byte) :
    handleSuspension inputs context
        ⟨.inputDataByte? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩) := by
  rw [handleSuspension_inputDataByte?, present]
  rfl

@[simp] theorem handleRequest_inputDataSize
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .inputDataSize =
      (context, inputs.inputData.sizeWord) :=
  rfl

@[simp] theorem handleSuspension_inputDataSize
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.inputDataSize, continuation, store⟩ =
      (context,
        ⟨.ret (.word inputs.inputData.sizeWord), continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_inputDataWordBE?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word) :
    handleRequest inputs context (.inputDataWordBE? offset) =
      (context, inputs.inputData.wordBE? offset) :=
  rfl

@[simp] theorem handleSuspension_inputDataWordBE?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.inputDataWordBE? offset, continuation, store⟩ =
      (context,
        (Core.HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
          (inputs.inputData.wordBE? offset)) :=
  rfl

theorem handleSuspension_inputDataWordBE?_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (absent : inputs.inputData.wordBE? offset = none) :
    handleSuspension inputs context
        ⟨.inputDataWordBE? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inLeft .word .unit), continuation, store⟩) := by
  rw [handleSuspension_inputDataWordBE?, absent]
  rfl

theorem handleSuspension_inputDataWordBE?_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset word : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (present : inputs.inputData.wordBE? offset = some word) :
    handleSuspension inputs context
        ⟨.inputDataWordBE? offset, continuation, store⟩ =
      (context,
        ⟨.ret (.inRight .unit (.word word)), continuation, store⟩) := by
  rw [handleSuspension_inputDataWordBE?, present]
  rfl

@[simp] theorem handleRequest_currentAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    handleRequest inputs context .currentAddress =
      (context, addressToWord inputs.currentAddress) :=
  rfl

@[simp] theorem handleSuspension_currentAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.currentAddress, continuation, store⟩ =
      (context,
        ⟨.ret (.word (addressToWord inputs.currentAddress)),
          continuation, store⟩) :=
  rfl

@[simp] theorem handleRequest_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (topic payload : Core.Word) :
    handleRequest inputs context (.emitLogWord topic payload) =
      (context, ()) :=
  rfl

@[simp] theorem handleSuspension_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store) :
    handleSuspension inputs context
        ⟨.emitLogWord topic payload, continuation, store⟩ =
      (context, ⟨.ret .unit, continuation, store⟩) :=
  rfl

@[simp] theorem handleSuspension_storageRead_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageRead slot, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageRead]

@[simp] theorem handleSuspension_storageWrite_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).1 =
        context.writeStorage slot value := by
  rw [handleSuspension_storageWrite]

@[simp] theorem handleSuspension_storageWrite_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.control =
        .ret .unit := by
  rw [handleSuspension_storageWrite]

@[simp] theorem handleSuspension_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension inputs context suspension).2.continuation =
      suspension.continuation := by
  simp [handleSuspension, HostHandler.handleSuspension]

@[simp] theorem handleSuspension_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension) :
    (handleSuspension inputs context suspension).2.store =
      suspension.store := by
  simp [handleSuspension, HostHandler.handleSuspension]

@[simp] theorem handleSuspension_storageWrite_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_storageWrite_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) (continuation : List Core.Frame)
    (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageWrite slot value, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_storageAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_storageAddress]

@[simp] theorem handleSuspension_storageAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord context.context.storageAddress)) := by
  rw [handleSuspension_storageAddress]

@[simp] theorem handleSuspension_storageAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_storageAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.storageAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_codeAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_codeAddress]

@[simp] theorem handleSuspension_codeAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.codeAddress)) := by
  rw [handleSuspension_codeAddress]

@[simp] theorem handleSuspension_codeAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_codeAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.codeAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_callValue_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).1 = context := by
  rw [handleSuspension_callValue]

@[simp] theorem handleSuspension_callValue_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.control =
        .ret (.word inputs.callValue) := by
  rw [handleSuspension_callValue]

@[simp] theorem handleSuspension_callValue_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_callValue_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callValue, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_callerAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_callerAddress]

@[simp] theorem handleSuspension_callerAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.callerAddress)) := by
  rw [handleSuspension_callerAddress]

@[simp] theorem handleSuspension_callerAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_callerAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.callerAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_inputDataByte?_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).1 = context := by
  rw [handleSuspension_inputDataByte?]

theorem handleSuspension_inputDataByte?_context_independent
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.inputDataByte? offset, continuation, store⟩).1 =
      (handleSuspension rightInputs context
        ⟨.inputDataByte? offset, continuation, store⟩).1 := by
  simp

@[simp] theorem handleSuspension_inputDataByte?_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
  (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret ((Core.HostRequest.inputDataByte? offset).responseValue
          (inputs.inputData.byte? offset)) := by
  rw [handleSuspension_inputDataByte?]
  rfl

theorem handleSuspension_inputDataByte?_control_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (absent : inputs.inputData.byte? offset = none) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret (.inLeft .word .unit) := by
  rw [handleSuspension_inputDataByte?_none inputs context offset continuation store
    absent]

theorem handleSuspension_inputDataByte?_control_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset byte : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (present : inputs.inputData.byte? offset = some byte) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.control =
        .ret (.inRight .unit (.word byte)) := by
  rw [handleSuspension_inputDataByte?_some inputs context offset byte continuation
    store present]

@[simp] theorem handleSuspension_inputDataByte?_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_inputDataByte?_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataByte? offset, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_inputDataSize_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataSize, continuation, store⟩).1 = context := by
  rw [handleSuspension_inputDataSize]

theorem handleSuspension_inputDataSize_context_independent
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.inputDataSize, continuation, store⟩).1 =
      (handleSuspension rightInputs context
        ⟨.inputDataSize, continuation, store⟩).1 := by
  simp

@[simp] theorem handleSuspension_inputDataSize_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataSize, continuation, store⟩).2.control =
        .ret (.word inputs.inputData.sizeWord) := by
  rw [handleSuspension_inputDataSize]

@[simp] theorem handleSuspension_inputDataSize_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataSize, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_inputDataSize_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataSize, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_inputDataWordBE?_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).1 = context := by
  rw [handleSuspension_inputDataWordBE?]

theorem handleSuspension_inputDataWordBE?_context_independent
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.inputDataWordBE? offset, continuation, store⟩).1 =
      (handleSuspension rightInputs context
        ⟨.inputDataWordBE? offset, continuation, store⟩).1 := by
  simp

@[simp] theorem handleSuspension_inputDataWordBE?_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).2.control =
        .ret ((Core.HostRequest.inputDataWordBE? offset).responseValue
          (inputs.inputData.wordBE? offset)) := by
  rw [handleSuspension_inputDataWordBE?]
  rfl

theorem handleSuspension_inputDataWordBE?_control_none
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (absent : inputs.inputData.wordBE? offset = none) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).2.control =
        .ret (.inLeft .word .unit) := by
  rw [handleSuspension_inputDataWordBE?_none inputs context offset continuation
    store absent]

theorem handleSuspension_inputDataWordBE?_control_some
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset word : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store)
    (present : inputs.inputData.wordBE? offset = some word) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).2.control =
        .ret (.inRight .unit (.word word)) := by
  rw [handleSuspension_inputDataWordBE?_some inputs context offset word
    continuation store present]

@[simp] theorem handleSuspension_inputDataWordBE?_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_inputDataWordBE?_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (offset : Core.Word)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.inputDataWordBE? offset, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem handleSuspension_currentAddress_context
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).1 = context := by
  rw [handleSuspension_currentAddress]

theorem handleSuspension_currentAddress_context_independent
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.currentAddress, continuation, store⟩).1 =
      (handleSuspension rightInputs context
        ⟨.currentAddress, continuation, store⟩).1 := by
  simp

@[simp] theorem handleSuspension_currentAddress_control
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.control =
        .ret (.word (addressToWord inputs.currentAddress)) := by
  rw [handleSuspension_currentAddress]

theorem handleSuspension_currentAddress_control_eq_iff
    {RollbackState : Type u} {TraceState : Type v}
    (leftInputs rightInputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension leftInputs context
        ⟨.currentAddress, continuation, store⟩).2.control =
      (handleSuspension rightInputs context
        ⟨.currentAddress, continuation, store⟩).2.control ↔
      leftInputs.currentAddress = rightInputs.currentAddress := by
  simp only [handleSuspension_currentAddress_control]
  constructor
  · intro equal
    injection equal with valueEqual
    injection valueEqual with wordEqual
    exact addressToWord_injective wordEqual
  · intro equal
    rw [equal]

@[simp] theorem handleSuspension_currentAddress_continuation
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.continuation =
        continuation := by
  exact handleSuspension_continuation inputs context _

@[simp] theorem handleSuspension_currentAddress_store
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (continuation : List Core.Frame) (store : Core.Store) :
    (handleSuspension inputs context
      ⟨.currentAddress, continuation, store⟩).2.store = store := by
  exact handleSuspension_store inputs context _

@[simp] theorem wordToAddress?_handler_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress?
        ((handler inputs).handle context .storageAddress).2 =
      some context.context.storageAddress := by
  change wordToAddress? (addressToWord context.context.storageAddress) = _
  exact wordToAddress?_addressToWord context.context.storageAddress

@[simp] theorem wordToAddress?_handler_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler inputs).handle context .codeAddress).2 =
      some inputs.codeAddress := by
  change wordToAddress? (addressToWord inputs.codeAddress) = _
  exact wordToAddress?_addressToWord inputs.codeAddress

@[simp] theorem wordToAddress?_handler_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler inputs).handle context .callerAddress).2 =
      some inputs.callerAddress := by
  change wordToAddress? (addressToWord inputs.callerAddress) = _
  exact wordToAddress?_addressToWord inputs.callerAddress

@[simp] theorem wordToAddress?_handler_currentAddress
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState) :
    wordToAddress? ((handler inputs).handle context .currentAddress).2 =
      some inputs.currentAddress := by
  change wordToAddress? (addressToWord inputs.currentAddress) = _
  exact wordToAddress?_addressToWord inputs.currentAddress

@[simp] theorem handler_storageWrite_readStorage_same
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot value : Core.Word) :
    (((handler inputs).handle context
      (.storageWrite slot value)).1).readStorage slot = value := by
  change (context.writeStorage slot value).readStorage slot = value
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.readStorage_writeStorage_same
      context slot value

@[simp] theorem handler_storageWrite_zero_storageValue?
    {RollbackState : Type u} {TraceState : Type v}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (slot : Core.Word) :
    (((handler inputs).handle context
      (.storageWrite slot Core.Word.zero)).1).storageAccount.storageValue?
        slot = none := by
  change
    (context.writeStorage slot Core.Word.zero).storageAccount.storageValue?
      slot = none
  exact
    FrameCheckpointedWorkingPairWithPresentStorageAccount.storageValue?_writeStorage_zero
      context slot

theorem handleSuspension_state_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (inputs : ExecutionInputs)
    (context : Context RollbackState TraceState)
    (suspension : Core.HostSuspension)
    (typing : Core.HostSuspensionHasType suspension resultType definitions) :
    Core.HostStateHasType
      (handleSuspension inputs context suspension).2
      resultType definitions := by
  simpa only [handleSuspension] using
    HostHandler.handleSuspension_state_hasType
      (handler inputs) context suspension typing

end Solcore.ContractRuntime.HostStorageDriver
end

section
-- leanmerge: from Solcore.ContractRuntime.HostStorageDriver
/-! Canonical driver for storage-backed host execution. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverProperties`
-/

/-! Execution and preservation laws for the canonical storage host driver. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostStorageDriver

universe u v

@[simp] theorem run_of_done
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (value : Core.Value)
    (store : Core.Store)
    (execution : Core.hostRun fuel state = .done value store) :
    run context inputs fuel state =
      ⟨context, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_of_done
      (@handler RollbackState TraceState inputs)
      context fuel state value store execution

@[simp] theorem run_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state exhausted : Core.State)
    (execution : Core.hostRun fuel state = .outOfFuel exhausted) :
    run context inputs fuel state =
      ⟨context, .outOfFuel exhausted⟩ := by
  simpa only [run] using
    HostDriver.run_of_outOfFuel
      (@handler RollbackState TraceState inputs)
      context fuel state exhausted execution

@[simp] theorem run_of_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (execution : Core.hostRun fuel state = .fault error faultState) :
    run context inputs fuel state =
      ⟨context, .fault error faultState⟩ := by
  simpa only [run] using
    HostDriver.run_of_fault
      (@handler RollbackState TraceState inputs)
      context fuel state faultState error execution

/-- Every suspension resumes under the same immutable input. -/
theorem run_of_suspended
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (suspension : Core.HostSuspension)
    (execution :
      Core.hostRun fuel state = .suspended suspension remainingFuel) :
    run context inputs fuel state =
      if (@handler RollbackState TraceState inputs).supports
          suspension.request then
        run
          (handleSuspension inputs context suspension).1 inputs
          remainingFuel
          (handleSuspension inputs context suspension).2
      else
        ⟨context, .unsupported suspension remainingFuel⟩ := by
  simpa only [run, handleSuspension] using
    HostDriver.run_of_suspended
      (@handler RollbackState TraceState inputs)
      context fuel remainingFuel state suspension execution

theorem run_of_suspended_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.storageAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord context.context.storageAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.storageAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.storageAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspension_storageAddress]

theorem run_of_suspended_codeAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.codeAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.codeAddress)), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.codeAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.codeAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _
        execution
    _ = _ := by rw [handleSuspension_codeAddress]

theorem run_of_suspended_callValue
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.callValue, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word inputs.callValue), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.callValue, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.callValue, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_callValue]

theorem run_of_suspended_callerAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.callerAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.callerAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.callerAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.callerAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_callerAddress]

theorem run_of_suspended_currentAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.currentAddress, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word (addressToWord inputs.currentAddress)),
          continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.currentAddress, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.currentAddress, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_currentAddress]

theorem run_of_suspended_inputDataByte?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ((Core.HostSuspension.mk (.inputDataByte? offset) continuation store).resume
          (inputs.inputData.byte? offset)) := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataByte? offset, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataByte? offset, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataByte?]

theorem run_of_suspended_inputDataByte?_none
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel)
    (absent : inputs.inputData.byte? offset = none) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inLeft .word .unit), continuation, store⟩ := by
  rw [run_of_suspended_inputDataByte? context inputs fuel remainingFuel state
    offset continuation store execution, absent]
  rfl

theorem run_of_suspended_inputDataByte?_some
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset byte : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataByte? offset, continuation, store⟩ remainingFuel)
    (present : inputs.inputData.byte? offset = some byte) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩ := by
  rw [run_of_suspended_inputDataByte? context inputs fuel remainingFuel state
    offset continuation store execution, present]
  rfl

theorem run_of_suspended_inputDataSize
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataSize, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.word inputs.inputData.sizeWord), continuation, store⟩ := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataSize, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataSize, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataSize]

theorem run_of_suspended_inputDataWordBE?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ((Core.HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
          (inputs.inputData.wordBE? offset)) := by
  calc
    run context inputs fuel state =
        run
          (handleSuspension inputs context
            ⟨.inputDataWordBE? offset, continuation, store⟩).1
          inputs remainingFuel
          (handleSuspension inputs context
            ⟨.inputDataWordBE? offset, continuation, store⟩).2 :=
      run_of_suspended context inputs fuel remainingFuel state _ execution
    _ = _ := by rw [handleSuspension_inputDataWordBE?]

theorem run_of_suspended_inputDataWordBE?_none
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel)
    (absent : inputs.inputData.wordBE? offset = none) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inLeft .word .unit), continuation, store⟩ := by
  rw [run_of_suspended_inputDataWordBE? context inputs fuel remainingFuel state
    offset continuation store execution, absent]
  rfl

theorem run_of_suspended_inputDataWordBE?_some
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (offset word : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ remainingFuel)
    (present : inputs.inputData.wordBE? offset = some word) :
    run context inputs fuel state =
      run context inputs remainingFuel
        ⟨.ret (.inRight .unit (.word word)), continuation, store⟩ := by
  rw [run_of_suspended_inputDataWordBE? context inputs fuel remainingFuel state
    offset continuation store execution, present]
  rfl

theorem run_of_suspended_emitLogWord
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel remainingFuel : Nat)
    (state : Core.State)
    (topic payload : Core.Word)
    (continuation : List Core.Frame)
    (store : Core.Store)
    (execution :
      Core.hostRun fuel state =
        .suspended
          ⟨.emitLogWord topic payload, continuation, store⟩ remainingFuel) :
    run context inputs fuel state =
      ⟨context,
        .unsupported
          ⟨.emitLogWord topic payload, continuation, store⟩
          remainingFuel⟩ := by
  simpa [run, handler] using
    HostDriver.run_of_unsupported (handler inputs) context fuel remainingFuel
      state ⟨.emitLogWord topic payload, continuation, store⟩ execution rfl

@[simp] theorem run_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.storageAddress =
      context.context.storageAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.storageAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_checkpoint
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.checkpoint =
      context.context.values.checkpoint := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.values.checkpoint)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingEffects
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    (run context inputs fuel state).context.context.values.working.2 =
      context.context.values.working.2 := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current => current.context.values.working.2)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingCode?
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (run context inputs fuel state).context.context.values.working.1.code?
        observedAddress =
      context.context.values.working.1.code? observedAddress := by
  simpa only [run] using
    HostDriver.run_observe
      (@handler RollbackState TraceState inputs)
      (fun current =>
        current.context.values.working.1.code? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest])
      context fuel state

@[simp] theorem run_workingAccount?_of_ne_storageAddress
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address)
    (different : observedAddress ≠ context.context.storageAddress) :
    (run context inputs fuel state).context.context.values.working.1.account?
        observedAddress =
      context.context.values.working.1.account? observedAddress := by
  have preserved :
      (if observedAddress =
          (run context inputs fuel state).context.context.storageAddress
        then none
        else
          (run context inputs fuel state).context.context.values.working.1.account?
            observedAddress) =
      (if observedAddress = context.context.storageAddress
        then none
        else context.context.values.working.1.account? observedAddress) := by
    exact
      HostDriver.run_observe
        (@handler RollbackState TraceState inputs)
        (fun current =>
          if observedAddress = current.context.storageAddress
            then none
            else current.context.values.working.1.account? observedAddress)
        (by
          intro current request
          cases request with
          | storageRead slot =>
              simp [handler, handleRequest] <;> rfl
          | storageWrite slot value =>
              by_cases same :
                  observedAddress = current.context.storageAddress
              · simp [handler, handleRequest, same]
              · simp [handler, handleRequest, same]
          | storageAddress =>
              simp [handler, handleRequest] <;> rfl
          | codeAddress =>
              simp [handler, handleRequest] <;> rfl
          | callValue =>
              simp [handler, handleRequest] <;> rfl
          | callerAddress =>
              simp [handler, handleRequest] <;> rfl
          | currentAddress =>
              simp [handler, handleRequest] <;> rfl
          | inputDataByte? offset =>
              simp [handler, handleRequest] <;> rfl
          | inputDataSize =>
              simp [handler, handleRequest] <;> rfl
          | inputDataWordBE? offset =>
              simp [handler, handleRequest] <;> rfl
          | callContractWord target input =>
              simp [handler, handleRequest] <;> rfl
          | callContractWordWithValue target value input =>
              simp [handler, handleRequest] <;> rfl
          | createContractWord templateId value input =>
              simp [handler, handleRequest] <;> rfl
          | emitLogWord topic payload =>
              simp [handler, handleRequest] <;> rfl)
        context fuel state
  simpa only [run_storageAddress, if_neg different] using preserved

end Solcore.ContractRuntime.HostStorageDriver

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverSafetyProperties`
-/

/-! Type and fault safety for the canonical storage host driver. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

theorem run_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome.HasType
      resultType definitions := by
  simpa only [run] using
    HostDriver.run_hasType
      (@handler RollbackState TraceState inputs)
      context fuel state stateTyping

theorem run_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment} {resultType : Core.Ty}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state faultState : Core.State)
    (error : Core.MachineFault)
    (stateTyping : Core.HostStateHasType state resultType definitions) :
    (run context inputs fuel state).outcome ≠
      .fault error faultState := by
  simpa only [run] using
    HostDriver.run_ne_fault
      (@handler RollbackState TraceState inputs)
      context fuel state faultState error stateTyping

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    (code.runWithStorage context inputs fuel).outcome.HasType
      code.program.resultType code.program.dataDefinitions := by
  exact HostStorageDriver.run_hasType
    context inputs fuel _ code.initialState_hasType

theorem runWithStorage_ne_fault
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (error : Core.MachineFault)
    (faultState : Core.State) :
    (code.runWithStorage context inputs fuel).outcome ≠
      .fault error faultState := by
  exact HostStorageDriver.run_ne_fault
    context inputs fuel _ faultState error code.initialState_hasType

theorem runWithStorage_done_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .done value store) :
    ∃ world,
      Core.HostStoreHasTypes world store code.program.dataDefinitions ∧
        Core.HostRuntimeValueHasType world value code.program.resultType
          code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

theorem runWithStorage_outOfFuel_hasType
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel : Nat} {state : Core.State}
    (result :
      (code.runWithStorage context inputs fuel).outcome =
        .outOfFuel state) :
    Core.HostStateHasType state code.program.resultType
      code.program.dataDefinitions := by
  have typing := code.runWithStorage_hasType context inputs fuel
  rw [result] at typing
  exact typing

end CheckedHostCoreProgram

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.HostStorageDriverFuelProperties`
-/

/-! Whole-run fuel accounting indexed by immutable execution inputs. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v

namespace HostStorageDriver

namespace FuelSound

/-- Prefix a sound suffix with one request handled under the same input. -/
theorem prependRequest
    {RollbackState : Type u} {TraceState : Type v}
    {inputs : ExecutionInputs}
    {result : HostDriverResult (Context RollbackState TraceState)}
    {fuel remainingFuel prefixSteps : Nat}
    {context nextContext : Context RollbackState TraceState}
    {start requestState resumed : Core.State}
    {suspension : Core.HostSuspension}
    (prefixPath : Core.HostSteps prefixSteps start requestState)
    (emission : Core.HostRequestEmission requestState suspension)
    (supported :
      (@handler RollbackState TraceState inputs).supports
        suspension.request = true)
    (handled :
      handleSuspension inputs context suspension =
        (nextContext, resumed))
    (accounting : prefixSteps + remainingFuel + 1 = fuel)
    (suffixSound :
      HostStorageDriver.FuelSound
        result inputs remainingFuel nextContext resumed) :
    HostStorageDriver.FuelSound
      result inputs fuel context start := by
  apply HostDriverResult.FuelSoundWith.prependRequest
    prefixPath emission supported (accounting := accounting)
  · simpa only [handleSuspension] using handled
  · exact suffixSound

end FuelSound

theorem run_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State) :
    FuelSound (run context inputs fuel state) inputs
      fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_fuelSound
      (@handler RollbackState TraceState inputs)
      context fuel state

theorem run_eq_of_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState))
    (sound : FuelSound result inputs fuel context state) :
    run context inputs fuel state = result := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_of_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result sound

theorem run_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (result : HostDriverResult (Context RollbackState TraceState)) :
    run context inputs fuel state = result ↔
      FuelSound result inputs fuel context state := by
  simpa only [run, FuelSound] using
    HostDriver.run_eq_iff_fuelSoundWith
      (@handler RollbackState TraceState inputs)
      context fuel state result

/-- Exhausted storage execution resumes under the exact same immutable input. -/
theorem run_additional_of_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context nextContext : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state exhausted : Core.State)
    (execution :
      run context inputs fuel state =
        ⟨nextContext, .outOfFuel exhausted⟩) :
    run context inputs (fuel + additional) state =
      run nextContext inputs additional exhausted := by
  simpa only [run] using
    HostDriver.run_additional_of_outOfFuel
      (@handler RollbackState TraceState inputs) execution

/-- Split storage execution agrees with one summed-budget run. -/
theorem resumeWithFuel_run
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    (fuel additional : Nat)
    (state : Core.State) :
    (run context inputs fuel state).resumeWithFuel
        (@handler RollbackState TraceState inputs) additional =
      run context inputs (fuel + additional) state := by
  simpa only [run] using
    HostDriverResult.resumeWithFuel_run
      (@handler RollbackState TraceState inputs)
      context fuel additional state

theorem run_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (context : Context RollbackState TraceState)
    (inputs : ExecutionInputs)
    {fuel largerFuel : Nat}
    (state : Core.State)
    {finalContext : Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      run context inputs fuel state =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    run context inputs largerFuel state =
      ⟨finalContext, .done value store⟩ := by
  simpa only [run] using
    HostDriver.run_done_stable
      (@handler RollbackState TraceState inputs)
      execution more

end HostStorageDriver

namespace CheckedHostCoreProgram

theorem runWithStorage_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    HostStorageDriver.FuelSound
      (code.runWithStorage context inputs fuel) inputs fuel context
      (Core.State.initial code.program.body Core.hostEnvironment) := by
  exact HostStorageDriver.run_fuelSound context inputs fuel _

theorem runWithStorage_eq_iff_fuelSound
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState)) :
    code.runWithStorage context inputs fuel = result ↔
      HostStorageDriver.FuelSound result inputs fuel context
        (Core.State.initial code.program.body Core.hostEnvironment) := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_eq_iff_fuelSound context inputs fuel
      (Core.State.initial code.program.body Core.hostEnvironment) result

theorem runWithStorage_done_stable
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    {fuel largerFuel : Nat}
    {finalContext : HostStorageDriver.Context RollbackState TraceState}
    {value : Core.Value} {store : Core.Store}
    (execution :
      code.runWithStorage context inputs fuel =
        ⟨finalContext, .done value store⟩)
    (more : fuel ≤ largerFuel) :
    code.runWithStorage context inputs largerFuel =
      ⟨finalContext, .done value store⟩ := by
  simpa only [runWithStorage] using
    HostStorageDriver.run_done_stable context inputs
      (Core.State.initial code.program.body Core.hostEnvironment)
      execution more

/-- Checked storage execution has the same exact split-fuel law. -/
theorem runWithStorage_resumeWithFuel
    {RollbackState : Type u} {TraceState : Type v}
    (code : CheckedHostCoreProgram)
    (context : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel additional : Nat) :
    (code.runWithStorage context inputs fuel).resumeWithFuel
        (@HostStorageDriver.handler RollbackState TraceState inputs)
        additional =
      code.runWithStorage context inputs (fuel + additional) := by
  simpa only [runWithStorage] using
    HostStorageDriver.resumeWithFuel_run context inputs fuel additional
      (Core.State.initial code.program.body Core.hostEnvironment)

end CheckedHostCoreProgram

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.WordReturnedFrameCompletion
/-! Successful handled Word completion and canonical returned-frame view. -/

set_option autoImplicit false

/-!
## Consolidated module: `Solcore.ContractRuntime.WordReturnedFrameCompletionProperties`
-/

/-! Exact raw, byte, frame, and resolution laws for Word completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

universe u v w

namespace HostDriverResult

@[simp] theorem toWordReturnedFrameCompletion?_done_word
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (HostDriverResult.mk context
      (.done (.word word) store)).toWordReturnedFrameCompletion? =
      some ⟨context, word, store⟩ :=
  rfl

theorem toWordReturnedFrameCompletion?_done_eq_none_iff
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (value : Core.Value) (store : Core.Store) :
    (HostDriverResult.mk context
      (.done value store)).toWordReturnedFrameCompletion? = none ↔
      ∀ word, value ≠ .word word := by
  cases value <;> simp [toWordReturnedFrameCompletion?]

@[simp] theorem toWordReturnedFrameCompletion?_outOfFuel
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (state : Core.State) :
    (HostDriverResult.mk context
      (.outOfFuel state)).toWordReturnedFrameCompletion? = none :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_fault
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (error : Core.MachineFault) (state : Core.State) :
    (HostDriverResult.mk context
      (.fault error state)).toWordReturnedFrameCompletion? = none :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_unsupported
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (suspension : Core.HostSuspension) (remainingFuel : Nat) :
    (HostDriverResult.mk context
      (.unsupported suspension remainingFuel)).toWordReturnedFrameCompletion? =
        none :=
  rfl

/-- Successful projection is exactly inverse to reconstructing the raw result. -/
theorem toWordReturnedFrameCompletion?_eq_some_iff
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    result.toWordReturnedFrameCompletion? = some completion ↔
      result = completion.toHostDriverResult := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          cases value <;> cases completion <;>
            simp [toWordReturnedFrameCompletion?,
              WordReturnedFrameCompletion.toHostDriverResult]
      | outOfFuel state =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]
      | fault error state =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]
      | unsupported suspension remainingFuel =>
          cases completion
          simp [toWordReturnedFrameCompletion?,
            WordReturnedFrameCompletion.toHostDriverResult]

end HostDriverResult

namespace WordReturnedFrameCompletion

@[simp] theorem mk_context
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).context = context :=
  rfl

@[simp] theorem mk_word
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).word = word :=
  rfl

@[simp] theorem mk_store
    {RollbackState : Type u} {TraceState : Type v}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (store : Core.Store) :
    (WordReturnedFrameCompletion.mk context word store).store = store :=
  rfl

@[simp] theorem toWordReturnedFrameCompletion?_toHostDriverResult
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    completion.toHostDriverResult.toWordReturnedFrameCompletion? =
      some completion := by
  cases completion
  rfl

@[simp] theorem returnData_size
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    completion.returnData.size = 32 := by
  exact encodeWordBytesBE_size completion.word

@[simp] theorem decodeWordBytesBE?_returnData
    {RollbackState : Type u} {TraceState : Type v}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    decodeWordBytesBE? completion.returnData = some completion.word := by
  exact decodeWordBytesBE?_encodeWordBytesBE completion.word

@[simp] theorem stateCheckpoint_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).stateCheckpoint =
      completion.context.context.values.checkpoint.state :=
  rfl

@[simp] theorem effectCheckpoint_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectCheckpoint =
      completion.context.context.values.checkpoint.effects :=
  rfl

@[simp] theorem effectWorking_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).effectWorking =
      completion.context.context.values.working.2 :=
  rfl

@[simp] theorem result_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).result =
      ⟨completion.context.context.values.working.1,
        .returned completion.returnData⟩ :=
  rfl

@[simp] theorem resolve_toFrameContinuationContext
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (completion : WordReturnedFrameCompletion RollbackState TraceState) :
    (completion.toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason).resolve =
      .returned completion.context.context.values.working.1
        completion.context.context.values.working.2 completion.returnData :=
  rfl

/-- Core-local Store is retained by the carrier but is not serialized. -/
theorem toFrameContinuationContext_store_independent
    {RollbackState : Type u} {TraceState : Type v} {TrapReason : Type w}
    (context : HostStorageDriver.Context RollbackState TraceState)
    (word : Core.Word) (leftStore rightStore : Core.Store) :
    ((⟨context, word, leftStore⟩ :
        WordReturnedFrameCompletion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) =
    ((⟨context, word, rightStore⟩ :
        WordReturnedFrameCompletion RollbackState TraceState).toFrameContinuationContext :
      FrameContinuationContext RollbackState TraceState TrapReason) :=
  rfl

end WordReturnedFrameCompletion

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.WordReturnedFrameCompletionSafetyProperties`
-/

/-! Typed branch exclusion and terminal resumption for Word completion. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.HostDriverResult

universe u v

/-- A typed Word projection fails only at exhaustion or a policy boundary. -/
theorem toWordReturnedFrameCompletion?_eq_none_iff_of_hasType
    {RollbackState : Type u} {TraceState : Type v}
    {definitions : Core.DataEnvironment}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (typing : result.outcome.HasType .word definitions) :
    result.toWordReturnedFrameCompletion? = none ↔
      (∃ context state,
        result = ⟨context, .outOfFuel state⟩) ∨
      ∃ context suspension remainingFuel,
        result = ⟨context, .unsupported suspension remainingFuel⟩ := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done value store =>
          obtain ⟨world, _storeTyping, valueTyping⟩ := typing
          obtain ⟨word, rfl⟩ := valueTyping.word_shape
          simp
      | outOfFuel state =>
          simp
      | fault error state =>
          exact False.elim typing
      | unsupported suspension remainingFuel => simp

/-- A successful projection is unchanged by any later fuel offer. -/
theorem toWordReturnedFrameCompletion?_resumeWithFuel_of_some
    {RollbackState : Type u} {TraceState : Type v}
    (result :
      HostDriverResult (HostStorageDriver.Context RollbackState TraceState))
    (handler :
      HostHandler (HostStorageDriver.Context RollbackState TraceState))
    (additional : Nat)
    (completion : WordReturnedFrameCompletion RollbackState TraceState)
    (completed :
      result.toWordReturnedFrameCompletion? = some completion) :
    toWordReturnedFrameCompletion?
        (result.resumeWithFuel handler additional) = some completion := by
  rw [(toWordReturnedFrameCompletion?_eq_some_iff
    result completion).mp completed]
  rfl

end Solcore.ContractRuntime.HostDriverResult
end
