import Solcore.Frontend.RustHull.CreationHandlerCorrespondence
import Solcore.Frontend.RustHull.CreationSemantics
import Solcore.Frontend.RustHull.CallTransportCorrespondence

/-! The actual `Creation.invoke` transport for attempts refused before init
code runs. An unaddressable init range faults before any frame cell changes.
Otherwise memory covers the init range and return data is cleared; at the
depth limit the attempt returns zero, and below it the init bytes are copied
into fresh scratch cells and the installed handler's refusal is published. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

/-- Word inputs of one creation attempt, as the lowering evaluates them. -/
structure Arguments where
  creator : Word
  depth : Word
  value : Word
  salt : Word
  create2 : Bool
  gas : Word
  offset : Word
  length : Word

def argumentValues (locations : Locations) (callback : Nat) (arguments : Arguments) : List Value :=
  [.cellRef WordMapping.type locations.memory, .cellRef .word locations.memorySize,
    .cellRef WordMapping.type locations.returnData, .cellRef .word locations.returnDataSize,
    .cellRef (OptionalCell.cellType Creation.callbackType) callback,
    .word arguments.creator, .word arguments.depth, .word arguments.value, .word arguments.salt,
    .bool arguments.create2, .word arguments.gas, .word arguments.offset, .word arguments.length]

abbrev Inputs (depth : Nat) (environment : Environment) (locations : Locations) (callback : Nat)
    (arguments : Arguments) :=
  CodeValue depth environment (fun depth => .var depth) (bundleValues (argumentValues locations callback arguments))

theorem input_part {depth : Nat} {environment : Environment} {locations : Locations} {callback : Nat}
    {arguments : Arguments} (related : Inputs depth environment locations callback arguments)
    {index : Nat} {value : Value} (found : (argumentValues locations callback arguments)[index]? = some value) :
    CodeValue depth environment (CreationImplementation.input index) value := related.part found

theorem input_initial (locations : Locations) (callback : Nat) (arguments : Arguments) (environment : Environment) :
    Inputs 0 (bundleValues (argumentValues locations callback arguments) :: environment) locations callback arguments := by
  intro extra store
  exact .var (by simp)

/-- The request built from the copied init bytes. -/
def request (arguments : Arguments) (initCode : MemorySemantics.Entries) : Request :=
  ⟨arguments.creator.bitAnd addressMask, arguments.value, arguments.salt, arguments.create2,
    arguments.depth.add (Word.ofNatModulo 1), arguments.gas, initCode, arguments.length⟩

/-- Memory covers the init range and return data is empty. -/
def cleared (state : CallTransportSemantics.State) (size : Word) : CallTransportSemantics.State :=
  ⟨{state.memory with size := size}, [], Word.zero⟩

theorem Copy.exists (sourceWords : MemorySemantics.Entries) (destination source length : Word)
    (destinationWords : MemorySemantics.Entries) :
    ∃ finalWords, MemoryCopySemantics.Copy sourceWords destination source length destinationWords finalWords := by
  by_cases zero : length = Word.zero
  · subst zero
    exact ⟨destinationWords, .empty _ _ _ _⟩
  · have positive : 0 < length.val := by
      rcases Nat.eq_zero_or_pos length.val with same | positive
      · exact False.elim (zero (Fin.ext same))
      · exact positive
    have bounded : MemoryCopySemantics.width length ≤ length.val := by
      unfold MemoryCopySemantics.width
      split
      · rename_i large
        change 31 % wordModulus < length.val at large
        rw [Nat.mod_eq_of_lt (by decide)] at large
        omega
      · omega
    have widthSmall : MemoryCopySemantics.width length < wordModulus := by
      unfold MemoryCopySemantics.width; split <;> decide
    have value : (Word.ofNatModulo (MemoryCopySemantics.width length)).val = MemoryCopySemantics.width length :=
      Nat.mod_eq_of_lt widthSmall
    have widthPositive : 0 < MemoryCopySemantics.width length := by
      unfold MemoryCopySemantics.width; split <;> omega
    have smaller : (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length))).val < length.val := by
      have subtracted : (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length))).val =
          length.val - MemoryCopySemantics.width length := by
        simp only [Word.sub]
        rw [Fin.sub_val_of_le (by rw [Fin.le_def, value]; exact bounded), value]
      omega
    obtain ⟨finalWords, rest⟩ := Copy.exists
      (MemoryCopySemantics.remainingSource sourceWords source length)
      (destination.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (source.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length)))
      (MemoryCopySemantics.written destinationWords destination length
        (MemoryCopySemantics.copiedWord sourceWords source length))
    exact ⟨finalWords, .step zero rest⟩
termination_by length.val

private theorem clear_evaluates {depth : Nat} {environment : Environment} {store final : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    {target : Value} {body : Code}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (continued : Evaluates ([Value.unit, .unit] ++ environment)
      (publishStore locations store [] Word.zero) (body (depth + 2)) target final) :
    Evaluates environment store
      (bind (CodeBuilder.store (CreationImplementation.input 2) CodeBuilder.empty) (fun _ =>
        bind (CodeBuilder.store (CreationImplementation.input 3) (number 0)) (fun _ => body)) depth) target final := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell ((input_part inputs (index := 2) rfl).evaluates store) related.logs (.construct .unit) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell ((input_part (inputs.prepend [.unit]) (index := 3) rfl).evaluates writtenData)
        sizeFound .word sizeWritten
    · exact continued

/-- The dispatch prefix copies the init bytes into two fresh scratch cells; the
caller's cells are retained. -/
private theorem snapshot_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize) :
    ∃ extra copiedStore initCode input,
      extra.length = 4 ∧ StoreRetains store copiedStore ∧
      Inputs (depth + 4) (extra ++ environment) locations callback arguments ∧
      CodeValue (depth + 4) (extra ++ environment) initCode (.cellRef WordMapping.type store.length) ∧
      copiedStore.read? store.length = some (WordMapping.encode input) ∧
      ∀ target final,
        Evaluates (extra ++ environment) copiedStore
          ((bindResult .word (fun depth => OptionalCell.read Creation.callbackType
              (CreationImplementation.input 4 depth) Creation.unavailableReason) fun function =>
            bindResult .word (apply function (CreationImplementation.request initCode))
              CreationImplementation.finish) (depth + 4)) target final →
        Evaluates environment store (CreationImplementation.dispatch depth) target final := by
  let snapshot := WordMapping.encode state.memory.words
  let inputRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word Word.zero]
  let inputCode : Code := fun here => .var (here - (depth + 1) - 1)
  have snapshotRelated := CodeValue.bound depth environment snapshot
  have inputRelated := CodeValue.bound (depth + 1) (snapshot :: environment) inputRef
  have sizeRelated := CodeValue.bound (depth + 2) (inputRef :: snapshot :: environment) sizeRef
  have scratchRelated : MemoryCorrespondence.StateRel store.length (store.length + 1) {} allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let extraInput : Environment := [sizeRef, inputRef, snapshot]
  obtain ⟨size, touched⟩ : ∃ size,
      MemorySemantics.touchSize? ({} : MemorySemantics.State).size Word.zero arguments.length = some size := by
    change ∃ size, MemorySemantics.touchSize? Word.zero Word.zero arguments.length = some size
    unfold MemorySemantics.touchSize?
    by_cases zero : arguments.length = Word.zero
    · simp [zero]
    · have sum : Word.zero.add arguments.length = arguments.length := by
        apply Fin.ext
        show (0 + arguments.length.val) % wordModulus = arguments.length.val
        rw [Nat.zero_add, Nat.mod_eq_of_lt arguments.length.isLt]
      have notWrapped : ¬Word.zero > arguments.length := fun wrapped => Nat.not_lt_zero _ wrapped
      have notLarge : ¬arguments.length > Word.ofNatModulo (wordModulus - 32) := by
        intro large
        change (Word.ofNatModulo (wordModulus - 32)).val < arguments.length.val at large
        have limit : (Word.ofNatModulo (wordModulus - 32)).val = wordModulus - 32 :=
          Nat.mod_eq_of_lt (by decide)
        have small : (49152 : Nat) < wordModulus - 32 := by decide
        simp only [CreationSemantics.maxInitCodeSize] at bounded
        omega
      simp only [beq_iff_eq, zero, ↓reduceIte, sum, notWrapped, notLarge]
      exact ⟨_, rfl⟩
  obtain ⟨words, copiedWords⟩ := Copy.exists state.memory.words Word.zero arguments.offset arguments.length []
  have copied : MemoryCopySemantics.From state.memory.words Word.zero arguments.offset arguments.length
      {} (.value .unit) ⟨words, size⟩ := .done touched copiedWords
  obtain ⟨target, copiedStore, resultRelated, evaluated, inputMemory, frame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves copied scratchRelated
      ((inputRelated.prepend [sizeRef]).evaluates allocated) (sizeRelated.evaluates allocated) .word
      ((snapshotRelated.prepend [sizeRef, inputRef]).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 11) rfl).evaluates allocated)
      ((input_part (inputs.prepend extraInput) (index := 12) rfl).evaluates allocated)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      have retained : StoreRetains store copiedStore := by
        constructor
        · have length := frame.length
          simp only [allocated, List.length_append, List.length_cons, List.length_nil] at length
          omega
        · intro location bounded
          have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
          have after : copiedStore.read? location = some store[location] :=
            frame.read location _ (by omega) (by omega)
              (by simpa only [allocated, Store.read?, List.getElem?_append_left bounded] using found)
          exact after.trans found.symm
      refine ⟨.unit :: extraInput, copiedStore, inputCode, words, rfl, retained, inputs.prepend (.unit :: extraInput),
        inputRelated.prepend [.unit, sizeRef], inputMemory.memory, ?_⟩
      intro target final completed
      unfold CreationImplementation.dispatch CodeBuilder.bind
      apply Evaluates.letE (.loadCell ((input_part inputs (index := 0) rfl).evaluates store) related.memory)
      apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
      · exact .newCell (.construct .unit)
      · apply Evaluates.letE (bodyStore := allocated)
        · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
            List.cons_append, List.nil_append, inputRef, snapshot, resources, CodeBuilder.allocate, CodeBuilder.number,
            CodeBuilder.constant, show Word.ofNatModulo 0 = Word.zero from rfl] using
            (Evaluates.newCell (elementType := .word) (environment := inputRef :: snapshot :: environment)
              (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word Word.zero))
        · exact LanguageResult.bind_success .word evaluated completed

/-- The payload of the refused handler response. -/
def refusedPayload : Value := bundleValues [.word Word.zero, WordMapping.encode [], .word Word.zero]

private theorem finish_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {locations : Locations} {callback : Nat} {arguments : Arguments} {state : CallTransportSemantics.State}
    (inputs : Inputs depth environment locations callback arguments)
    (related : StateRel locations state store) :
    Evaluates (refusedPayload :: environment) store
      (CreationImplementation.finish (fun here => .var (here - depth - 1)) (depth + 1))
      (.inRight .word (.word Word.zero)) (publishStore locations store [] Word.zero) := by
  let writtenData : Store := store.set locations.returnData (WordMapping.encode [])
  have distinct := related.distinct
  simp [Locations.resources, LogsCorrespondence.Locations.all] at distinct
  have dataWritten : store.write? locations.returnData (WordMapping.encode []) = some writtenData :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp related.logs).1, rfl⟩
  have sizeFound : writtenData.read? locations.returnDataSize = some (.word state.returnDataSize) := by
    rw [Store.write?_preserves_other dataWritten (by intro same; simp_all)]
    exact related.logSize
  have sizeWritten : writtenData.write? locations.returnDataSize (.word Word.zero) =
      some (publishStore locations store [] Word.zero) :=
    Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp sizeFound).1, rfl⟩
  have payloadCode := CodeValue.bound depth environment refusedPayload
  unfold CreationImplementation.finish CodeBuilder.bind
  apply Evaluates.letE (bodyStore := writtenData)
  · exact .storeCell (((input_part inputs (index := 2) rfl).prepend [refusedPayload]).evaluates store)
      related.logs ((payloadCode.part (index := 1) rfl).evaluates store) dataWritten
  · apply Evaluates.letE (bodyStore := publishStore locations store [] Word.zero)
    · exact .storeCell (((input_part inputs (index := 3) rfl).prepend [.unit, refusedPayload]).evaluates writtenData)
        sizeFound (((payloadCode.part (index := 2) rfl).prepend [.unit]).evaluates writtenData) sizeWritten
    · exact .inRight (((payloadCode.part (index := 0) rfl).prepend [.unit, .unit]).evaluates _)

theorem invoke_overflow {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store)
    (invalid : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = none) :
    Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inLeft .word (.word Memory.overflowReason)) store := by
  rw [CreationImplementation.invoke_eq]
  apply Evaluates.letE packed
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
  exact LanguageResult.bind_failure .word touched

theorem invoke_depth {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (exceeded : arguments.depth > Word.ofNatModulo 1023) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inRight .word (.word Word.zero)) final ∧
      StateRel locations (cleared state size) final ∧ Frame locations store final := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  have clearedRelated : StateRel locations (cleared state size)
      (publishStore locations inputStore [] Word.zero) := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  refine ⟨publishStore locations inputStore [] Word.zero, .letE packed ?_, clearedRelated,
    inputFrame.trans clearFrame⟩
  apply LanguageResult.bind_success .word touched
  apply clear_evaluates (inputs.prepend [.unit]) inputRelated
  exact .ifTrue (.binary ((input_part (inputs.prepend [.unit, .unit, .unit]) (index := 6) rfl).evaluates _) .word
    (by simp [BinaryOp.apply, Creation.depthLimit, exceeded])) (.inRight .word)

/-- Below the depth limit the actual dispatch copies the init bytes and
publishes the handler's refusal: return data stays empty and the result is
zero. The handler and the shared state are those of the creating frame. -/
theorem invoke_refused {locations : Locations} {callback : Nat} {arguments : Arguments}
    {state : CallTransportSemantics.State} {environment : Environment} {initial store : Store}
    {memoryReference sizeReference returnDataReference returnSizeReference callbackReference
      creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length : Core.Expr}
    {sharedLocations : AccountCallCorrespondence.SharedLocations} {shared : AccountCallSemantics.Shared}
    {function : Value}
    (packed : Evaluates environment initial
      (bundle [memoryReference, sizeReference, returnDataReference, returnSizeReference,
        callbackReference, creatorAddress, depth, transferredValue, saltValue, isCreate2,
        suppliedGas, offset, length])
      (bundleValues (argumentValues locations callback arguments)) store)
    (related : StateRel locations state store) {size : Word}
    (touchedSize : MemorySemantics.touchSize? state.memory.size arguments.offset arguments.length = some size)
    (allowed : ¬arguments.depth > Word.ofNatModulo 1023)
    (bounded : arguments.length.val ≤ CreationSemantics.maxInitCodeSize)
    (callbackRead : store.read? callback = some (.inRight .unit function))
    (callbackOutside : callback ∉ locations.resources.all)
    (handler : HandlerClosure sharedLocations function)
    (sharedRelated : AccountCallCorrespondence.SharedStateRel sharedLocations shared store)
    (separate : ∀ location ∈ sharedLocations.all, location ∉ locations.resources.all)
    (refusing : ∀ initCode, Refusing shared (request arguments initCode)) :
    ∃ final, Evaluates environment initial
      (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference callbackReference
        creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length)
      (.inRight .word (.word Word.zero)) final ∧
      StateRel locations (cleared state size) final ∧ Frame locations store final := by
  rw [CreationImplementation.invoke_eq]
  have inputs := input_initial locations callback arguments environment
  have touched := MemoryCorrespondence.touch_evaluates (size := state.memory.size)
    ((input_part inputs (index := 1) rfl).evaluates store)
    ((input_part inputs (index := 11) rfl).evaluates store)
    ((input_part inputs (index := 12) rfl).evaluates store) related.memorySize
  simp only [MemoryCorrespondence.touchResult, touchedSize] at touched
  let inputStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size
    arguments.offset arguments.length
  have inputRelated : StateRel locations {state with memory := {state.memory with size := size}} inputStore :=
    related.touch touchedSize
  have inputFrame := LogsCorrespondence.Frame.touch locations.resources store state.memory.size
    arguments.offset arguments.length
  let clearedStore := publishStore locations inputStore [] Word.zero
  have clearedRelated : StateRel locations (cleared state size) clearedStore := published inputRelated [] Word.zero
  have clearFrame := LogsCorrespondence.Frame.publish locations.resources inputStore [] Word.zero
  have framed := inputFrame.trans clearFrame
  have dispatchInputs := inputs.prepend [.unit, .unit, .unit]
  obtain ⟨extra, copiedStore, initCode, input, extraLength, retained, inputs', initRelated, initRead, entered⟩ :=
    snapshot_evaluates dispatchInputs clearedRelated bounded
  have keep {location : Nat} {value : Value} (outside : location ∉ locations.resources.all)
      (found : store.read? location = some value) : copiedStore.read? location = some value := by
    have afterClear := framed.read location value outside found
    exact (retained.read location (List.getElem?_eq_some_iff.mp afterClear).1).trans afterClear
  have callbackFound := keep callbackOutside callbackRead
  have functionRead := OptionalCell.read_success Creation.unavailableReason
    ((input_part inputs' (index := 4) rfl).evaluates copiedStore) callbackFound
  have sharedCopied : AccountCallCorrespondence.SharedStateRel sharedLocations shared copiedStore := by
    obtain ⟨accounts, worldSame, worldRead⟩ := sharedRelated.world
    exact ⟨⟨accounts, worldSame, keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) worldRead⟩,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.logs,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.logSize,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.balances,
      keep (separate _ (by simp [AccountCallCorrespondence.SharedLocations.all])) sharedRelated.complete,
      sharedRelated.distinct⟩
  have functionCode := CodeValue.bound (0 + [Value.unit, Value.unit, Value.unit].length + 4)
    (extra ++ ([.unit, .unit, .unit] ++ bundleValues (argumentValues locations callback arguments) :: environment)) function
  have callInputs := inputs'.prepend [function]
  have requestEvaluated : Evaluates (function :: extra ++ ([.unit, .unit, .unit] ++
      bundleValues (argumentValues locations callback arguments) :: environment)) copiedStore
      (CreationImplementation.request initCode (0 + 3 + 4 + 1))
      (requestValue (request arguments input)) copiedStore := by
    refine .pair (.binary ((input_part callInputs (index := 5) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 7) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 8) rfl).evaluates copiedStore) ?_
    refine .pair ((input_part callInputs (index := 9) rfl).evaluates copiedStore) ?_
    refine .pair (.binary ((input_part callInputs (index := 6) rfl).evaluates copiedStore) .word rfl) ?_
    refine .pair ((input_part callInputs (index := 10) rfl).evaluates copiedStore) ?_
    exact .pair (.loadCell ((initRelated.prepend [function]).evaluates copiedStore) initRead)
      ((input_part callInputs (index := 12) rfl).evaluates copiedStore)
  obtain ⟨afterCall, called, callRetained⟩ := handler.apply_refused sharedCopied (refusing input)
    ((functionCode.evaluates copiedStore)) requestEvaluated
  have afterRelated := state_retained clearedRelated (retained.trans callRetained)
  have finished := finish_evaluates callInputs afterRelated
  refine ⟨publishStore locations afterCall [] Word.zero, .letE packed ?_, published afterRelated [] Word.zero,
    (framed.trans (retained_frame locations (retained.trans callRetained))).trans
      (LogsCorrespondence.Frame.publish locations.resources afterCall [] Word.zero)⟩
  apply LanguageResult.bind_success .word touched
  apply clear_evaluates (inputs.prepend [.unit]) inputRelated
  apply Evaluates.ifFalse (.binary ((input_part dispatchInputs (index := 6) rfl).evaluates _) .word
    (by simp [BinaryOp.apply, Creation.depthLimit, allowed]))
  apply entered
  apply LanguageResult.bind_success .word functionRead
  apply LanguageResult.bind_success .word called
  exact finished

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
/-- The transport preserves the variable renaming of the outer lowering. -/
theorem invoke_rename (memoryReference sizeReference returnDataReference returnSizeReference
    callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas
    offset length : Core.Expr) (mapping : Renaming) :
    (Creation.invoke memoryReference sizeReference returnDataReference returnSizeReference
      callbackReference creatorAddress depth transferredValue saltValue isCreate2 suppliedGas offset length).rename mapping =
    Creation.invoke (memoryReference.rename mapping) (sizeReference.rename mapping)
      (returnDataReference.rename mapping) (returnSizeReference.rename mapping) (callbackReference.rename mapping)
      (creatorAddress.rename mapping) (depth.rename mapping) (transferredValue.rename mapping)
      (saltValue.rename mapping) (isCreate2.rename mapping) (suppliedGas.rename mapping)
      (offset.rename mapping) (length.rename mapping) := by
  rw [CreationImplementation.invoke_eq, CreationImplementation.invoke_eq]
  simp only [bundle, Core.Expr.rename]
  congr 1
  simp [CreationImplementation.invokeCode, CreationImplementation.dispatch, CreationImplementation.finish,
    CreationImplementation.request, CreationImplementation.input, CodeBuilder.bind, CodeBuilder.bindResult,
    CodeBuilder.store, CodeBuilder.load, CodeBuilder.allocate, CodeBuilder.empty, CodeBuilder.choose,
    CodeBuilder.binary, CodeBuilder.success, CodeBuilder.number, CodeBuilder.constant, CodeBuilder.part,
    CodeBuilder.apply, CodeBuilder.packet, CodeBuilder.address, MemoryCopyCorrespondence.copyPackedFrom_rename,
    Memory.touch, Memory.packet, Memory.field, Memory.number, Memory.add, Creation.responseField, projectArgument, bundle,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    OptionalCell.read, WordMapping.empty, Core.Expr.rename, Core.Renaming.lift]
  all_goals rfl

end Solcore.Frontend.RustHull.CreationCorrespondence
