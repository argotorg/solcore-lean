import Solcore.Frontend.RustHull.AccountRuntime
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.CallTransportValues
import Solcore.Frontend.RustHull.EffectStateCorrespondence
import Solcore.Frontend.RustHull.Sha256HashCorrespondence

/-! The implemented identity and SHA-256 precompiles preserve their independent
gas, byte-copy and digest meaning. `Precompiles` keeps its builders private, so
`staticCall_shape` restates the implemented expression with public builders and
proves the restatement by `rfl`. Only these two branches are spelled out; the
other precompiled branches remain opaque. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PrecompileCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

namespace Implementation

def integer (value : Nat) : Code := fun _ => .integer (Int.ofNat value)
def unary (op : UnaryOp) (value : Code) : Code := fun depth => .unary op (value depth)
/-- Field `index` of the ten-field call packet bound at depth zero. -/
def input (index : Nat) : Code := part index 10 (fun depth => .var depth)
def touch (size offset length : Code) : Code := fun depth =>
  Memory.touch (size depth) (offset depth) (length depth)
def copy (memory size destination mapping source length : Code) : Code := fun depth =>
  Memory.copyPackedFrom (memory depth) (size depth) (destination depth)
    (mapping depth) (source depth) (length depth)

def enoughGas (base perWord : Nat) : Code :=
  unary .boolNot (binary .integerLt (unary .wordToInteger (input 4))
    (binary .integerAdd (integer base)
      (binary .integerMul (integer perWord)
        (binary .integerDiv
          (binary .integerAdd (unary .wordToInteger (input 7)) (integer 31)) (integer 32)))))

def finish (mapping length : Code) : Code :=
  bind mapping fun snapshot =>
  bind (store (input 2) snapshot) fun _ =>
  bind (store (input 3) length) fun _ =>
  bindResult .word (copy (input 0) (input 1) (input 8) snapshot (number 0)
    (choose (binary .wordGt length (input 9)) (input 9) length)) fun _ =>
  success (number 1)

def identity (snapshot : Code) : Code :=
  bind (allocate WordMapping.type empty) fun resultMemory =>
  bind (allocate .word (number 0)) fun resultSize =>
  bindResult .word (copy resultMemory resultSize (number 0) snapshot (input 6) (input 7)) fun _ =>
  finish (load resultMemory) (input 7)

def finishWord (value : Code) : Code :=
  bindResult .word (fun depth => WordMapping.insert WordMapping.empty (number 0 depth) (value depth)) fun mapping =>
  finish mapping (number 32)

def hashCall (operation : Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr) (snapshot : Code) : Code :=
  bind (allocate WordMapping.type snapshot) fun sourceMemory =>
  bind (allocate .word (number 0)) fun sourceSize =>
  bindResult .word (fun depth => operation (sourceMemory depth) (sourceSize depth) (input 6 depth) (input 7 depth))
    finishWord

def select (recover ripemd p256 : Core.Expr) (snapshot address : Code) : Code :=
  choose (binary .wordEq address (number 1)) (constant recover) <|
  choose (binary .wordEq address (number 2))
    (choose (enoughGas 60 12) (hashCall Sha256.hash snapshot) (success (number 0))) <|
  choose (binary .wordEq address (number 3)) (constant ripemd) <|
  choose (binary .wordEq address (number 4))
    (choose (enoughGas 15 3) (identity snapshot) (success (number 0))) (constant p256)

def dispatch (recover ripemd p256 : Core.Expr) (snapshot : Code) : Code :=
  bind (binary .wordAnd (input 5) (number (2 ^ 160 - 1))) fun address =>
  select recover ripemd p256 snapshot address

def callCode (recover ripemd p256 : Core.Expr) : Code :=
  bindResult .word (touch (input 1) (input 6) (input 7)) fun _ =>
  bindResult .word (touch (input 1) (input 8) (input 9)) fun _ =>
  bind (load (input 0)) fun snapshot =>
  bind (store (input 2) empty) fun _ =>
  bind (store (input 3) (number 0)) fun _ =>
  dispatch recover ripemd p256 snapshot

end Implementation

/-- The actual precompile expression, with its other branches left opaque. -/
theorem staticCall_shape : ∃ recover ripemd p256 : Core.Expr,
    ∀ a b c d e f g h i j : Core.Expr, Precompiles.staticCall a b c d e f g h i j =
      .letE (bundle [a, b, c, d, e, f, g, h, i, j]) (Implementation.callCode recover ripemd p256 0) :=
  ⟨_, _, _, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩

/-- Cells below `boundary` keep their values; later cells may change. -/
structure RetainsBelow (boundary : Nat) (initial final : Core.Store) : Prop where
  length_le : initial.length ≤ final.length
  read : ∀ location, location < boundary → final.read? location = initial.read? location

theorem RetainsBelow.refl (boundary : Nat) (store : Core.Store) : RetainsBelow boundary store store :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem RetainsBelow.trans {boundary : Nat} {initial middle final : Core.Store}
    (first : RetainsBelow boundary initial middle) (second : RetainsBelow boundary middle final) :
    RetainsBelow boundary initial final :=
  ⟨Nat.le_trans first.length_le second.length_le, fun location below => by
    rw [second.read location below, first.read location below]⟩

theorem RetainsBelow.append {boundary : Nat} {store : Core.Store} (bounded : boundary ≤ store.length)
    (suffix : Core.Store) : RetainsBelow boundary store (store ++ suffix) :=
  ⟨by simp, fun location below => List.getElem?_append_left (by omega)⟩

theorem RetainsBelow.set {boundary location : Nat} (above : boundary ≤ location)
    (store : Core.Store) (value : Core.Value) :
    RetainsBelow boundary store (store.set location value) :=
  ⟨by simp, fun other below => by
    simp only [Store.read?]
    exact List.getElem?_set_ne (by omega)⟩

theorem RetainsBelow.ofFrame {boundary memoryLocation sizeLocation : Nat} {initial final : Core.Store}
    (framed : MemoryCorrespondence.Frame memoryLocation sizeLocation initial final)
    (memoryAbove : boundary ≤ memoryLocation) (sizeAbove : boundary ≤ sizeLocation)
    (bounded : boundary ≤ initial.length) : RetainsBelow boundary initial final :=
  ⟨framed.length, fun location below => by
    obtain ⟨value, found⟩ : ∃ value, initial.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem (Nat.lt_of_lt_of_le below bounded)⟩
    rw [found]
    exact framed.read location value (by omega) (by omega) found⟩

theorem RetainsBelow.touch {boundary location : Nat} (above : boundary ≤ location)
    (store : Core.Store) (size offset length : Core.Word) :
    RetainsBelow boundary store (MemoryCorrespondence.touchStore store location size offset length) :=
  ⟨Nat.le_of_eq (MemoryCorrespondence.touchStore_length ..).symm, fun other below =>
    MemoryCorrespondence.touchStore_other store (by omega) size offset length⟩

theorem RetainsBelow.retains {initial final : Core.Store}
    (retained : RetainsBelow initial.length initial final) : StoreRetains initial final :=
  ⟨retained.length_le, retained.read⟩

theorem enoughGas_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {gas length : Core.Word} (base perWord : Nat)
    (gasCode : CodeValue depth environment (Implementation.input 4) (.word gas))
    (lengthCode : CodeValue depth environment (Implementation.input 7) (.word length)) :
    Core.Evaluates environment store (Implementation.enoughGas base perWord depth)
      (.bool (decide (AccountCallSemantics.linearCost base perWord length ≤ gas.val))) store := by
  apply Core.Evaluates.unary
  · apply Core.Evaluates.binary (.unary (gasCode.evaluates store) rfl)
    · exact .binary .integer (.binary .integer (.binary (.binary (.unary (lengthCode.evaluates store) rfl)
        .integer rfl) .integer rfl) rfl) rfl
    · rfl
  · have divided : Integer.divide (Int.ofNat length.val + Int.ofNat 31) (Int.ofNat 32) =
        Int.ofNat ((length.val + 31) / 32) := by
      simp only [Integer.divide, Int.ofNat_eq_natCast]
      omega
    have total : Int.ofNat base + Int.ofNat perWord * Int.ofNat ((length.val + 31) / 32) =
        Int.ofNat (AccountCallSemantics.linearCost base perWord length) := by
      simp only [AccountCallSemantics.linearCost, Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
    rw [divided, total]
    simp only [UnaryOp.apply, Option.some.injEq, Value.bool.injEq, Int.ofNat_eq_natCast]
    by_cases enough : AccountCallSemantics.linearCost base perWord length ≤ gas.val
    · simp only [enough, decide_true, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    · simp only [enough, decide_false, Bool.not_eq_false', decide_eq_true_eq]
      omega

/-- The ten packet fields received by the precompile body: four fresh cells,
then the forwarded gas, target, input range and the empty output range. -/
def packetValues (memory size data dataSize : Nat) (request : AccountCallSemantics.Request) : List Core.Value :=
  [.cellRef WordMapping.type memory, .cellRef .word size, .cellRef WordMapping.type data, .cellRef .word dataSize,
   .word request.gas, .word request.target, .word Word.zero, .word request.calldataSize, .word Word.zero, .word Word.zero]

def packetValue (memory size data dataSize : Nat) (request : AccountCallSemantics.Request) : Core.Value :=
  bundleValues (packetValues memory size data dataSize request)

theorem packet_field {environment : Core.Environment} {memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {index : Nat} {value : Core.Value}
    (found : (packetValues memory size data dataSize request)[index]? = some value) :
    CodeValue 0 (packetValue memory size data dataSize request :: environment) (Implementation.input index) value := by
  have packetCode : CodeValue 0 (packetValue memory size data dataSize request :: environment)
      (fun depth => .var depth) (packetValue memory size data dataSize request) := by
    intro extra store
    exact .var (by simp)
  exact packetCode.part found

/-- The environment of a selected branch: the masked address, two discarded
updates, the input snapshot, two discarded touches and the call packet. -/
def branchEnvironment (address memory size data dataSize : Nat) (request : AccountCallSemantics.Request)
    (environment : Core.Environment) : Core.Environment :=
  [.word (Word.ofNatModulo address), .unit, .unit, WordMapping.encode request.calldata, .unit, .unit,
    packetValue memory size data dataSize request] ++ environment

theorem branch_field {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {index : Nat} {value : Core.Value}
    (found : (packetValues memory size data dataSize request)[index]? = some value) :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (Implementation.input index) value :=
  (packet_field found).prepend [.word (Word.ofNatModulo address), .unit, .unit, WordMapping.encode request.calldata,
    .unit, .unit]

theorem branch_snapshot {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (fun here => .var (here - 2 - 1)) (WordMapping.encode request.calldata) :=
  (CodeValue.bound 2 ([.unit, .unit, packetValue memory size data dataSize request] ++ environment)
    (WordMapping.encode request.calldata)).prepend [.word (Word.ofNatModulo address), .unit, .unit]

theorem branch_address {environment : Core.Environment} {address memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} :
    CodeValue 6 (branchEnvironment address memory size data dataSize request environment)
      (fun here => .var (here - 5 - 1)) (.word (Word.ofNatModulo address)) :=
  CodeValue.bound 5 ([.unit, .unit, WordMapping.encode request.calldata, .unit, .unit,
    packetValue memory size data dataSize request] ++ environment) (.word (Word.ofNatModulo address))

/-- Both range touches, the return-data reset and target masking reach the
actual selection among the implemented precompiles. -/
theorem callCode_prefix {recover ripemd p256 : Core.Expr} {environment : Core.Environment}
    {store : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize : Core.Word} {address : Nat} {flag : Core.Value} {final : Core.Store}
    (masked : request.target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo address)
    (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size)
    (continued : Core.Evaluates (branchEnvironment address memory size data dataSize request environment)
      (((MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize).set data
        (WordMapping.encode [])).set dataSize (.word Word.zero))
      (Implementation.select recover ripemd p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final) :
    Core.Evaluates (packetValue memory size data dataSize request :: environment) store
      (Implementation.callCode recover ripemd p256 0) flag final := by
  let first := MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize
  have touched := MemoryCorrespondence.touch_evaluates
    (environment := packetValue memory size data dataSize request :: environment)
    ((packet_field (index := 1) rfl).evaluates store) ((packet_field (index := 6) rfl).evaluates store)
    ((packet_field (index := 7) rfl).evaluates store) sizeRead
  simp only [MemoryCorrespondence.touchResult, valid] at touched
  apply LanguageResult.bind_success .word touched
  have firstSize : first.read? size = some (.word inputSize) := MemoryCorrespondence.touchStore_read sizeRead valid
  have touchedOutput := MemoryCorrespondence.touch_evaluates
    (environment := .unit :: packetValue memory size data dataSize request :: environment)
    (((packet_field (index := 1) rfl).prepend [.unit]).evaluates first)
    (((packet_field (index := 8) rfl).prepend [.unit]).evaluates first)
    (((packet_field (index := 9) rfl).prepend [.unit]).evaluates first) firstSize
  have unchanged : MemoryCorrespondence.touchStore first size inputSize Word.zero Word.zero = first := by
    simp [MemoryCorrespondence.touchStore]
  simp only [MemoryCorrespondence.touchResult, MemorySemantics.touchSize?, beq_self_eq_true, ↓reduceIte,
    unchanged] at touchedOutput
  apply LanguageResult.bind_success .word touchedOutput
  have firstMemory : first.read? memory = some (WordMapping.encode request.calldata) :=
    (MemoryCorrespondence.touchStore_other store memorySize _ _ _).trans memoryRead
  apply Core.Evaluates.letE (.loadCell (((packet_field (index := 0) rfl).prepend [.unit, .unit]).evaluates first)
    firstMemory)
  have firstLength : first.length = store.length := MemoryCorrespondence.touchStore_length ..
  have dataFirst : data < first.length := by rw [firstLength]; exact dataBound
  have dataOld : first.read? data = some (first[data]'dataFirst) := List.getElem?_eq_getElem _
  apply Core.Evaluates.letE (.storeCell
    (((packet_field (index := 2) rfl).prepend [WordMapping.encode request.calldata, .unit, .unit]).evaluates first)
    dataOld ((CodeValue.empty _ _).evaluates first) (Store.write?_eq_some_iff.mpr ⟨dataFirst, rfl⟩))
  let second : Store := first.set data (WordMapping.encode [])
  have dataSizeSecond : dataSize < second.length := by
    simp only [second, List.length_set, firstLength]; exact dataSizeBound
  have dataSizeOld : second.read? dataSize = some (second[dataSize]'dataSizeSecond) := List.getElem?_eq_getElem _
  apply Core.Evaluates.letE (.storeCell
    (((packet_field (index := 3) rfl).prepend [.unit, WordMapping.encode request.calldata, .unit, .unit]).evaluates second)
    dataSizeOld .word (Store.write?_eq_some_iff.mpr ⟨dataSizeSecond, rfl⟩))
  apply Core.Evaluates.letE (boundValue := .word (Word.ofNatModulo address)) (.binary
    (((packet_field (index := 5) rfl).prepend [.unit, .unit, WordMapping.encode request.calldata, .unit, .unit]).evaluates _)
    .word (by
      show some (Value.word (request.target.bitAnd (Word.ofNatModulo (2 ^ 160 - 1)))) = _
      rw [masked]))
  exact continued

/-- Address 4 selects the identity branch. -/
theorem select_identity {recover ripemd p256 : Core.Expr} {environment : Core.Environment}
    {store final : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {flag : Core.Value}
    (continued : Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
      (choose (Implementation.enoughGas 15 3) (Implementation.identity (fun here => .var (here - 2 - 1)))
        (success (number 0)) 6) flag final) :
    Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
      (Implementation.select recover ripemd p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final := by
  have addressCode := branch_address (environment := environment) (address := 4) (memory := memory) (size := size)
    (data := data) (dataSize := dataSize) (request := request)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  exact .ifTrue (.binary (addressCode.evaluates _) .word rfl) continued

/-- Address 2 selects the SHA-256 branch. -/
theorem select_sha256 {recover ripemd p256 : Core.Expr} {environment : Core.Environment}
    {store final : Core.Store} {memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {flag : Core.Value}
    (continued : Core.Evaluates (branchEnvironment 2 memory size data dataSize request environment) store
      (choose (Implementation.enoughGas 60 12) (Implementation.hashCall Sha256.hash (fun here => .var (here - 2 - 1)))
        (success (number 0)) 6) flag final) :
    Core.Evaluates (branchEnvironment 2 memory size data dataSize request environment) store
      (Implementation.select recover ripemd p256 (fun here => .var (here - 2 - 1)) (fun here => .var (here - 5 - 1)) 6)
      flag final := by
  have addressCode := branch_address (environment := environment) (address := 2) (memory := memory) (size := size)
    (data := data) (dataSize := dataSize) (request := request)
  apply Core.Evaluates.ifFalse (.binary (addressCode.evaluates _) .word rfl)
  exact .ifTrue (.binary (addressCode.evaluates _) .word rfl) continued


theorem read_set_other {store : Core.Store} {location other : Nat} {value : Core.Value}
    (different : other ≠ location) : Store.read? (store.set location value) other = store.read? other := by
  simp only [Store.read?]
  exact List.getElem?_set_ne (Ne.symm different)

theorem read_set_self {store : Core.Store} {location : Nat} {value : Core.Value}
    (bound : location < store.length) : Store.read? (store.set location value) location = some value := by
  simp only [Store.read?]
  exact List.getElem?_set_self bound

/-- Sufficient gas copies the complete input into fresh result memory through
the actual copy loop, then publishes that mapping and the input length as
return data. The empty output range leaves caller memory unchanged. -/
theorem identity_evaluates {environment : Core.Environment} {store : Core.Store}
    {boundary memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize : Core.Word} {output : MemorySemantics.Entries}
    (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize)
    (copied : MemoryCopySemantics.Copy request.calldata Word.zero Word.zero request.calldataSize [] output)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word inputSize))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ final, Core.Evaluates (branchEnvironment 4 memory size data dataSize request environment) store
        (Implementation.identity (fun here => .var (here - 2 - 1)) 6)
        (.inRight .word (.word (Word.ofNatModulo 1))) final ∧
      final.read? data = some (WordMapping.encode output) ∧
      final.read? dataSize = some (.word request.calldataSize) ∧ RetainsBelow boundary store final := by
  let base := branchEnvironment 4 memory size data dataSize request environment
  have memoryBound : memory < store.length := (List.getElem?_eq_some_iff.mp memoryRead).1
  have sizeBound : size < store.length := (List.getElem?_eq_some_iff.mp sizeRead).1
  let resultSize := (store ++ [WordMapping.encode []]).length
  let allocated : Core.Store := (store ++ [WordMapping.encode []]) ++ [.word (Word.ofNatModulo 0)]
  have freshRelated : MemoryCorrespondence.StateRel store.length resultSize ⟨[], Word.zero⟩ allocated :=
    ⟨by simp [resultSize], by simp [allocated, Store.read?], by simp [allocated, resultSize, Store.read?]; rfl⟩
  let resultMemoryValue := Core.Value.cellRef WordMapping.type store.length
  let resultSizeValue := Core.Value.cellRef .word resultSize
  have memoryCode := CodeValue.bound 6 base resultMemoryValue
  have sizeCode := CodeValue.bound 7 (resultMemoryValue :: base) resultSizeValue
  obtain ⟨copyTarget, copiedStore, copyRelated, copyEvaluated, copiedRelated, copiedFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := [resultSizeValue, resultMemoryValue] ++ base)
      (MemoryCopySemantics.From.done (initial := ⟨[], Word.zero⟩) valid copied) freshRelated
      ((memoryCode.prepend [resultSizeValue]).evaluates allocated) (sizeCode.evaluates allocated) .word
      ((branch_snapshot.prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
      (((branch_field (index := 6) rfl).prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
      (((branch_field (index := 7) rfl).prepend [resultSizeValue, resultMemoryValue]).evaluates allocated)
  cases copyRelated with
  | value unitRelated =>
  cases unitRelated
  have allocatedLength : allocated.length = store.length + 2 := by simp [allocated]
  have copiedLength : store.length + 2 ≤ copiedStore.length := allocatedLength ▸ copiedFrame.length
  have retainedAllocated : ∀ location, location < store.length →
      copiedStore.read? location = store.read? location := by
    intro location below
    have found : allocated.read? location = store.read? location := by
      simp only [allocated, Store.read?, List.append_assoc]
      exact List.getElem?_append_left below
    obtain ⟨value, stored⟩ : ∃ value, store.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem below⟩
    rw [stored] at found ⊢
    exact copiedFrame.read location value (by omega) (by simp [resultSize]; omega) found
  let published : Core.Store := copiedStore.set data (WordMapping.encode output)
  let sized : Core.Store := published.set dataSize (.word request.calldataSize)
  have callerRelated : MemoryCorrespondence.StateRel memory size ⟨request.calldata, inputSize⟩ sized := by
    refine ⟨memorySize, ?_, ?_⟩
    · simp only [sized, published]
      rw [read_set_other memoryDataSize, read_set_other memoryData, retainedAllocated memory memoryBound]
      exact memoryRead
    · simp only [sized, published]
      rw [read_set_other sizeDataSize, read_set_other sizeData, retainedAllocated size sizeBound]
      exact sizeRead
  let outputValue := WordMapping.encode output
  let finishEnvironment := [Core.Value.unit, .unit, outputValue, .unit, resultSizeValue, resultMemoryValue] ++ base
  have finishField {index : Nat} {value : Core.Value}
      (found : (packetValues memory size data dataSize request)[index]? = some value) :
      CodeValue 12 finishEnvironment (Implementation.input index) value :=
    (branch_field found).prepend [.unit, .unit, outputValue, .unit, resultSizeValue, resultMemoryValue]
  have snapshotCode := (CodeValue.bound 9 (.unit :: [resultSizeValue, resultMemoryValue] ++ base) outputValue).prepend
    [.unit, .unit]
  have lengthEvaluated : Core.Evaluates finishEnvironment sized
      (.ifE (.binary .wordGt (Implementation.input 7 12) (Implementation.input 9 12))
        (Implementation.input 9 12) (Implementation.input 7 12)) (.word Word.zero) sized := by
    by_cases positive : request.calldataSize > Word.zero
    · exact .ifTrue (.binary ((finishField (index := 7) rfl).evaluates sized) ((finishField (index := 9) rfl).evaluates sized)
        (by simp [BinaryOp.apply, positive])) ((finishField (index := 9) rfl).evaluates sized)
    · have zero : request.calldataSize = Word.zero := by
        apply Fin.ext
        simp only [GT.gt, Fin.lt_def, Word.zero, Nat.not_lt] at positive
        simpa [Word.zero] using positive
      apply Core.Evaluates.ifFalse (.binary ((finishField (index := 7) rfl).evaluates sized)
        ((finishField (index := 9) rfl).evaluates sized) (by simp [BinaryOp.apply, positive]))
      simpa only [zero] using (finishField (index := 7) rfl).evaluates sized
  obtain ⟨finishTarget, final, finishRelated, finishEvaluated, finalRelated, finalFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := finishEnvironment)
      (MemoryCopySemantics.From.done (initial := ⟨request.calldata, inputSize⟩) (size := inputSize)
        (by simp [MemorySemantics.touchSize?]) (.empty output request.calldata Word.zero Word.zero)) callerRelated
      ((finishField (index := 0) rfl).evaluates sized) ((finishField (index := 1) rfl).evaluates sized)
      ((finishField (index := 8) rfl).evaluates sized) (snapshotCode.evaluates sized) .word lengthEvaluated
  cases finishRelated with
  | value unitRelated =>
  cases unitRelated
  have dataCopied : data < copiedStore.length := by omega
  have dataSizePublished : dataSize < published.length := by simp only [published, List.length_set]; omega
  have dataOld : copiedStore.read? data = some (copiedStore[data]'dataCopied) := List.getElem?_eq_getElem _
  have dataSizeOld : Store.read? published dataSize = some (published[dataSize]'dataSizePublished) :=
    List.getElem?_eq_getElem _
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success .word copyEvaluated
    apply Core.Evaluates.letE (.loadCell ((memoryCode.prepend [.unit, resultSizeValue]).evaluates copiedStore)
      copiedRelated.memory)
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 2) rfl).prepend [outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates copiedStore)
      dataOld ((CodeValue.bound 9 (.unit :: [resultSizeValue, resultMemoryValue] ++ base) outputValue).evaluates copiedStore)
      (Store.write?_eq_some_iff.mpr ⟨dataCopied, rfl⟩))
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 3) rfl).prepend [.unit, outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates published)
      dataSizeOld
      (((branch_field (index := 7) rfl).prepend [.unit, outputValue, .unit, resultSizeValue, resultMemoryValue]).evaluates published)
      (Store.write?_eq_some_iff.mpr ⟨dataSizePublished, rfl⟩))
    apply LanguageResult.bind_success .word finishEvaluated
    exact .inRight .word
  · have published : sized.read? data = some outputValue := by
      simp only [sized, published]
      rw [read_set_other dataDataSize, read_set_self dataCopied]
    exact finalFrame.read data _ (Ne.symm memoryData) (Ne.symm sizeData) published
  · have sizedRead : sized.read? dataSize = some (.word request.calldataSize) := read_set_self dataSizePublished
    exact finalFrame.read dataSize _ (Ne.symm memoryDataSize) (Ne.symm sizeDataSize) sizedRead
  · have bounded : boundary ≤ store.length := by omega
    have first : RetainsBelow boundary store allocated := by
      simpa only [allocated, List.append_assoc] using
        RetainsBelow.append bounded ([WordMapping.encode []] ++ [.word (Word.ofNatModulo 0)])
    have second := RetainsBelow.ofFrame (boundary := boundary) copiedFrame (by omega) (by simp [resultSize]; omega)
      (by simp [allocated]; omega)
    have third := RetainsBelow.set (boundary := boundary) dataAbove copiedStore (WordMapping.encode output)
    have fourth := RetainsBelow.set (boundary := boundary) dataSizeAbove published (.word request.calldataSize)
    have fifth := RetainsBelow.ofFrame (boundary := boundary) finalFrame memoryAbove sizeAbove
      (by simp only [sized, published, List.length_set]; omega)
    exact first.trans (second.trans (third.trans (fourth.trans fifth)))

/-- Sufficient gas digests the complete input from a fresh copy of the input
snapshot through the actual SHA-256 expression, then publishes the 32-byte
digest as return data. The empty output range leaves caller memory unchanged. -/
theorem sha256_evaluates {environment : Core.Environment} {store : Core.Store}
    {boundary memory size data dataSize : Nat} {request : AccountCallSemantics.Request}
    {inputSize digest : Core.Word}
    (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize)
    (digested : Sha256Semantics.Digest request.calldata Word.zero request.calldataSize digest)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word inputSize))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ final, Core.Evaluates (branchEnvironment 2 memory size data dataSize request environment) store
        (Implementation.hashCall Sha256.hash (fun here => .var (here - 2 - 1)) 6)
        (.inRight .word (.word (Word.ofNatModulo 1))) final ∧
      final.read? data = some (WordMapping.encode [(Word.zero, digest)]) ∧
      final.read? dataSize = some (.word (Word.ofNatModulo 32)) ∧ RetainsBelow boundary store final := by
  let base := branchEnvironment 2 memory size data dataSize request environment
  have memoryBound : memory < store.length := (List.getElem?_eq_some_iff.mp memoryRead).1
  have sizeBound : size < store.length := (List.getElem?_eq_some_iff.mp sizeRead).1
  let sourceSize := (store ++ [WordMapping.encode request.calldata]).length
  let allocated : Core.Store := (store ++ [WordMapping.encode request.calldata]) ++ [.word (Word.ofNatModulo 0)]
  have sourceRelated : MemoryCorrespondence.StateRel store.length sourceSize ⟨request.calldata, Word.zero⟩ allocated :=
    ⟨by simp [sourceSize], by simp [allocated, Store.read?], by simp [allocated, sourceSize, Store.read?]; rfl⟩
  let sourceMemoryValue := Core.Value.cellRef WordMapping.type store.length
  let sourceSizeValue := Core.Value.cellRef .word sourceSize
  have memoryCode := CodeValue.bound 6 base sourceMemoryValue
  have sizeCode := CodeValue.bound 7 (sourceMemoryValue :: base) sourceSizeValue
  obtain ⟨hashed, hashEvaluated, hashedRelated, hashedFrame⟩ :=
    Sha256HashCorrespondence.hash_preserves (environment := [sourceSizeValue, sourceMemoryValue] ++ base)
      (state := ⟨request.calldata, Word.zero⟩) valid digested sourceRelated
      ((memoryCode.prepend [sourceSizeValue]).evaluates allocated) (sizeCode.evaluates allocated)
      (((branch_field (index := 6) rfl).prepend [sourceSizeValue, sourceMemoryValue]).evaluates allocated)
      (((branch_field (index := 7) rfl).prepend [sourceSizeValue, sourceMemoryValue]).evaluates allocated)
  have allocatedLength : allocated.length = store.length + 2 := by simp [allocated]
  have hashedLength : store.length + 2 ≤ hashed.length := allocatedLength ▸ hashedFrame.length
  have retainedAllocated : ∀ location, location < store.length →
      hashed.read? location = store.read? location := by
    intro location below
    have found : allocated.read? location = store.read? location := by
      simp only [allocated, Store.read?, List.append_assoc]
      exact List.getElem?_append_left below
    obtain ⟨value, stored⟩ : ∃ value, store.read? location = some value :=
      ⟨_, List.getElem?_eq_getElem below⟩
    rw [stored] at found ⊢
    exact hashedFrame.read location value (by omega) (by simp [sourceSize]; omega) found
  let digestValue := Core.Value.word digest
  let insertEnvironment := digestValue :: [sourceSizeValue, sourceMemoryValue] ++ base
  let mappingValue := WordMapping.encode [(Word.ofNatModulo 0, digest)]
  let inserted : Core.Store := WordMapping.installedStore hashed WordMapping.insertParameter WordMapping.type
    WordMapping.insertBody (.pair (WordMapping.encode []) (.pair (.word (Word.ofNatModulo 0)) (.word digest)))
    insertEnvironment
  have insertEvaluated : Core.Evaluates insertEnvironment hashed
      (WordMapping.insert WordMapping.empty (.word (Word.ofNatModulo 0)) (.var 0))
      (.inRight .word mappingValue) inserted :=
    WordMapping.insert_evaluates [] (Word.ofNatModulo 0) digest (.construct .unit) .word (.var rfl)
  have insertedRead : ∀ location, location < hashed.length → inserted.read? location = hashed.read? location :=
    fun location bound => List.getElem?_append_left bound
  have insertedLength : hashed.length ≤ inserted.length := by simp [inserted, WordMapping.installedStore]
  have dataInserted : data < inserted.length := by omega
  let published : Core.Store := inserted.set data mappingValue
  let sized : Core.Store := published.set dataSize (.word (Word.ofNatModulo 32))
  have dataSizePublished : dataSize < published.length := by simp only [published, List.length_set]; omega
  have callerRelated : MemoryCorrespondence.StateRel memory size ⟨request.calldata, inputSize⟩ sized := by
    refine ⟨memorySize, ?_, ?_⟩
    · simp only [sized, published]
      rw [read_set_other memoryDataSize, read_set_other memoryData, insertedRead memory (by omega),
        retainedAllocated memory memoryBound]
      exact memoryRead
    · simp only [sized, published]
      rw [read_set_other sizeDataSize, read_set_other sizeData, insertedRead size (by omega),
        retainedAllocated size sizeBound]
      exact sizeRead
  let finishEnvironment := [Core.Value.unit, .unit, mappingValue, mappingValue] ++ insertEnvironment
  have finishField {index : Nat} {value : Core.Value}
      (found : (packetValues memory size data dataSize request)[index]? = some value) :
      CodeValue 13 finishEnvironment (Implementation.input index) value :=
    (branch_field found).prepend [.unit, .unit, mappingValue, mappingValue, digestValue, sourceSizeValue, sourceMemoryValue]
  have snapshotCode := (CodeValue.bound 10 (mappingValue :: insertEnvironment) mappingValue).prepend [.unit, .unit]
  have lengthEvaluated : Core.Evaluates finishEnvironment sized
      (.ifE (.binary .wordGt (.word (Word.ofNatModulo 32)) (Implementation.input 9 13))
        (Implementation.input 9 13) (.word (Word.ofNatModulo 32))) (.word Word.zero) sized :=
    .ifTrue (.binary .word ((finishField (index := 9) rfl).evaluates sized) rfl)
      ((finishField (index := 9) rfl).evaluates sized)
  obtain ⟨finishTarget, final, finishRelated, finishEvaluated, finalRelated, finalFrame⟩ :=
    MemoryCopyCorrespondence.copyPackedFrom_preserves (environment := finishEnvironment)
      (MemoryCopySemantics.From.done (initial := ⟨request.calldata, inputSize⟩) (size := inputSize)
        (by simp [MemorySemantics.touchSize?]) (.empty [(Word.ofNatModulo 0, digest)] request.calldata Word.zero Word.zero))
      callerRelated
      ((finishField (index := 0) rfl).evaluates sized) ((finishField (index := 1) rfl).evaluates sized)
      ((finishField (index := 8) rfl).evaluates sized) (snapshotCode.evaluates sized) .word lengthEvaluated
  cases finishRelated with
  | value unitRelated =>
  cases unitRelated
  have dataOld : inserted.read? data = some (inserted[data]'dataInserted) := List.getElem?_eq_getElem _
  have dataSizeOld : Store.read? published dataSize = some (published[dataSize]'dataSizePublished) :=
    List.getElem?_eq_getElem _
  refine ⟨final, ?_, ?_, ?_, ?_⟩
  · apply Core.Evaluates.letE (.newCell (branch_snapshot.evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success .word hashEvaluated
    apply LanguageResult.bind_success .word insertEvaluated
    apply Core.Evaluates.letE (.var rfl)
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 2) rfl).prepend [mappingValue, mappingValue, digestValue, sourceSizeValue,
        sourceMemoryValue]).evaluates inserted)
      dataOld ((CodeValue.bound 10 (mappingValue :: insertEnvironment) mappingValue).evaluates inserted)
      (Store.write?_eq_some_iff.mpr ⟨dataInserted, rfl⟩))
    apply Core.Evaluates.letE (.storeCell
      (((branch_field (index := 3) rfl).prepend [.unit, mappingValue, mappingValue, digestValue, sourceSizeValue,
        sourceMemoryValue]).evaluates published)
      dataSizeOld .word (Store.write?_eq_some_iff.mpr ⟨dataSizePublished, rfl⟩))
    apply LanguageResult.bind_success .word finishEvaluated
    exact .inRight .word
  · have sizedRead : sized.read? data = some mappingValue := by
      simp only [sized, published]
      rw [read_set_other dataDataSize, read_set_self dataInserted]
    exact finalFrame.read data _ (Ne.symm memoryData) (Ne.symm sizeData) sizedRead
  · have sizedRead : sized.read? dataSize = some (.word (Word.ofNatModulo 32)) := read_set_self dataSizePublished
    exact finalFrame.read dataSize _ (Ne.symm memoryDataSize) (Ne.symm sizeDataSize) sizedRead
  · have bounded : boundary ≤ store.length := by omega
    have first : RetainsBelow boundary store allocated := by
      simpa only [allocated, List.append_assoc] using
        RetainsBelow.append bounded ([WordMapping.encode request.calldata] ++ [.word (Word.ofNatModulo 0)])
    have second := RetainsBelow.ofFrame (boundary := boundary) hashedFrame (by omega)
      (by simp [sourceSize]; omega) (by simp [allocated]; omega)
    have third : RetainsBelow boundary hashed inserted :=
      ⟨insertedLength, fun location below => insertedRead location (by omega)⟩
    have fourth := RetainsBelow.set (boundary := boundary) dataAbove inserted mappingValue
    have fifth := RetainsBelow.set (boundary := boundary) dataSizeAbove published (.word (Word.ofNatModulo 32))
    have sixth := RetainsBelow.ofFrame (boundary := boundary) finalFrame memoryAbove sizeAbove
      (by simp only [sized, published, List.length_set]; omega)
    exact first.trans (second.trans (third.trans (fourth.trans (fifth.trans sixth))))

/-- The body's flag, together with the response it leaves in the return-data
cells. -/
inductive Answered (data dataSize : Nat) (final : Core.Store) :
    Semantics.Result AccountCallSemantics.Response → Core.Value → Prop where
  | returned (response : AccountCallSemantics.Response)
      (dataRead : final.read? data = some (WordMapping.encode response.data))
      (sizeRead : final.read? dataSize = some (.word response.size)) :
      Answered data dataSize final (.value response)
        (.inRight .word (.word (Word.ofNatModulo (if response.success then 1 else 0))))
  | language (reason : Core.Word) :
      Answered data dataSize final (.fault (.language reason)) (.inLeft .word (.word reason))

/-- Every independent identity and SHA-256 outcome is produced by the actual
precompile body. Only its four fresh cells and later allocations change. -/
theorem callCode_preserves {recover ripemd p256 : Core.Expr} {environment : Core.Environment}
    {store : Core.Store} {boundary memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Precompile request result)
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ flag final, Core.Evaluates (packetValue memory size data dataSize request :: environment) store
        (Implementation.callCode recover ripemd p256 0) flag final ∧
      Answered data dataSize final result flag ∧ RetainsBelow boundary store final := by
  let first := MemoryCorrespondence.touchStore store size Word.zero Word.zero request.calldataSize
  let prepared : Core.Store := (first.set data (WordMapping.encode [])).set dataSize (.word Word.zero)
  have firstLength : first.length = store.length := MemoryCorrespondence.touchStore_length ..
  have dataFirst : data < first.length := by omega
  have dataSizeCleared : dataSize < (first.set data (WordMapping.encode [])).length := by
    simp only [List.length_set]; omega
  have preparedRetained : RetainsBelow boundary store prepared :=
    (RetainsBelow.touch sizeAbove store _ _ _).trans
      ((RetainsBelow.set dataAbove first _).trans (RetainsBelow.set dataSizeAbove _ _))
  have preparedData : prepared.read? data = some (WordMapping.encode []) := by
    simp only [prepared]
    rw [read_set_other dataDataSize, read_set_self dataFirst]
  have preparedDataSize : prepared.read? dataSize = some (.word Word.zero) := read_set_self dataSizeCleared
  have preparedMemory : prepared.read? memory = some (WordMapping.encode request.calldata) := by
    simp only [prepared]
    rw [read_set_other memoryDataSize, read_set_other memoryData,
      MemoryCorrespondence.touchStore_other store memorySize]
    exact memoryRead
  have preparedLength : prepared.length = store.length := by simp [prepared, firstLength]
  have preparedSize {inputSize : Core.Word}
      (valid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = some inputSize) :
      prepared.read? size = some (.word inputSize) := by
    simp only [prepared]
    rw [read_set_other sizeDataSize, read_set_other sizeData]
    exact MemoryCorrespondence.touchStore_read sizeRead valid
  have enough (address base perWord : Nat) := enoughGas_evaluates (store := prepared) base perWord
    (branch_field (environment := environment) (address := address) (memory := memory) (size := size) (data := data)
      (dataSize := dataSize) (request := request) (index := 4) rfl)
    (branch_field (environment := environment) (address := address) (memory := memory) (size := size) (data := data)
      (dataSize := dataSize) (request := request) (index := 7) rfl)
  have overflowed (invalid : MemorySemantics.touchSize? Word.zero Word.zero request.calldataSize = none) :
      ∃ flag final, Core.Evaluates (packetValue memory size data dataSize request :: environment) store
        (Implementation.callCode recover ripemd p256 0) flag final ∧
      Answered data dataSize final (.fault (.language (Word.ofNatModulo 6))) flag ∧
      RetainsBelow boundary store final := by
    have touched := MemoryCorrespondence.touch_evaluates
      (environment := packetValue memory size data dataSize request :: environment)
      ((packet_field (index := 1) rfl).evaluates store) ((packet_field (index := 6) rfl).evaluates store)
      ((packet_field (index := 7) rfl).evaluates store) sizeRead
    simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
    exact ⟨_, store, LanguageResult.bind_failure .word touched, .language _, .refl _ _⟩
  have maskedIdentity : (Word.ofNatModulo 4).bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo 4 := by
    decide +kernel
  have maskedSha256 : (Word.ofNatModulo 2).bitAnd (Word.ofNatModulo (2 ^ 160 - 1)) = Word.ofNatModulo 2 := by
    decide +kernel
  cases computed with
  | identityOverflow _ invalid => exact overflowed invalid
  | sha256Overflow _ invalid => exact overflowed invalid
  | identityUnderfunded identity valid short =>
    refine ⟨_, prepared, callCode_prefix (by rw [identity]; exact maskedIdentity) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_identity ?_),
      .returned (AccountCallSemantics.emptyResponse false) preparedData preparedDataSize, preparedRetained⟩
    have checked := enough 4 15 3
    simp only [Nat.not_le.mpr short, decide_false] at checked
    exact .ifFalse checked (.inRight .word)
  | @identity inputSize output identity valid funded copied =>
    obtain ⟨final, evaluated, dataRead, dataSizeRead, retained⟩ := identity_evaluates (environment := environment)
      valid copied preparedMemory (preparedSize valid) (by omega) (by omega) memorySize memoryData memoryDataSize
      sizeData sizeDataSize dataDataSize memoryAbove sizeAbove dataAbove dataSizeAbove
    refine ⟨_, final, callCode_prefix (by rw [identity]; exact maskedIdentity) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_identity ?_),
      .returned ⟨true, output, request.calldataSize⟩ dataRead dataSizeRead, preparedRetained.trans retained⟩
    have checked := enough 4 15 3
    simp only [funded, decide_true] at checked
    exact .ifTrue checked evaluated
  | sha256Underfunded sha256 valid short =>
    refine ⟨_, prepared, callCode_prefix (by rw [sha256]; exact maskedSha256) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_sha256 ?_),
      .returned (AccountCallSemantics.emptyResponse false) preparedData preparedDataSize, preparedRetained⟩
    have checked := enough 2 60 12
    simp only [Nat.not_le.mpr short, decide_false] at checked
    exact .ifFalse checked (.inRight .word)
  | @sha256 inputSize digest sha256 valid funded digested =>
    obtain ⟨final, evaluated, dataRead, dataSizeRead, retained⟩ := sha256_evaluates (environment := environment)
      valid digested preparedMemory (preparedSize valid) (by omega) (by omega) memorySize memoryData memoryDataSize
      sizeData sizeDataSize dataDataSize memoryAbove sizeAbove dataAbove dataSizeAbove
    refine ⟨_, final, callCode_prefix (by rw [sha256]; exact maskedSha256) valid memoryRead sizeRead dataBound
      dataSizeBound memorySize (select_sha256 ?_),
      .returned ⟨true, [(Word.zero, digest)], Word.ofNatModulo 32⟩ dataRead dataSizeRead,
      preparedRetained.trans retained⟩
    have checked := enough 2 60 12
    simp only [funded, decide_true] at checked
    exact .ifTrue checked evaluated

/-- The actual precompile expression evaluates its ten arguments into the
packet and runs the precompile body. -/
theorem staticCall_preserves {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {memoryCode sizeCode dataCode dataSizeCode gasCode targetCode lengthCode : Code}
    {boundary memory size data dataSize : Nat}
    {request : AccountCallSemantics.Request} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Precompile request result)
    (memoryValue : CodeValue depth environment memoryCode (.cellRef WordMapping.type memory))
    (sizeValue : CodeValue depth environment sizeCode (.cellRef .word size))
    (dataValue : CodeValue depth environment dataCode (.cellRef WordMapping.type data))
    (dataSizeValue : CodeValue depth environment dataSizeCode (.cellRef .word dataSize))
    (gasValue : CodeValue depth environment gasCode (.word request.gas))
    (targetValue : CodeValue depth environment targetCode (.word request.target))
    (lengthValue : CodeValue depth environment lengthCode (.word request.calldataSize))
    (memoryRead : store.read? memory = some (WordMapping.encode request.calldata))
    (sizeRead : store.read? size = some (.word Word.zero))
    (dataBound : data < store.length) (dataSizeBound : dataSize < store.length)
    (memorySize : memory ≠ size) (memoryData : memory ≠ data) (memoryDataSize : memory ≠ dataSize)
    (sizeData : size ≠ data) (sizeDataSize : size ≠ dataSize) (dataDataSize : data ≠ dataSize)
    (memoryAbove : boundary ≤ memory) (sizeAbove : boundary ≤ size)
    (dataAbove : boundary ≤ data) (dataSizeAbove : boundary ≤ dataSize) :
    ∃ flag final, Core.Evaluates environment store
        (Precompiles.staticCall (memoryCode depth) (sizeCode depth) (dataCode depth) (dataSizeCode depth)
          (gasCode depth) (targetCode depth) (number 0 depth) (lengthCode depth) (number 0 depth) (number 0 depth))
        flag final ∧
      Answered data dataSize final result flag ∧ RetainsBelow boundary store final := by
  obtain ⟨recover, ripemd, p256, shape⟩ := staticCall_shape
  obtain ⟨flag, final, evaluated, answered, retained⟩ := callCode_preserves (recover := recover)
    (ripemd := ripemd) (p256 := p256) (environment := environment) computed memoryRead sizeRead dataBound
    dataSizeBound memorySize memoryData memoryDataSize sizeData sizeDataSize dataDataSize memoryAbove sizeAbove
    dataAbove dataSizeAbove
  refine ⟨flag, final, ?_, answered, retained⟩
  rw [shape]
  apply Core.Evaluates.letE _ evaluated
  exact .pair (memoryValue.evaluates store) (.pair (sizeValue.evaluates store) (.pair (dataValue.evaluates store)
    (.pair (dataSizeValue.evaluates store) (.pair (gasValue.evaluates store) (.pair (targetValue.evaluates store)
      (.pair .word (.pair (lengthValue.evaluates store) (.pair .word .word))))))))

/-- The account runtime's private precompile call, restated with public
builders. `AccountCallCorrespondence.dispatch_precompile_eq` proves that it is
the implementation. -/
def precompileCode (request : Code) : Code :=
  bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
  bind (allocate .word (number 0)) fun size =>
  bind (allocate WordMapping.type empty) fun data =>
  bind (allocate .word (number 0)) fun dataSize =>
  bindResult Calls.responseType (fun depth => Precompiles.staticCall
    (memory depth) (size depth) (data depth) (dataSize depth)
    (part 5 8 request depth) (part 0 8 request depth)
    (number 0 depth) (part 7 8 request depth) (number 0 depth) (number 0 depth)) fun flag =>
  AccountRuntime.callResult (binary .wordEq flag (number 1)) (load data) (load dataSize)

/-- The independent precompile result is the actual response. The fresh
precompile cells lie above every cell of the calling store. -/
theorem precompile_preserves {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {requestCode : Code} {request : AccountCallSemantics.Request}
    {result : Semantics.Result AccountCallSemantics.Response}
    (requestRelated : CodeValue depth environment requestCode (requestValue request))
    (computed : AccountCallSemantics.Precompile request result) :
    ∃ target final, Core.Evaluates environment store (precompileCode requestCode depth) target final ∧
      ResponseRel result target ∧ StoreRetains store final := by
  let memory := store.length
  let first : Core.Store := store ++ [WordMapping.encode request.calldata]
  let size := first.length
  let second : Core.Store := first ++ [.word (Word.ofNatModulo 0)]
  let data := second.length
  let third : Core.Store := second ++ [WordMapping.encode []]
  let dataSize := third.length
  let allocated : Core.Store := third ++ [.word (Word.ofNatModulo 0)]
  let memoryRef := Core.Value.cellRef WordMapping.type memory
  let sizeRef := Core.Value.cellRef .word size
  let dataRef := Core.Value.cellRef WordMapping.type data
  let dataSizeRef := Core.Value.cellRef .word dataSize
  let cells : Core.Environment := [dataSizeRef, dataRef, sizeRef, memoryRef]
  have lengths : size = store.length + 1 ∧ data = store.length + 2 ∧ dataSize = store.length + 3 ∧
      allocated.length = store.length + 4 := by
    simp [size, data, dataSize, allocated, third, second, first]
  have memoryRead : allocated.read? memory = some (WordMapping.encode request.calldata) := by
    simp [allocated, third, second, first, memory, Store.read?]
  have sizeRead : allocated.read? size = some (.word Word.zero) := by
    simp [allocated, third, second, first, size, Store.read?]; rfl
  have memoryValue : CodeValue (depth + 4) (cells ++ environment) (fun here => .var (here - depth - 1)) memoryRef :=
    (CodeValue.bound depth environment memoryRef).prepend [dataSizeRef, dataRef, sizeRef]
  have sizeValue : CodeValue (depth + 4) (cells ++ environment) (fun here => .var (here - (depth + 1) - 1)) sizeRef :=
    (CodeValue.bound (depth + 1) (memoryRef :: environment) sizeRef).prepend [dataSizeRef, dataRef]
  have dataValue : CodeValue (depth + 4) (cells ++ environment)
      (fun here => .var (here - (depth + 1 + 1) - 1)) dataRef :=
    (CodeValue.bound (depth + 1 + 1) (sizeRef :: memoryRef :: environment) dataRef).prepend [dataSizeRef]
  have dataSizeValue : CodeValue (depth + 4) (cells ++ environment)
      (fun here => .var (here - (depth + 1 + 1 + 1) - 1)) dataSizeRef :=
    CodeValue.bound (depth + 1 + 1 + 1) (dataRef :: sizeRef :: memoryRef :: environment) dataSizeRef
  have requestValue' := requestRelated.prepend cells
  obtain ⟨flag, final, evaluated, answered, retained⟩ := staticCall_preserves (boundary := store.length)
    computed memoryValue sizeValue dataValue dataSizeValue (requestValue'.part (index := 5) rfl)
    (requestValue'.part (index := 0) rfl) (requestValue'.part (index := 7) rfl) memoryRead sizeRead
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (Nat.le_refl _) (by omega) (by omega) (by omega)
  have allocatedRetained : StoreRetains store allocated := by
    simpa only [allocated, third, second, first, List.append_assoc] using StoreRetains.append store _
  have finalRetained : StoreRetains store final :=
    ⟨Nat.le_trans allocatedRetained.length_le retained.length_le, fun location below => by
      rw [retained.read location below, allocatedRetained.read location below]⟩
  cases answered with
  | returned response dataRead dataSizeRead =>
    refine ⟨.inRight .word (responseValue response), final, ?_, .returned response, finalRetained⟩
    apply Core.Evaluates.letE (.newCell ((requestRelated.part (index := 6) rfl).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply LanguageResult.bind_success Calls.responseType evaluated
    let flagValue := Core.Value.word (Word.ofNatModulo (if response.success then 1 else 0))
    have flagCode := CodeValue.bound (depth + 4) (cells ++ environment) flagValue
    have flagEquals : BinaryOp.wordEq.apply flagValue (.word (Word.ofNatModulo 1)) = some (.bool response.success) := by
      show BinaryOp.wordEq.apply (.word (Word.ofNatModulo (if response.success = true then 1 else 0)))
        (.word (Word.ofNatModulo 1)) = some (.bool response.success)
      cases response.success <;> rfl
    exact .inRight (.pair (.binary (flagCode.evaluates final) .word flagEquals)
      (.pair (.loadCell ((dataValue.prepend [flagValue]).evaluates final) dataRead)
        (.loadCell ((dataSizeValue.prepend [flagValue]).evaluates final) dataSizeRead)))
  | language reason =>
    refine ⟨.inLeft Calls.responseType (.word reason), final, ?_, .language reason, finalRetained⟩
    apply Core.Evaluates.letE (.newCell ((requestRelated.part (index := 6) rfl).evaluates store))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.empty _ _).evaluates _))
    apply Core.Evaluates.letE (.newCell ((CodeValue.number 0 _ _).evaluates _))
    exact LanguageResult.bind_failure Calls.responseType evaluated

end Solcore.Frontend.RustHull.PrecompileCorrespondence
