import Solcore.Frontend.RustHull.CreationImplementation
import Solcore.Frontend.RustHull.CreationPreimage
import Solcore.Frontend.RustHull.KeccakHashCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! The actual address builders compute the independent CREATE and CREATE2
addresses. Each builder writes its preimage into fresh scratch cells with the
actual `mstore8` and `mstore` and hashes it with the connected Keccak; the
scratch bytes are the specified preimage, so the masked digest is the address.
CREATE2 first hashes the copied init bytes held in their own cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationAddressCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CreationPreimage CreationBytes

abbrev StateRel := MemoryCorrespondence.StateRel
abbrev Frame := MemoryCorrespondence.Frame

theorem touch_some (size offset length : Word) (small : offset.val + length.val < 2 ^ 255) :
    ∃ touched, MemorySemantics.touchSize? size offset length = some touched := by
  unfold MemorySemantics.touchSize?
  by_cases zero : length == Word.zero
  · simp [zero]
  · simp only [zero, Bool.false_eq_true, ↓reduceIte]
    have sum : (offset.add length).val = offset.val + length.val := by
      show (offset.val + length.val) % wordModulus = _
      exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
    have notWrapped : ¬offset > offset.add length := by
      rw [GT.gt, Fin.lt_def, sum]
      omega
    have notLarge : ¬offset.add length > Word.ofNatModulo (wordModulus - 32) := by
      rw [GT.gt, Fin.lt_def, sum, val_small (show wordModulus - 32 < 2 ^ 256 by decide)]
      change ¬(2 ^ 256 - 32 < offset.val + length.val)
      omega
    simp only [notWrapped, notLarge, ↓reduceIte]
    exact ⟨_, rfl⟩

theorem writeByte_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset value : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {offsetWord valueWord touched : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word offsetWord))
    (valueCode : CodeValue depth environment value (.word valueWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size offsetWord (Word.ofNatModulo 1) = some touched) :
    ∃ next, Evaluates environment store (CreationImplementation.writeByte memory size offset value depth)
        (.inRight .word .unit) next ∧
      StateRel memoryLocation sizeLocation ⟨MemorySemantics.writeByte state.words offsetWord valueWord, touched⟩ next ∧
      Frame memoryLocation sizeLocation store next := by
  have evaluated := MemoryCorrespondence.mstore8_evaluates state offsetWord valueWord
    (memoryCode.evaluates store) (sizeCode.evaluates store) (offsetCode.evaluates store) (valueCode.evaluates store)
    related.memory related.size related.distinct
  obtain ⟨_, nextRelated, frame⟩ := MemoryCorrespondence.mstore8_preserves related offsetWord valueWord environment
  simp only [MemoryCorrespondence.mstore8Result, fits] at evaluated
  simp only [MemorySemantics.mstore8, fits] at nextRelated
  exact ⟨_, evaluated, nextRelated, frame⟩

theorem writeWord_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset value : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {offsetWord valueWord touched : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word offsetWord))
    (valueCode : CodeValue depth environment value (.word valueWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size offsetWord (Word.ofNatModulo 32) = some touched) :
    ∃ next, Evaluates environment store (CreationImplementation.writeWord memory size offset value depth)
        (.inRight .word .unit) next ∧
      StateRel memoryLocation sizeLocation ⟨MemorySemantics.writeWord state.words offsetWord valueWord, touched⟩ next ∧
      Frame memoryLocation sizeLocation store next := by
  have evaluated := MemoryCorrespondence.mstore_evaluates state offsetWord valueWord
    (memoryCode.evaluates store) (sizeCode.evaluates store) (offsetCode.evaluates store) (valueCode.evaluates store)
    related.memory related.size related.distinct
  obtain ⟨_, nextRelated, frame⟩ := MemoryCorrespondence.mstore_preserves related offsetWord valueWord environment
  simp only [MemoryCorrespondence.mstoreResult, fits] at evaluated
  simp only [MemorySemantics.mstore, fits] at nextRelated
  exact ⟨_, evaluated, nextRelated, frame⟩

theorem hash_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size offset length : Code} {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State}
    {lengthWord touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (offsetCode : CodeValue depth environment offset (.word (Word.ofNatModulo 0)))
    (lengthCode : CodeValue depth environment length (.word lengthWord))
    (related : StateRel memoryLocation sizeLocation state store)
    (fits : MemorySemantics.touchSize? state.size (Word.ofNatModulo 0) lengthWord = some touched)
    (absorbed : KeccakSemantics.Absorb state.words (Word.ofNatModulo 0) lengthWord (List.replicate 25 Word.zero) digest) :
    ∃ next, Evaluates environment store (CreationImplementation.hash memory size offset length depth)
        (.inRight .word (.word digest)) next ∧ Frame memoryLocation sizeLocation store next := by
  obtain ⟨target, next, resultRelated, evaluated, _, frame⟩ := KeccakHashCorrespondence.hash_preserves
    (.done fits absorbed) related (memoryCode.evaluates store) (sizeCode.evaluates store)
    (offsetCode.evaluates store) (lengthCode.evaluates store)
  cases resultRelated with
  | value valueRelated =>
      cases valueRelated
      exact ⟨next, evaluated, frame⟩


theorem binary_code {depth : Nat} {environment : Environment} {left right : Code} {leftValue rightValue result : Value}
    {op : BinaryOp} (leftCode : CodeValue depth environment left leftValue)
    (rightCode : CodeValue depth environment right rightValue) (applied : op.apply leftValue rightValue = some result) :
    CodeValue depth environment (binary op left right) result :=
  fun extra store => .binary (leftCode extra store) (rightCode extra store) applied

theorem createFinish_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size encoded : Code} {memoryLocation sizeLocation : Nat} {creator nonce touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨createScratch creator nonce, touched⟩ store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store (CreationImplementation.createFinish memory size encoded depth)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame memoryLocation sizeLocation store final := by
  have lengthCode : CodeValue depth environment (binary .wordAdd (number 22) encoded) (.word (createLength nonce)) :=
    binary_code (CodeValue.number 22 depth environment) encodedCode rfl
  have total := createPreimage_length creator nonce
  have bounded := nonceBytes_length_le nonce
  have lengthValue := createLength_val creator nonce
  obtain ⟨hashTouched, fits⟩ := touch_some touched (Word.ofNatModulo 0) (createLength nonce)
    (by rw [lengthValue, val_small (by decide)]; omega)
  obtain ⟨final, evaluated, frame⟩ := hash_evaluates memoryCode sizeCode (CodeValue.number 0 depth environment)
    lengthCode related fits ((createScratch_keccak creator nonce).mp hashed)
  refine ⟨final, LanguageResult.bind_success .word evaluated (.inRight ?_), frame⟩
  exact .binary ((CodeValue.bound depth environment (.word digest)).evaluates final) .word rfl


theorem touch_byte (size : Word) (offset : Nat) (small : offset < 1000) :
    ∃ touched, MemorySemantics.touchSize? size (Word.ofNatModulo offset) (Word.ofNatModulo 1) = some touched :=
  touch_some size _ _ (by rw [val_small (by omega), val_small (by decide)]; omega)

theorem touch_word (size : Word) (offset : Nat) (small : offset < 1000) :
    ∃ touched, MemorySemantics.touchSize? size (Word.ofNatModulo offset) (Word.ofNatModulo 32) = some touched :=
  touch_some size _ _ (by rw [val_small (by omega), val_small (by decide)]; omega)

theorem createTail_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {memory size nonceCode count encoded : Code} {memoryLocation sizeLocation : Nat}
    {creator nonce touched digest : Word}
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (nonceValue : CodeValue depth environment nonceCode (.word nonce))
    (countCode : CodeValue depth environment count (.word (byteCount nonce)))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨CreationPreimage.createPrefix creator nonce, touched⟩ store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store
        (CreationImplementation.createTail memory size nonceCode count encoded depth)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame memoryLocation sizeLocation store final := by
  unfold CreationImplementation.createTail
  by_cases zero : nonce.val = 0
  · have test : (nonce == Word.ofNatModulo 0) = true := beq_iff_eq.mpr (Fin.ext (by rw [zero]; rfl))
    obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
    obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
      (CodeValue.number 22 depth environment) (CodeValue.number 128 depth environment) related fits
    have scratchSame : MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
        (Word.ofNatModulo 128) = createScratch creator nonce := by
      unfold createScratch; rw [if_pos test]
    rw [scratchSame] at related1
    obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates (memoryCode.prepend [.unit]) (sizeCode.prepend [.unit])
      (encodedCode.prepend [.unit]) related1 hashed
    exact ⟨final, .ifTrue (.binary (nonceValue.evaluates store) .word (by simp only [BinaryOp.apply, test]))
      (LanguageResult.bind_success .word evaluated1 evaluated), frame1.trans frame⟩
  · have test : (nonce == Word.ofNatModulo 0) = false :=
      beq_eq_false_iff_ne.mpr (fun same => zero (by rw [same]; rfl))
    have zeroTest : Evaluates environment store (binary .wordEq nonceCode (number 0) depth) (.bool false) store :=
      .binary (nonceValue.evaluates store) .word (by simp only [BinaryOp.apply, test])
    by_cases large : nonce > Word.ofNatModulo 127
    · obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
      obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
        (CodeValue.number 22 depth environment)
        (binary_code (op := .wordAdd) (CodeValue.number 128 depth environment) countCode rfl) related fits
      obtain ⟨wordWritten, wordFits⟩ := touch_word written 23 (by decide)
      have shiftCode := binary_code (op := .wordShl) (nonceValue.prepend [.unit])
        (binary_code (op := .wordMul)
          (binary_code (op := .wordSub) (CodeValue.number 32 (depth + 1) (.unit :: environment))
            (countCode.prepend [.unit]) rfl)
          (CodeValue.number 8 (depth + 1) (.unit :: environment)) rfl) rfl
      obtain ⟨store2, evaluated2, related2, frame2⟩ := writeWord_evaluates (memoryCode.prepend [.unit])
        (sizeCode.prepend [.unit]) (CodeValue.number 23 (depth + 1) (.unit :: environment)) shiftCode related1 wordFits
      have scratchSame : MemorySemantics.writeWord
          (MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
            ((Word.ofNatModulo 128).add (byteCount nonce))) (Word.ofNatModulo 23)
          (nonce.shiftLeft (((Word.ofNatModulo 32).sub (byteCount nonce)).mul (Word.ofNatModulo 8))) =
          createScratch creator nonce := by
        unfold createScratch; rw [if_neg (by rw [test]; decide), if_pos large]
      rw [scratchSame] at related2
      obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates ((memoryCode.prepend [.unit]).prepend [.unit])
        ((sizeCode.prepend [.unit]).prepend [.unit]) ((encodedCode.prepend [.unit]).prepend [.unit]) related2 hashed
      exact ⟨final, .ifFalse zeroTest (.ifTrue (.binary (nonceValue.evaluates store) .word
          (by simp only [BinaryOp.apply, large, decide_true]))
        (LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2 evaluated))),
        (frame1.trans frame2).trans frame⟩
    · obtain ⟨written, fits⟩ := touch_byte touched 22 (by decide)
      obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
        (CodeValue.number 22 depth environment) nonceValue related fits
      have scratchSame : MemorySemantics.writeByte (CreationPreimage.createPrefix creator nonce) (Word.ofNatModulo 22)
          nonce = createScratch creator nonce := by
        unfold createScratch; rw [if_neg (by rw [test]; decide), if_neg large]
      rw [scratchSame] at related1
      obtain ⟨final, evaluated, frame⟩ := createFinish_evaluates (memoryCode.prepend [.unit]) (sizeCode.prepend [.unit])
        (encodedCode.prepend [.unit]) related1 hashed
      exact ⟨final, .ifFalse zeroTest (.ifFalse (.binary (nonceValue.evaluates store) .word
          (by simp only [BinaryOp.apply, large, decide_false]))
        (LanguageResult.bind_success .word evaluated1 evaluated)), frame1.trans frame⟩


theorem createPrefix_evaluates {depth : Nat} {environment : Environment} {store : Store}
    {creatorCode memory size encoded rest : Code} {memoryLocation sizeLocation : Nat}
    {creator nonce empty : Word} {result : Value}
    (creatorValue : CodeValue depth environment creatorCode (.word creator))
    (memoryCode : CodeValue depth environment memory (.cellRef WordMapping.type memoryLocation))
    (sizeCode : CodeValue depth environment size (.cellRef .word sizeLocation))
    (encodedCode : CodeValue depth environment encoded (.word (encodedLength nonce)))
    (related : StateRel memoryLocation sizeLocation ⟨[], empty⟩ store)
    (continued : ∀ next touched,
      StateRel memoryLocation sizeLocation ⟨CreationPreimage.createPrefix creator nonce, touched⟩ next →
      ∃ final, Evaluates (.unit :: .unit :: .unit :: environment) next (rest (depth + 3)) result final ∧
        Frame memoryLocation sizeLocation next final) :
    ∃ final, Evaluates environment store
        (CreationImplementation.createPrefix creatorCode memory size encoded rest depth) result final ∧
      Frame memoryLocation sizeLocation store final := by
  obtain ⟨touched0, fits0⟩ := touch_byte empty 0 (by decide)
  obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryCode sizeCode
    (CodeValue.number 0 depth environment)
    (binary_code (op := .wordAdd) (CodeValue.number 213 depth environment) encodedCode rfl) related fits0
  obtain ⟨touched1, fits1⟩ := touch_byte touched0 1 (by decide)
  obtain ⟨store2, evaluated2, related2, frame2⟩ := writeByte_evaluates (memoryCode.prepend [.unit])
    (sizeCode.prepend [.unit]) (CodeValue.number 1 (depth + 1) (.unit :: environment))
    (CodeValue.number 148 (depth + 1) (.unit :: environment)) related1 fits1
  obtain ⟨touched2, fits2⟩ := touch_word touched1 2 (by decide)
  have addressCode := binary_code (op := .wordShl)
    (binary_code (op := .wordAnd) ((creatorValue.prepend [.unit]).prepend [.unit])
      (CodeValue.number (2 ^ 160 - 1) (depth + 1 + 1) (.unit :: .unit :: environment)) rfl)
    (CodeValue.number 96 (depth + 1 + 1) (.unit :: .unit :: environment)) rfl
  obtain ⟨store3, evaluated3, related3, frame3⟩ := writeWord_evaluates ((memoryCode.prepend [.unit]).prepend [.unit])
    ((sizeCode.prepend [.unit]).prepend [.unit]) (CodeValue.number 2 (depth + 1 + 1) (.unit :: .unit :: environment))
    addressCode related2 fits2
  obtain ⟨final, evaluated, frame⟩ := continued store3 touched2 related3
  exact ⟨final, LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2
    (LanguageResult.bind_success .word evaluated3 evaluated)), ((frame1.trans frame2).trans frame3).trans frame⟩

/-- Fresh scratch cells keep every existing cell when only they change. -/
theorem scratch_retains {store final : Store} {first second : Value}
    (frame : Frame store.length (store.length + 1) (store ++ [first, second]) final) : StoreRetains store final := by
  constructor
  · have := frame.length
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  · intro location bound
    have found : (store ++ [first, second]).read? location = some store[location] := by
      show (store ++ [first, second])[location]? = some store[location]
      rw [List.getElem?_append_left bound, List.getElem?_eq_getElem bound]
    rw [frame.read location _ (by omega) (by omega) found]
    exact (List.getElem?_eq_getElem bound).symm

theorem createAddress_evaluates {environment : Environment} {store : Store}
    {creatorExpr nonceExpr : Core.Expr} {creator nonce digest : Word}
    (evaluated : Evaluates environment store (.pair creatorExpr nonceExpr) (.pair (.word creator) (.word nonce)) store)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.createPreimage creator nonce) digest) :
    ∃ final, Evaluates environment store (Creation.createAddress creatorExpr nonceExpr)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧ StoreRetains store final := by
  rw [CreationImplementation.createAddress_eq]
  let pairValue : Value := .pair (.word creator) (.word nonce)
  have inputs : CodeValue 0 (pairValue :: environment) (fun depth => .var depth)
      (bundleValues [.word creator, .word nonce]) := by
    intro extra store
    exact .var (by simp [pairValue, bundleValues])
  have creatorCode := inputs.part (index := 0) rfl
  have nonceCode := inputs.part (index := 1) rfl
  let count := byteCount nonce
  have countEvaluated : Evaluates (pairValue :: environment) store
      (binary .wordSub (number 32)
        (binary .wordDiv (fun depth => .unary .wordClz (part 1 2 (fun depth => .var depth) depth)) (number 8)) 0)
      (.word count) store :=
    .binary .word (.binary (.unary (nonceCode.evaluates store) rfl) .word rfl) rfl
  have countValue := CodeValue.bound 0 (pairValue :: environment) (.word count)
  have encodedEvaluated : Evaluates (.word count :: pairValue :: environment) store
      (choose (binary .wordGt (part 1 2 (fun depth => .var depth)) (number 127))
        (binary .wordAdd (fun here => .var (here - 0 - 1)) (number 1)) (number 1) 1)
      (.word (encodedLength nonce)) store := by
    unfold encodedLength
    by_cases large : nonce > Word.ofNatModulo 127
    · rw [if_pos large]
      exact .ifTrue (.binary ((nonceCode.prepend [.word count]).evaluates store) .word
        (by simp only [BinaryOp.apply, large, decide_true])) (.binary (countValue.evaluates store) .word rfl)
    · rw [if_neg large]
      exact .ifFalse (.binary ((nonceCode.prepend [.word count]).evaluates store) .word
        (by simp only [BinaryOp.apply, large, decide_false])) .word
  let encoded := encodedLength nonce
  have encodedValue := CodeValue.bound 1 (.word count :: pairValue :: environment) (.word encoded)
  let memoryRef := Value.cellRef WordMapping.type store.length
  let sizeRef := Value.cellRef .word (store.length + 1)
  let allocated : Store := store ++ [WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have scratchRelated : StateRel store.length (store.length + 1) ⟨[], Word.ofNatModulo 0⟩ allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  let E2 : Environment := .word encoded :: .word count :: pairValue :: environment
  have memoryValue := CodeValue.bound 2 E2 memoryRef
  have sizeValue := CodeValue.bound 3 (memoryRef :: E2) sizeRef
  obtain ⟨final, prefixEvaluated, frame⟩ := createPrefix_evaluates
    (rest := CreationImplementation.createTail (fun here => .var (here - 2 - 1)) (fun here => .var (here - 3 - 1))
      (part 1 2 (fun depth => .var depth)) (fun here => .var (here - 0 - 1)) (fun here => .var (here - 1 - 1)))
    (creatorCode.prepend [sizeRef, memoryRef, .word encoded, .word count]) (memoryValue.prepend [sizeRef]) sizeValue
    (encodedValue.prepend [sizeRef, memoryRef]) scratchRelated
    (fun next touched related => createTail_evaluates
      (((memoryValue.prepend [sizeRef]).prepend [.unit, .unit, .unit]))
      ((sizeValue.prepend [.unit, .unit, .unit]))
      ((nonceCode.prepend [sizeRef, memoryRef, .word encoded, .word count]).prepend [.unit, .unit, .unit])
      ((countValue.prepend [sizeRef, memoryRef, .word encoded]).prepend [.unit, .unit, .unit])
      ((encodedValue.prepend [sizeRef, memoryRef]).prepend [.unit, .unit, .unit]) related hashed)
  refine ⟨final, .letE evaluated (.letE countEvaluated (.letE encodedEvaluated ?_)), scratch_retains frame⟩
  apply Evaluates.letE (bodyStore := store ++ [WordMapping.encode []])
  · exact .newCell (.construct .unit)
  · apply Evaluates.letE (bodyStore := allocated)
    · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
        (Evaluates.newCell (elementType := .word) (environment := memoryRef :: E2)
          (initialStore := store ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word (Word.ofNatModulo 0)))
    · exact prefixEvaluated


/-- Fresh scratch cells keep every cell that an earlier frame keeps. -/
theorem scratch_frame {memoryLocation sizeLocation : Nat} {initial store final : Store} {first second : Value}
    (earlier : Frame memoryLocation sizeLocation initial store)
    (later : Frame store.length (store.length + 1) (store ++ [first, second]) final) :
    Frame memoryLocation sizeLocation initial final := by
  have retained := scratch_retains later
  refine ⟨Nat.le_trans earlier.length retained.length_le, ?_⟩
  intro location value memory size found
  have kept := earlier.read location value memory size found
  have bound := (List.getElem?_eq_some_iff.mp kept).1
  rw [retained.read location bound]
  exact kept

theorem create2Address_evaluates {environment : Environment} {store : Store}
    {memoryExpr sizeExpr creatorExpr saltExpr offsetExpr lengthExpr : Core.Expr}
    {initLocation initSizeLocation : Nat} {initCode : MemorySemantics.Entries}
    {initSize creator salt length initHash digest : Word}
    (evaluated : Evaluates environment store (bundle [memoryExpr, sizeExpr, creatorExpr, saltExpr, offsetExpr, lengthExpr])
      (bundleValues [.cellRef WordMapping.type initLocation, .cellRef .word initSizeLocation, .word creator,
        .word salt, .word (Word.ofNatModulo 0), .word length]) store)
    (initRelated : StateRel initLocation initSizeLocation ⟨initCode, initSize⟩ store)
    (bounded : length.val ≤ 49152)
    (initHashed : KeccakSemantics.Absorb initCode Word.zero length (List.replicate 25 Word.zero) initHash)
    (hashed : CreationAddressSemantics.Keccak (CreationAddressSemantics.create2Preimage creator salt initHash) digest) :
    ∃ final, Evaluates environment store
        (Creation.create2Address memoryExpr sizeExpr creatorExpr saltExpr offsetExpr lengthExpr)
        (.inRight .word (.word (CreationAddressSemantics.address digest))) final ∧
      Frame initLocation initSizeLocation store final := by
  rw [CreationImplementation.create2Address_eq]
  let argumentValues : List Value := [.cellRef WordMapping.type initLocation, .cellRef .word initSizeLocation,
    .word creator, .word salt, .word (Word.ofNatModulo 0), .word length]
  have inputs : CodeValue 0 (bundleValues argumentValues :: environment) (fun depth => .var depth)
      (bundleValues argumentValues) := by
    intro extra store
    exact .var (by simp)
  have input (index : Nat) {value : Value} (found : argumentValues[index]? = some value) :=
    inputs.part (index := index) found
  obtain ⟨initTouched, initFits⟩ := touch_some initSize (Word.ofNatModulo 0) length
    (by rw [val_small (by decide)]; omega)
  obtain ⟨hashStore, hashEvaluated, hashFrame⟩ := hash_evaluates (input 0 rfl) (input 1 rfl) (input 4 rfl)
    (input 5 rfl) initRelated initFits initHashed
  let E1 : Environment := .word initHash :: bundleValues argumentValues :: environment
  have hashValue := CodeValue.bound 0 (bundleValues argumentValues :: environment) (.word initHash)
  let memoryRef := Value.cellRef WordMapping.type hashStore.length
  let sizeRef := Value.cellRef .word (hashStore.length + 1)
  let allocated : Store := hashStore ++ [WordMapping.encode [], .word (Word.ofNatModulo 0)]
  have scratchRelated : StateRel hashStore.length (hashStore.length + 1) ⟨[], Word.ofNatModulo 0⟩ allocated := by
    refine ⟨by omega, ?_, ?_⟩ <;> simp [allocated, Store.read?]
  have memoryValue := (CodeValue.bound 1 E1 memoryRef).prepend [sizeRef]
  have sizeValue := CodeValue.bound 2 (memoryRef :: E1) sizeRef
  let E3 : Environment := sizeRef :: memoryRef :: E1
  obtain ⟨touched0, fits0⟩ := touch_byte (Word.ofNatModulo 0) 0 (by decide)
  obtain ⟨store1, evaluated1, related1, frame1⟩ := writeByte_evaluates memoryValue sizeValue
    (CodeValue.number 0 3 E3) (CodeValue.number 255 3 E3) scratchRelated fits0
  obtain ⟨touched1, fits1⟩ := touch_word touched0 1 (by decide)
  have addressCode := binary_code (op := .wordShl)
    (binary_code (op := .wordAnd) ((input 2 rfl).prepend [.unit, sizeRef, memoryRef, .word initHash])
      (CodeValue.number (2 ^ 160 - 1) 4 (.unit :: E3)) rfl)
    (CodeValue.number 96 4 (.unit :: E3)) rfl
  obtain ⟨store2, evaluated2, related2, frame2⟩ := writeWord_evaluates (memoryValue.prepend [.unit])
    (sizeValue.prepend [.unit]) (CodeValue.number 1 4 (.unit :: E3)) addressCode related1 fits1
  obtain ⟨touched2, fits2⟩ := touch_word touched1 21 (by decide)
  obtain ⟨store3, evaluated3, related3, frame3⟩ := writeWord_evaluates ((memoryValue.prepend [.unit]).prepend [.unit])
    ((sizeValue.prepend [.unit]).prepend [.unit]) (CodeValue.number 21 5 (.unit :: .unit :: E3))
    ((input 3 rfl).prepend [.unit, .unit, sizeRef, memoryRef, .word initHash]) related2 fits2
  obtain ⟨touched3, fits3⟩ := touch_word touched2 53 (by decide)
  obtain ⟨store4, evaluated4, related4, frame4⟩ := writeWord_evaluates
    (((memoryValue.prepend [.unit]).prepend [.unit]).prepend [.unit])
    (((sizeValue.prepend [.unit]).prepend [.unit]).prepend [.unit])
    (CodeValue.number 53 6 (.unit :: .unit :: .unit :: E3))
    (hashValue.prepend [.unit, .unit, .unit, sizeRef, memoryRef]) related3 fits3
  obtain ⟨touched4, fits4⟩ := touch_some touched3 (Word.ofNatModulo 0) (Word.ofNatModulo 85)
    (by rw [val_small (by decide), val_small (by decide)]; decide)
  obtain ⟨store5, evaluated5, frame5⟩ := hash_evaluates
    ((((memoryValue.prepend [.unit]).prepend [.unit]).prepend [.unit]).prepend [.unit])
    ((((sizeValue.prepend [.unit]).prepend [.unit]).prepend [.unit]).prepend [.unit])
    (CodeValue.number 0 7 (.unit :: .unit :: .unit :: .unit :: E3))
    (CodeValue.number 85 7 (.unit :: .unit :: .unit :: .unit :: E3)) related4 fits4
    ((create2Scratch_keccak creator salt initHash).mp hashed)
  refine ⟨store5, .letE evaluated (LanguageResult.bind_success .word hashEvaluated ?_),
    scratch_frame hashFrame ((((frame1.trans frame2).trans frame3).trans frame4).trans frame5)⟩
  apply Evaluates.letE (bodyStore := hashStore ++ [WordMapping.encode []])
  · exact .newCell (.construct .unit)
  · apply Evaluates.letE (bodyStore := allocated)
    · simpa only [allocated, List.length_append, List.length_cons, List.length_nil, List.append_assoc,
        List.cons_append, List.nil_append, CodeBuilder.allocate, CodeBuilder.number, CodeBuilder.constant] using
        (Evaluates.newCell (elementType := .word) (environment := memoryRef :: E1)
          (initialStore := hashStore ++ [WordMapping.encode []]) Evaluates.word (initialValue := .word (Word.ofNatModulo 0)))
    · exact LanguageResult.bind_success .word evaluated1 (LanguageResult.bind_success .word evaluated2
        (LanguageResult.bind_success .word evaluated3 (LanguageResult.bind_success .word evaluated4
          (LanguageResult.bind_success .word evaluated5 (.inRight (.binary
            ((CodeValue.bound 7 (.unit :: .unit :: .unit :: .unit :: E3) (.word digest)).evaluates store5) .word rfl))))))

end Solcore.Frontend.RustHull.CreationAddressCorrespondence
