import Solcore.Frontend.RustHull.MemorySemantics
import Solcore.Frontend.RustHull.Memory
import Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport

/-! Concrete memory operations preserve the independent packed-word model.
The final store retains every administrative mapping-helper allocation. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.MemoryCorrespondence
open Core

theorem lookup_eq (entries : MemorySemantics.Entries) (key : Word) :
    MemorySemantics.lookup key entries = WordMapping.lookupEntries key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [MemorySemantics.lookup, WordMapping.lookupEntries, ih]

theorem insert_eq (entries : MemorySemantics.Entries) (key value : Word) :
    MemorySemantics.insert key value entries = WordMapping.insertEntries key value entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [MemorySemantics.insert, WordMapping.insertEntries, ih]

theorem msize_evaluates {environment : Environment} {initial store : Store}
    {reference : Core.Expr} {location : Nat} {size : Word}
    (evaluated : Evaluates environment initial reference (.cellRef .word location) store)
    (read : store.read? location = some (.word size)) :
    Evaluates environment initial (Memory.msize reference) (.inRight .word (.word size)) store :=
  .letE evaluated (.inRight (.loadCell (.var rfl) read))

def touchStore (store : Store) (location : Nat) (size offset length : Word) : Store :=
  if length == Word.zero then store
  else
    let last := offset.add length
    if offset > last then store
    else if last > Word.ofNatModulo (wordModulus - 32) then store
    else if MemorySemantics.rounded last > size then
      store.set location (.word (MemorySemantics.rounded last))
    else store

def touchResult (size offset length : Word) : Value :=
  match MemorySemantics.touchSize? size offset length with
  | none => .inLeft .unit (.word Memory.overflowReason)
  | some _ => .inRight .word .unit

theorem touch_evaluates {environment : Environment} {initial first second store : Store}
    {reference offsetExpr lengthExpr : Core.Expr} {location : Nat} {size offset length : Word}
    (referenceEvaluated : Evaluates environment initial reference (.cellRef .word location) first)
    (offsetEvaluated : Evaluates environment first offsetExpr (.word offset) second)
    (lengthEvaluated : Evaluates environment second lengthExpr (.word length) store)
    (read : store.read? location = some (.word size)) :
    Evaluates environment initial (Memory.touch reference offsetExpr lengthExpr)
      (touchResult size offset length) (touchStore store location size offset length) := by
  apply Evaluates.letE (.pair referenceEvaluated (.pair offsetEvaluated lengthEvaluated))
  by_cases empty : length == Word.zero
  · simp only [touchResult, MemorySemantics.touchSize?, touchStore, empty, if_true]
    apply Evaluates.ifTrue
    · exact .binary (.second (.second (.var rfl))) .word (by simpa only [BinaryOp.apply, show Word.ofNatModulo 0 = Word.zero from rfl] using congrArg some (congrArg Value.bool empty))
    · exact .inRight .unit
  · simp only [touchResult, MemorySemantics.touchSize?, touchStore, empty]
    apply Evaluates.ifFalse
    · apply Evaluates.binary (.second (.second (.var rfl))) .word
      simpa only [BinaryOp.apply, show Word.ofNatModulo 0 = Word.zero from rfl] using congrArg some (congrArg Value.bool (Bool.eq_false_iff.mpr empty))
    · apply Evaluates.letE (.binary (.first (.second (.var rfl))) (.second (.second (.var rfl))) rfl)
      by_cases wrapped : offset > offset.add length
      · simp only [wrapped, if_true]
        exact .ifTrue (.binary (.first (.second (.var rfl))) (.var rfl) (by simp [BinaryOp.apply, wrapped])) (.inLeft .word)
      · simp only [wrapped, if_false]
        apply Evaluates.ifFalse (.binary (.first (.second (.var rfl))) (.var rfl) (by simp [BinaryOp.apply, wrapped]))
        by_cases overflow : offset.add length > Word.ofNatModulo (wordModulus - 32)
        · simp only [overflow, if_true]
          exact .ifTrue (.binary (.var rfl) .word (by simp [BinaryOp.apply, overflow])) (.inLeft .word)
        · simp only [overflow, if_false]
          apply Evaluates.ifFalse (.binary (.var rfl) .word (by simp [BinaryOp.apply, overflow]))
          apply Evaluates.letE (.binary (.binary (.binary (.var rfl) .word rfl) .word rfl) .word rfl)
          apply Evaluates.inRight
          by_cases expands : MemorySemantics.rounded (offset.add length) > size
          · simp only [expands, if_true]
            apply Evaluates.ifTrue (.binary (.var rfl) (.loadCell (.first (.var rfl)) read) (by change some (Value.bool (decide (MemorySemantics.rounded (offset.add length) > size))) = _; simp only [expands, decide_true]))
            apply Evaluates.storeCell (.first (.var rfl)) read (.var rfl)
            exact Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp read).1, rfl⟩
          · simp only [expands, if_false]
            exact .ifFalse (.binary (.var rfl) (.loadCell (.first (.var rfl)) read) (by change some (Value.bool (decide (MemorySemantics.rounded (offset.add length) > size))) = _; simp only [expands, decide_false])) .unit

def lookupStore (store : Store) (entries : MemorySemantics.Entries) (key : Word)
    (environment : Environment) : Store :=
  WordMapping.installedStore store WordMapping.lookupParameter .word WordMapping.lookupBody
    (.pair (WordMapping.encode entries) (.word key)) environment

def readWordStore (store : Store) (entries : MemorySemantics.Entries) (offset : Word)
    (environment : Environment) : Store :=
  let packet := Value.pair (WordMapping.encode entries) (.word offset)
  let firstStore := lookupStore store entries (MemorySemantics.index offset) (packet :: environment)
  if MemorySemantics.position offset == Word.zero then firstStore
  else if MemorySemantics.index offset == Word.ofNatModulo ((wordModulus - 1) / 32) then firstStore
  else lookupStore firstStore entries ((MemorySemantics.index offset).add (Word.ofNatModulo 1))
    (.word (MemorySemantics.lookup (MemorySemantics.index offset) entries) :: packet :: environment)

theorem readMemoryWord_evaluates {environment : Environment} {initial middle store : Store}
    {mapping offsetExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset : Word)
    (mappingEvaluated : Evaluates environment initial mapping (WordMapping.encode entries) middle)
    (offsetEvaluated : Evaluates environment middle offsetExpr (.word offset) store) :
    Evaluates environment initial (Memory.readMemoryWord mapping offsetExpr)
      (.inRight .word (.word (MemorySemantics.readWord entries offset)))
      (readWordStore store entries offset environment) := by
  apply Evaluates.letE (.pair mappingEvaluated offsetEvaluated)
  apply LanguageResult.bind_success .word
    (WordMapping.lookup_evaluates entries (MemorySemantics.index offset)
      (.first (.var rfl)) (.binary (.second (.var rfl)) .word rfl))
  by_cases aligned : MemorySemantics.position offset == Word.zero
  · simp only [MemorySemantics.readWord, readWordStore, aligned, if_true, lookup_eq]
    apply Evaluates.ifTrue
    · apply Evaluates.binary (.binary (.second (.var rfl)) .word rfl) .word
      change some (Value.bool (MemorySemantics.position offset == Word.zero)) = _
      rw [aligned]
    · exact .inRight (.var rfl)
  · simp only [MemorySemantics.readWord, readWordStore, aligned, lookup_eq]
    apply Evaluates.ifFalse
    · apply Evaluates.binary (.binary (.second (.var rfl)) .word rfl) .word
      change some (Value.bool (MemorySemantics.position offset == Word.zero)) = _
      rw [Bool.eq_false_iff.mpr aligned]
    · by_cases last : MemorySemantics.index offset == Word.ofNatModulo ((wordModulus - 1) / 32)
      · simp only [last, if_true]
        apply LanguageResult.bind_success .word
        · apply Evaluates.ifTrue
          · apply Evaluates.binary (.binary (.second (.var rfl)) .word rfl) .word
            change some (Value.bool (MemorySemantics.index offset == Word.ofNatModulo ((wordModulus - 1) / 32))) = _
            rw [last]
          · exact .inRight .word
        · exact .inRight (.binary
            (.binary (.var rfl) (.binary (.binary (.second (.var rfl)) .word rfl) .word rfl) rfl)
            (.binary (.var rfl) (.binary .word (.binary (.binary (.second (.var rfl)) .word rfl) .word rfl) rfl) rfl) rfl)
      · simp only [last]
        apply LanguageResult.bind_success .word
        · apply Evaluates.ifFalse
          · apply Evaluates.binary (.binary (.second (.var rfl)) .word rfl) .word
            change some (Value.bool (MemorySemantics.index offset == Word.ofNatModulo ((wordModulus - 1) / 32))) = _
            rw [Bool.eq_false_iff.mpr last]
          · exact WordMapping.lookup_evaluates entries
              ((MemorySemantics.index offset).add (Word.ofNatModulo 1))
              (.first (.var rfl)) (.binary (.binary (.second (.var rfl)) .word rfl) .word rfl)
        · exact .inRight (.binary
            (.binary (.var rfl) (.binary (.binary (.second (.var rfl)) .word rfl) .word rfl) rfl)
            (.binary (.var rfl) (.binary .word (.binary (.binary (.second (.var rfl)) .word rfl) .word rfl) rfl) rfl) rfl)

def insertStore (store : Store) (entries : MemorySemantics.Entries) (key value : Word)
    (environment : Environment) : Store :=
  WordMapping.installedStore store WordMapping.insertParameter WordMapping.type WordMapping.insertBody
    (.pair (WordMapping.encode entries) (.pair (.word key) (.word value))) environment

def writeWordStore (store : Store) (entries : MemorySemantics.Entries) (offset value : Word)
    (environment : Environment) : Store :=
  let packet := Value.pair (WordMapping.encode entries) (.pair (.word offset) (.word value))
  let key := MemorySemantics.index offset
  if MemorySemantics.position offset == Word.zero then insertStore store entries key value (packet :: environment)
  else
    let distance := MemorySemantics.shift offset
    let mask := (Word.ofNatModulo (wordModulus - 1)).shiftRight distance
    let first := MemorySemantics.lookup key entries
    let firstValue := (first.bitAnd mask.bitNot).bitOr (value.shiftRight distance)
    let firstEnvironment := Value.word mask :: .word distance :: packet :: environment
    let firstStore := lookupStore store entries key firstEnvironment
    let secondStore := insertStore firstStore entries key firstValue (.word first :: firstEnvironment)
    let updated := MemorySemantics.insert key firstValue entries
    let next := key.add (Word.ofNatModulo 1)
    let second := MemorySemantics.lookup next updated
    let secondValue := (second.bitAnd mask).bitOr (value.shiftLeft ((Word.ofNatModulo 256).sub distance))
    let secondEnvironment := WordMapping.encode updated :: .word first :: firstEnvironment
    let thirdStore := lookupStore secondStore updated next secondEnvironment
    insertStore thirdStore updated next secondValue (.word second :: secondEnvironment)

theorem writeMemoryWord_evaluates {environment : Environment} {initial first second store : Store}
    {mapping offsetExpr valueExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset value : Word)
    (mappingEvaluated : Evaluates environment initial mapping (WordMapping.encode entries) first)
    (offsetEvaluated : Evaluates environment first offsetExpr (.word offset) second)
    (valueEvaluated : Evaluates environment second valueExpr (.word value) store) :
    Evaluates environment initial (Memory.writeMemoryWord mapping offsetExpr valueExpr)
      (.inRight .word (WordMapping.encode (MemorySemantics.writeWord entries offset value)))
      (writeWordStore store entries offset value environment) := by
  apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated valueEvaluated))
  by_cases aligned : MemorySemantics.position offset == Word.zero
  · simp only [MemorySemantics.writeWord, writeWordStore, aligned, if_true, insert_eq]
    apply Evaluates.ifTrue
    · apply Evaluates.binary (.binary (.first (.second (.var rfl))) .word rfl) .word
      change some (Value.bool (MemorySemantics.position offset == Word.zero)) = _
      rw [aligned]
    · exact WordMapping.insert_evaluates entries (MemorySemantics.index offset) value
        (.first (.var rfl)) (.binary (.first (.second (.var rfl))) .word rfl) (.second (.second (.var rfl)))
  · simp only [MemorySemantics.writeWord, writeWordStore, aligned, lookup_eq, insert_eq]
    apply Evaluates.ifFalse
    · apply Evaluates.binary (.binary (.first (.second (.var rfl))) .word rfl) .word
      change some (Value.bool (MemorySemantics.position offset == Word.zero)) = _
      rw [Bool.eq_false_iff.mpr aligned]
    · apply Evaluates.letE (.binary (.binary (.first (.second (.var rfl))) .word rfl) .word rfl)
      apply Evaluates.letE (.binary .word (.var rfl) rfl)
      apply LanguageResult.bind_success WordMapping.type
        (WordMapping.lookup_evaluates entries (MemorySemantics.index offset)
          (.first (.var rfl)) (.binary (.first (.second (.var rfl))) .word rfl))
      apply LanguageResult.bind_success WordMapping.type
        (WordMapping.insert_evaluates entries (MemorySemantics.index offset) _
          (.first (.var rfl)) (.binary (.first (.second (.var rfl))) .word rfl)
          (.binary (.binary (.var rfl) (.unary (.var rfl) rfl) rfl)
            (.binary (.second (.second (.var rfl))) (.var rfl) rfl) rfl))
      apply LanguageResult.bind_success WordMapping.type
        (WordMapping.lookup_evaluates _ ((MemorySemantics.index offset).add (Word.ofNatModulo 1))
          (.var rfl) (.binary (.binary (.first (.second (.var rfl))) .word rfl) .word rfl))
      exact WordMapping.insert_evaluates _ ((MemorySemantics.index offset).add (Word.ofNatModulo 1)) _
        (.var rfl) (.binary (.binary (.first (.second (.var rfl))) .word rfl) .word rfl)
        (.binary (.binary (.var rfl) (.var rfl) rfl)
          (.binary (.second (.second (.var rfl))) (.binary .word (.var rfl) rfl) rfl) rfl)

theorem touchStore_length (store : Store) (location : Nat) (size offset length : Word) :
    (touchStore store location size offset length).length = store.length := by
  unfold touchStore
  dsimp only
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> simp

theorem touchStore_other (store : Store) {location other : Nat}
    (different : other ≠ location) (size offset length : Word) :
    (touchStore store location size offset length).read? other = store.read? other := by
  unfold touchStore
  dsimp only
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  simp [Store.read?, Ne.symm different]

theorem touchStore_failure {store : Store} {location : Nat} {size offset length : Word}
    (failed : MemorySemantics.touchSize? size offset length = none) :
    touchStore store location size offset length = store := by
  unfold MemorySemantics.touchSize? at failed
  unfold touchStore
  dsimp only at failed ⊢
  split at failed <;> simp_all

theorem touchStore_read {store : Store} {location : Nat} {size offset length updated : Word}
    (read : store.read? location = some (.word size))
    (touched : MemorySemantics.touchSize? size offset length = some updated) :
    (touchStore store location size offset length).read? location = some (.word updated) := by
  by_cases empty : length == Word.zero
  · simp only [MemorySemantics.touchSize?, empty, if_true, Option.some.injEq] at touched
    cases touched
    simpa only [touchStore, empty, if_true] using read
  · by_cases wrapped : offset > offset.add length
    · simp [MemorySemantics.touchSize?, empty, wrapped] at touched
    · by_cases overflow : offset.add length > Word.ofNatModulo (wordModulus - 32)
      · simp [MemorySemantics.touchSize?, empty, wrapped, overflow] at touched
      · by_cases expands : MemorySemantics.rounded (offset.add length) > size
        · simp [MemorySemantics.touchSize?, empty, wrapped, overflow, expands] at touched
          cases touched
          have bound := (List.getElem?_eq_some_iff.mp read).1
          simp [touchStore, empty, wrapped, overflow, expands]
          simp [Store.read?, bound]
        · simp [MemorySemantics.touchSize?, empty, wrapped, overflow, expands] at touched
          cases touched
          simpa [touchStore, empty, wrapped, overflow, expands] using read

theorem readWordStore_extension (store : Store) (entries : MemorySemantics.Entries)
    (offset : Word) (environment : Environment) :
    ∃ suffix, readWordStore store entries offset environment = store ++ suffix := by
  unfold readWordStore
  split
  · exact ⟨[_], rfl⟩
  · split
    · exact ⟨[_], rfl⟩
    · simp only [lookupStore, WordMapping.installedStore, List.append_assoc]
      exact ⟨_, rfl⟩

theorem writeWordStore_extension (store : Store) (entries : MemorySemantics.Entries)
    (offset value : Word) (environment : Environment) :
    ∃ suffix, writeWordStore store entries offset value environment = store ++ suffix := by
  unfold writeWordStore
  split
  · exact ⟨[_], rfl⟩
  · simp only [lookupStore, insertStore, WordMapping.installedStore, List.append_assoc]
    exact ⟨_, rfl⟩

def mloadResult (state : MemorySemantics.State) (offset : Word) : Value :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => .inLeft .word (.word Memory.overflowReason)
  | some _ => .inRight .word (.word (MemorySemantics.readWord state.words offset))

def mloadStore (store : Store) (memoryLocation sizeLocation : Nat)
    (state : MemorySemantics.State) (offset : Word) (environment : Environment) : Store :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => store
  | some _ =>
      let packet := Value.pair (.cellRef WordMapping.type memoryLocation)
        (.pair (.cellRef .word sizeLocation) (.word offset))
      readWordStore (touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)) state.words offset
        (WordMapping.encode state.words :: .unit :: packet :: environment)

theorem mload_evaluates {environment : Environment} {initial first second store : Store}
    {memoryReference sizeReference offsetExpr : Core.Expr} {memoryLocation sizeLocation : Nat}
    (state : MemorySemantics.State) (offset : Word)
    (memoryEvaluated : Evaluates environment initial memoryReference (.cellRef WordMapping.type memoryLocation) first)
    (sizeEvaluated : Evaluates environment first sizeReference (.cellRef .word sizeLocation) second)
    (offsetEvaluated : Evaluates environment second offsetExpr (.word offset) store)
    (memoryRead : store.read? memoryLocation = some (WordMapping.encode state.words))
    (sizeRead : store.read? sizeLocation = some (.word state.size))
    (different : memoryLocation ≠ sizeLocation) :
    Evaluates environment initial (Memory.mload memoryReference sizeReference offsetExpr)
      (mloadResult state offset) (mloadStore store memoryLocation sizeLocation state offset environment) := by
  apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated offsetEvaluated))
  have touched := touch_evaluates
    (environment := Value.pair (.cellRef WordMapping.type memoryLocation)
      (.pair (.cellRef .word sizeLocation) (.word offset)) :: environment)
    (reference := .first (.second (.var 0))) (offsetExpr := .second (.second (.var 0)))
    (.first (.second (.var rfl))) (.second (.second (.var rfl)))
    (Evaluates.word (value := Word.ofNatModulo 32)) sizeRead
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none =>
      simp only [touchResult, checked, touchStore_failure checked] at touched
      simp only [mloadResult, mloadStore, checked]
      exact LanguageResult.bind_failure .word touched
  | some size =>
      simp only [touchResult, checked] at touched
      simp only [mloadResult, mloadStore, checked]
      apply LanguageResult.bind_success .word touched
      apply Evaluates.letE (.loadCell (.first (.var rfl))
        ((touchStore_other store different _ _ _).trans memoryRead))
      exact readMemoryWord_evaluates state.words offset (.var rfl) (.second (.second (.var rfl)))

def mstoreResult (state : MemorySemantics.State) (offset : Word) : Value :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => .inLeft .unit (.word Memory.overflowReason)
  | some _ => .inRight .word .unit

def mstoreStore (store : Store) (memoryLocation sizeLocation : Nat)
    (state : MemorySemantics.State) (offset value : Word) (environment : Environment) : Store :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => store
  | some _ =>
      let packet := Value.pair (.cellRef WordMapping.type memoryLocation)
        (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value)))
      let touched := touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)
      let written := writeWordStore touched state.words offset value
        (WordMapping.encode state.words :: .unit :: packet :: environment)
      written.set memoryLocation (WordMapping.encode (MemorySemantics.writeWord state.words offset value))

theorem mstore_evaluates {environment : Environment} {initial first second third store : Store}
    {memoryReference sizeReference offsetExpr valueExpr : Core.Expr} {memoryLocation sizeLocation : Nat}
    (state : MemorySemantics.State) (offset value : Word)
    (memoryEvaluated : Evaluates environment initial memoryReference (.cellRef WordMapping.type memoryLocation) first)
    (sizeEvaluated : Evaluates environment first sizeReference (.cellRef .word sizeLocation) second)
    (offsetEvaluated : Evaluates environment second offsetExpr (.word offset) third)
    (valueEvaluated : Evaluates environment third valueExpr (.word value) store)
    (memoryRead : store.read? memoryLocation = some (WordMapping.encode state.words))
    (sizeRead : store.read? sizeLocation = some (.word state.size))
    (different : memoryLocation ≠ sizeLocation) :
    Evaluates environment initial (Memory.mstore memoryReference sizeReference offsetExpr valueExpr)
      (mstoreResult state offset) (mstoreStore store memoryLocation sizeLocation state offset value environment) := by
  apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated valueEvaluated)))
  have touched := touch_evaluates
    (environment := Value.pair (.cellRef WordMapping.type memoryLocation)
      (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
    (reference := .first (.second (.var 0))) (offsetExpr := .first (.second (.second (.var 0))))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (Evaluates.word (value := Word.ofNatModulo 32)) sizeRead
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none =>
      simp only [touchResult, checked, touchStore_failure checked] at touched
      simp only [mstoreResult, mstoreStore, checked]
      exact LanguageResult.bind_failure .unit touched
  | some size =>
      simp only [touchResult, checked] at touched
      simp only [mstoreResult, mstoreStore, checked]
      have memoryAfterTouch := (touchStore_other store different state.size offset (Word.ofNatModulo 32)).trans memoryRead
      apply LanguageResult.bind_success .unit touched
      apply Evaluates.letE (.loadCell (.first (.var rfl)) memoryAfterTouch)
      apply LanguageResult.bind_success .unit
        (writeMemoryWord_evaluates state.words offset value (.var rfl)
          (.first (.second (.second (.var rfl)))) (.second (.second (.second (.var rfl)))))
      obtain ⟨suffix, extended⟩ := writeWordStore_extension
        (touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)) state.words offset value
        (WordMapping.encode state.words :: .unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
          (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
      have bound := (List.getElem?_eq_some_iff.mp memoryAfterTouch).1
      have memoryAfterWrite : (writeWordStore
          (touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)) state.words offset value
          (WordMapping.encode state.words :: .unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
            (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)).read?
            memoryLocation = some (WordMapping.encode state.words) := by
        rw [extended]
        simpa only [Store.read?, List.getElem?_append_left bound] using memoryAfterTouch
      apply Evaluates.inRight
      apply Evaluates.storeCell (.first (.var rfl)) memoryAfterWrite (.var rfl)
      exact Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp memoryAfterWrite).1, rfl⟩

structure StateRel (memoryLocation sizeLocation : Nat) (state : MemorySemantics.State)
    (store : Store) : Prop where
  distinct : memoryLocation ≠ sizeLocation
  memory : store.read? memoryLocation = some (WordMapping.encode state.words)
  size : store.read? sizeLocation = some (.word state.size)

/-- Memory effects may update their two cells and append helper closures.
Every existing cell outside those locations retains its exact value. -/
structure Frame (memoryLocation sizeLocation : Nat) (initial final : Store) : Prop where
  length : initial.length ≤ final.length
  read : ∀ location value, location ≠ memoryLocation → location ≠ sizeLocation →
    initial.read? location = some value → final.read? location = some value

theorem Frame.refl (memoryLocation sizeLocation : Nat) (store : Store) :
    Frame memoryLocation sizeLocation store store := ⟨Nat.le_refl _, fun _ _ _ _ found => found⟩

theorem Frame.trans {memoryLocation sizeLocation : Nat} {initial middle final : Store}
    (first : Frame memoryLocation sizeLocation initial middle)
    (second : Frame memoryLocation sizeLocation middle final) : Frame memoryLocation sizeLocation initial final :=
  ⟨Nat.le_trans first.length second.length,
    fun location value memory size found => second.read location value memory size (first.read location value memory size found)⟩

theorem Frame.append (memoryLocation sizeLocation : Nat) (store suffix : Store) :
    Frame memoryLocation sizeLocation store (store ++ suffix) where
  length := by simp
  read := by
    intro location value _ _ found
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

theorem Frame.touch (memoryLocation sizeLocation : Nat) (store : Store) (size offset length : Word) :
    Frame memoryLocation sizeLocation store (touchStore store sizeLocation size offset length) where
  length := by rw [touchStore_length]; exact Nat.le_refl _
  read := fun location value _ different found => (touchStore_other store different size offset length).trans found

theorem Frame.writeMemory (memoryLocation sizeLocation : Nat) (store : Store) (value : Value) :
    Frame memoryLocation sizeLocation store (store.set memoryLocation value) where
  length := by simp
  read := by
    intro location value different _ found
    simpa [Store.read?, Ne.symm different] using found

theorem StateRel.append {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) (suffix : Store) :
    StateRel memoryLocation sizeLocation state (store ++ suffix) where
  distinct := related.distinct
  memory := by
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.memory).1]
      using related.memory
  size := by
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.size).1]
      using related.size

theorem StateRel.touch {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) {offset length size : Word}
    (touched : MemorySemantics.touchSize? state.size offset length = some size) :
    StateRel memoryLocation sizeLocation {state with size := size}
      (touchStore store sizeLocation state.size offset length) where
  distinct := related.distinct
  memory := (touchStore_other store related.distinct _ _ _).trans related.memory
  size := touchStore_read related.size touched

theorem StateRel.writeMemory {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) (entries : MemorySemantics.Entries) :
    StateRel memoryLocation sizeLocation {state with words := entries}
      (store.set memoryLocation (WordMapping.encode entries)) where
  distinct := related.distinct
  memory := by
    have bound := (List.getElem?_eq_some_iff.mp related.memory).1
    simp [Store.read?, bound]
  size := by simpa [Store.read?, related.distinct] using related.size

theorem mload_preserves {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) (offset : Word) (environment : Environment) :
    Correspondence.ResultRel .word (MemorySemantics.mload state offset).1 (mloadResult state offset) ∧
    StateRel memoryLocation sizeLocation (MemorySemantics.mload state offset).2
      (mloadStore store memoryLocation sizeLocation state offset environment) ∧
    Frame memoryLocation sizeLocation store (mloadStore store memoryLocation sizeLocation state offset environment) := by
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none =>
      simp only [MemorySemantics.mload, mloadResult, mloadStore, checked]
      exact ⟨.language _, related, Frame.refl _ _ _⟩
  | some size =>
      simp only [MemorySemantics.mload, mloadResult, mloadStore, checked]
      obtain ⟨suffix, extended⟩ := readWordStore_extension
        (touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)) state.words offset
        (WordMapping.encode state.words :: .unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
          (.pair (.cellRef .word sizeLocation) (.word offset)) :: environment)
      rw [extended]
      exact ⟨.value (.word _), (related.touch checked).append suffix,
        (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ _)⟩

theorem mstore_preserves {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) (offset value : Word) (environment : Environment) :
    Correspondence.ResultRel .unit (MemorySemantics.mstore state offset value).1 (mstoreResult state offset) ∧
    StateRel memoryLocation sizeLocation (MemorySemantics.mstore state offset value).2
      (mstoreStore store memoryLocation sizeLocation state offset value environment) ∧
    Frame memoryLocation sizeLocation store (mstoreStore store memoryLocation sizeLocation state offset value environment) := by
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 32) with
  | none =>
      simp only [MemorySemantics.mstore, mstoreResult, mstoreStore, checked]
      exact ⟨.language _, related, Frame.refl _ _ _⟩
  | some size =>
      simp only [MemorySemantics.mstore, mstoreResult, mstoreStore, checked]
      obtain ⟨suffix, extended⟩ := writeWordStore_extension
        (touchStore store sizeLocation state.size offset (Word.ofNatModulo 32)) state.words offset value
        (WordMapping.encode state.words :: .unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
          (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
      rw [extended]
      exact ⟨.value .unit, ((related.touch checked).append suffix).writeMemory _,
        ((Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ _)).trans (Frame.writeMemory _ _ _ _)⟩

def writeByteStore (store : Store) (entries : MemorySemantics.Entries) (offset value : Word)
    (environment : Environment) : Store :=
  let packet := Value.pair (WordMapping.encode entries) (.pair (.word offset) (.word value))
  let key := MemorySemantics.index offset
  let distance := ((Word.ofNatModulo 31).sub (MemorySemantics.position offset)).mul (Word.ofNatModulo 8)
  let mask := (Word.ofNatModulo 255).shiftLeft distance
  let old := MemorySemantics.lookup key entries
  let updated := (old.bitAnd mask.bitNot).bitOr
    ((value.bitAnd (Word.ofNatModulo 255)).shiftLeft distance)
  let lookupEnvironment := Value.word distance :: packet :: environment
  insertStore (lookupStore store entries key lookupEnvironment) entries key updated
    (.word old :: lookupEnvironment)

theorem writeMemoryByte_evaluates {environment : Environment} {initial first second store : Store}
    {mapping offsetExpr valueExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset value : Word)
    (mappingEvaluated : Evaluates environment initial mapping (WordMapping.encode entries) first)
    (offsetEvaluated : Evaluates environment first offsetExpr (.word offset) second)
    (valueEvaluated : Evaluates environment second valueExpr (.word value) store) :
    Evaluates environment initial (Memory.writeMemoryByte mapping offsetExpr valueExpr)
      (.inRight .word (WordMapping.encode (MemorySemantics.writeByte entries offset value)))
      (writeByteStore store entries offset value environment) := by
  apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated valueEvaluated))
  apply Evaluates.letE (.binary (.binary .word (.binary (.first (.second (.var rfl))) .word rfl) rfl) .word rfl)
  simp only [MemorySemantics.writeByte, writeByteStore, lookup_eq, insert_eq]
  apply LanguageResult.bind_success WordMapping.type
    (WordMapping.lookup_evaluates entries (MemorySemantics.index offset)
      (.first (.var rfl)) (.binary (.first (.second (.var rfl))) .word rfl))
  apply WordMapping.insert_evaluates entries (MemorySemantics.index offset) _
    (.first (.var rfl)) (.binary (.first (.second (.var rfl))) .word rfl)
  exact (.binary (.binary (.var rfl) (.unary (.binary .word (.var rfl) rfl) rfl) rfl)
      (.binary (.binary (.second (.second (.var rfl))) .word rfl) (.var rfl) rfl) rfl)

theorem writeByteStore_extension (store : Store) (entries : MemorySemantics.Entries)
    (offset value : Word) (environment : Environment) :
    ∃ suffix, writeByteStore store entries offset value environment = store ++ suffix := by
  simp only [writeByteStore, lookupStore, insertStore, WordMapping.installedStore, List.append_assoc]
  exact ⟨_, rfl⟩

def mstore8Result (state : MemorySemantics.State) (offset : Word) : Value :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 1) with
  | none => .inLeft .unit (.word Memory.overflowReason)
  | some _ => .inRight .word .unit

def mstore8Store (store : Store) (memoryLocation sizeLocation : Nat)
    (state : MemorySemantics.State) (offset value : Word) (environment : Environment) : Store :=
  match MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 1) with
  | none => store
  | some _ =>
      let packet := Value.pair (.cellRef WordMapping.type memoryLocation)
        (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value)))
      let touched := touchStore store sizeLocation state.size offset (Word.ofNatModulo 1)
      let written := writeByteStore touched state.words offset value (.unit :: packet :: environment)
      written.set memoryLocation (WordMapping.encode (MemorySemantics.writeByte state.words offset value))

theorem mstore8_evaluates {environment : Environment} {initial first second third store : Store}
    {memoryReference sizeReference offsetExpr valueExpr : Core.Expr} {memoryLocation sizeLocation : Nat}
    (state : MemorySemantics.State) (offset value : Word)
    (memoryEvaluated : Evaluates environment initial memoryReference (.cellRef WordMapping.type memoryLocation) first)
    (sizeEvaluated : Evaluates environment first sizeReference (.cellRef .word sizeLocation) second)
    (offsetEvaluated : Evaluates environment second offsetExpr (.word offset) third)
    (valueEvaluated : Evaluates environment third valueExpr (.word value) store)
    (memoryRead : store.read? memoryLocation = some (WordMapping.encode state.words))
    (sizeRead : store.read? sizeLocation = some (.word state.size))
    (different : memoryLocation ≠ sizeLocation) :
    Evaluates environment initial (Memory.mstore8 memoryReference sizeReference offsetExpr valueExpr)
      (mstore8Result state offset) (mstore8Store store memoryLocation sizeLocation state offset value environment) := by
  apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated valueEvaluated)))
  have touched := touch_evaluates
    (environment := Value.pair (.cellRef WordMapping.type memoryLocation)
      (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
    (reference := .first (.second (.var 0))) (offsetExpr := .first (.second (.second (.var 0))))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (Evaluates.word (value := Word.ofNatModulo 1)) sizeRead
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 1) with
  | none =>
      simp only [touchResult, checked, touchStore_failure checked] at touched
      simp only [mstore8Result, mstore8Store, checked]
      exact LanguageResult.bind_failure .unit touched
  | some size =>
      simp only [touchResult, checked] at touched
      simp only [mstore8Result, mstore8Store, checked]
      have memoryAfterTouch := (touchStore_other store different state.size offset (Word.ofNatModulo 1)).trans memoryRead
      apply LanguageResult.bind_success .unit touched
      apply LanguageResult.bind_success .unit
        (writeMemoryByte_evaluates state.words offset value (.loadCell (.first (.var rfl)) memoryAfterTouch)
          (.first (.second (.second (.var rfl)))) (.second (.second (.second (.var rfl)))))
      obtain ⟨suffix, extended⟩ := writeByteStore_extension
        (touchStore store sizeLocation state.size offset (Word.ofNatModulo 1)) state.words offset value
        (.unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
          (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
      have bound := (List.getElem?_eq_some_iff.mp memoryAfterTouch).1
      have memoryAfterWrite : (writeByteStore
          (touchStore store sizeLocation state.size offset (Word.ofNatModulo 1)) state.words offset value
          (.unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
            (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)).read?
            memoryLocation = some (WordMapping.encode state.words) := by
        rw [extended]
        simpa only [Store.read?, List.getElem?_append_left bound] using memoryAfterTouch
      apply Evaluates.inRight
      apply Evaluates.storeCell (.first (.var rfl)) memoryAfterWrite (.var rfl)
      exact Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp memoryAfterWrite).1, rfl⟩

theorem mstore8_preserves {memoryLocation sizeLocation : Nat} {state : MemorySemantics.State} {store : Store}
    (related : StateRel memoryLocation sizeLocation state store) (offset value : Word) (environment : Environment) :
    Correspondence.ResultRel .unit (MemorySemantics.mstore8 state offset value).1 (mstore8Result state offset) ∧
    StateRel memoryLocation sizeLocation (MemorySemantics.mstore8 state offset value).2
      (mstore8Store store memoryLocation sizeLocation state offset value environment) ∧
    Frame memoryLocation sizeLocation store (mstore8Store store memoryLocation sizeLocation state offset value environment) := by
  cases checked : MemorySemantics.touchSize? state.size offset (Word.ofNatModulo 1) with
  | none =>
      simp only [MemorySemantics.mstore8, mstore8Result, mstore8Store, checked]
      exact ⟨.language _, related, Frame.refl _ _ _⟩
  | some size =>
      simp only [MemorySemantics.mstore8, mstore8Result, mstore8Store, checked]
      obtain ⟨suffix, extended⟩ := writeByteStore_extension
        (touchStore store sizeLocation state.size offset (Word.ofNatModulo 1)) state.words offset value
        (.unit :: Value.pair (.cellRef WordMapping.type memoryLocation)
          (.pair (.cellRef .word sizeLocation) (.pair (.word offset) (.word value))) :: environment)
      rw [extended]
      exact ⟨.value .unit, ((related.touch checked).append suffix).writeMemory _,
        ((Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ _)).trans (Frame.writeMemory _ _ _ _)⟩

set_option linter.unusedSimpArgs false in
theorem mload_rename (memory size offset : Core.Expr) (mapping : Renaming) :
    (Memory.mload memory size offset).rename mapping =
      Memory.mload (memory.rename mapping) (size.rename mapping) (offset.rename mapping) := by
  simp only [Memory.mload, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.readMemoryWord, Memory.writeMemoryWord, Memory.writeMemoryByte,
    WordMapping.lookup, WordMapping.insert, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.insertBody, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt,
    WordMapping.cons, WordMapping.empty]
  rfl

set_option linter.unusedSimpArgs false in
theorem mstore_rename (memory size offset value : Core.Expr) (mapping : Renaming) :
    (Memory.mstore memory size offset value).rename mapping =
      Memory.mstore (memory.rename mapping) (size.rename mapping) (offset.rename mapping) (value.rename mapping) := by
  simp only [Memory.mstore, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.readMemoryWord, Memory.writeMemoryWord, Memory.writeMemoryByte,
    WordMapping.lookup, WordMapping.insert, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.insertBody, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt,
    WordMapping.cons, WordMapping.empty]
  rfl

set_option linter.unusedSimpArgs false in
theorem mstore8_rename (memory size offset value : Core.Expr) (mapping : Renaming) :
    (Memory.mstore8 memory size offset value).rename mapping =
      Memory.mstore8 (memory.rename mapping) (size.rename mapping) (offset.rename mapping) (value.rename mapping) := by
  simp only [Memory.mstore8, Core.Expr.rename]
  congr 1
  simp only [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.readMemoryWord, Memory.writeMemoryWord, Memory.writeMemoryByte,
    WordMapping.lookup, WordMapping.insert, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.insertBody, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt,
    WordMapping.cons, WordMapping.empty]
  rfl

end Solcore.Frontend.RustHull.MemoryCorrespondence
