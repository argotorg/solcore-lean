import Solcore.Frontend.RustHull.Semantics.Memory
import Solcore.Frontend.RustHull.Memory
import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Frontend.RustHull.Semantics.World
import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.AccountRuntime

/-!
# Memory and log state

Core memory, range copies and logs against the independent state.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.LogsCorrespondence
/-! Event payload snapshots execute through the emitted mapping helpers.
All helper allocations remain in the resulting Core store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogsCorrespondence
open Core

theorem invoke_evaluates {environment captured : Environment} {store final : Store}
    {parameter result : Core.Ty} {body reference argument : Core.Expr} {location : Nat} {input output : Value}
    (referenceEvaluated : Evaluates environment store reference
      (.cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location) store)
    (installed : WordMapping.Installed store parameter result body location captured)
    (argumentEvaluated : Evaluates (WordMapping.closure parameter result body location captured :: environment)
      store (argument.weakenAt 0) input store)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) location :: captured)
      store body output final) :
    Evaluates environment store (WordMapping.invoke parameter result reference argument) output final :=
  .caseRight (OptionalCell.read_success Word.zero referenceEvaluated installed)
    (.apply (.var rfl) argumentEvaluated bodyEvaluated)

theorem runHelper_evaluates {environment : Environment} {initial store final : Store}
    {parameter result : Core.Ty} {body argument : Core.Expr} {input output : Value}
    (argumentEvaluated : Evaluates environment initial argument input store)
    (bodyEvaluated : Evaluates
      (input :: .cellRef (OptionalCell.cellType (WordMapping.helperType parameter result)) store.length :: input :: environment)
      (WordMapping.installedStore store parameter result body input environment) body output final) :
    Evaluates environment initial (WordMapping.runHelper parameter result body argument) output final := by
  apply Evaluates.letE argumentEvaluated
  apply Evaluates.letE (OptionalCell.allocate_evaluates _ _ _)
  apply Evaluates.letE (bodyStore := WordMapping.installedStore store parameter result body input environment)
  · apply Evaluates.storeCell (oldValue := .inLeft (WordMapping.helperType parameter result) .unit) (.var rfl)
    · simp [Store.read?]
    · exact .inRight .lambda
    · simp [Store.write?, WordMapping.installedStore, WordMapping.closure]
  · apply invoke_evaluates (body := body) (captured := input :: environment) (.var rfl)
    · simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]
    · simpa [Core.Expr.weakenAt] using (Evaluates.var (by rfl))
    · exact bodyEvaluated

theorem installed_append {store : Store} {parameter result : Core.Ty} {body : Core.Expr}
    {location : Nat} {captured : Environment}
    (installed : WordMapping.Installed store parameter result body location captured) (suffix : Store) :
    WordMapping.Installed (store ++ suffix) parameter result body location captured := by
  have bound := (List.getElem?_eq_some_iff.mp installed).1
  simpa only [WordMapping.Installed, Store.read?, List.getElem?_append_left bound] using installed

def copyInput (memory : LogsSemantics.Words) (offset length : Word)
    (mapping : LogsSemantics.Words) (cursor : Word) : Value :=
  .pair (WordMapping.encode memory) (.pair (.word offset) (.pair (.word length)
    (.pair (WordMapping.encode mapping) (.word cursor))))

theorem copyBody_evaluates {memory : LogsSemantics.Words} {offset length cursor : Word}
    {mapping result : LogsSemantics.Words} (copied : LogsSemantics.Copy memory offset length mapping cursor result)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Logs.copyType WordMapping.type Logs.copyBody location captured) :
    ∃ suffix, Evaluates
      (copyInput memory offset length mapping cursor ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Logs.copyType WordMapping.type)) location :: captured)
      store Logs.copyBody (.inRight .word (WordMapping.encode result)) (store ++ suffix) := by
  induction copied generalizing store with
  | empty offset cursor mapping =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      exact .ifTrue (.binary (.first (.second (.second (.var rfl)))) .word rfl)
        (.inRight (.first (.second (.second (.second (.var rfl))))))
  | @step offset length cursor mapping result nonempty rest ih =>
      let input := copyInput memory offset length mapping cursor
      let environment := input :: .cellRef (OptionalCell.cellType (WordMapping.helperType Logs.copyType WordMapping.type)) location :: captured
      let readStore := MemoryCorrespondence.readWordStore store memory offset environment
      obtain ⟨readSuffix, readExtended⟩ := MemoryCorrespondence.readWordStore_extension store memory offset environment
      have readEvaluated := MemoryCorrespondence.readMemoryWord_evaluates
        (environment := environment) (initial := store)
        (mapping := Logs.field 0 5 (.var 0)) (offsetExpr := Logs.field 1 5 (.var 0)) memory offset
        (.first (.var rfl)) (.first (.second (.var rfl)))
      let word := MemorySemantics.readWord memory offset
      let count := LogsSemantics.chunk length
      let distance := LogsSemantics.padding length
      let updated := MemorySemantics.insert cursor (LogsSemantics.paddedWord memory offset length) mapping
      let insertEnvironment := Value.word distance :: .word count :: .word word :: environment
      let inserted := MemoryCorrespondence.insertStore readStore mapping cursor
        (LogsSemantics.paddedWord memory offset length) insertEnvironment
      have insertedInstalled : WordMapping.Installed inserted Logs.copyType WordMapping.type Logs.copyBody location captured := by
        apply installed_append (suffix := [_])
        rw [show readStore = store ++ readSuffix from readExtended]
        exact installed_append installed readSuffix
      obtain ⟨suffix, evaluated⟩ := ih inserted insertedInstalled
      refine ⟨readSuffix ++ [.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody readStore.length
        (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word (LogsSemantics.paddedWord memory offset length))) :: insertEnvironment))] ++ suffix, ?_⟩
      have finalStore : inserted ++ suffix = store ++
          (readSuffix ++ [.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody readStore.length
            (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word (LogsSemantics.paddedWord memory offset length))) :: insertEnvironment))] ++ suffix) := by
        change (readStore ++ [_]) ++ suffix = _
        rw [show readStore = store ++ readSuffix from readExtended]
        simp only [List.append_assoc]
      rw [← finalStore]
      apply Evaluates.ifFalse
      · apply Evaluates.binary (.first (.second (.second (.var rfl)))) .word
        change some (Value.bool (length == Word.zero)) = some (Value.bool false)
        exact congrArg (fun value => some (Value.bool value)) (beq_eq_false_iff_ne.mpr nonempty)
      · apply LanguageResult.bind_success WordMapping.type readEvaluated
        have countEvaluated : Evaluates (.word word :: environment) readStore
            (.ifE (.binary .wordGt (Logs.field 2 5 (.var 1)) (Logs.number 31)) (Logs.number 32) (Logs.field 2 5 (.var 1)))
            (.word count) readStore := by
          by_cases enough : length > Word.ofNatModulo 31
          · simp only [count, LogsSemantics.chunk, enough, ↓reduceIte]
            exact .ifTrue (.binary (.first (.second (.second (.var rfl)))) .word (by simp [BinaryOp.apply, enough])) .word
          · simp only [count, LogsSemantics.chunk, enough, ↓reduceIte]
            exact .ifFalse (.binary (.first (.second (.second (.var rfl)))) .word (by simp [BinaryOp.apply, enough]))
              (.first (.second (.second (.var rfl))))
        apply Evaluates.letE countEvaluated
        apply Evaluates.letE (.binary (.binary .word (.var rfl) rfl) .word rfl)
        apply LanguageResult.bind_success WordMapping.type
        · have insertedEvaluated := WordMapping.insert_evaluates mapping cursor
            (LogsSemantics.paddedWord memory offset length)
            (environment := insertEnvironment) (initialStore := readStore)
            (mapping := Logs.field 3 5 (.var 3)) (keyExpr := Logs.field 4 5 (.var 3))
            (valueExpr := .binary .wordShl (.binary .wordShr (.var 2) (.var 0)) (.var 0))
            (.first (.second (.second (.second (.var rfl))))) (.second (.second (.second (.second (.var rfl)))))
            (.binary (.binary (.var rfl) (.var rfl) rfl) (.var rfl) rfl)
          simpa only [← MemoryCorrespondence.insert_eq, insertEnvironment, distance, LogsSemantics.padding, count] using insertedEvaluated
        · apply invoke_evaluates (body := Logs.copyBody) (captured := captured)
            (input := copyInput memory (offset.add count) (length.sub count) updated (cursor.add (Word.ofNatModulo 1)))
            (.var rfl) insertedInstalled
          · simp [Core.Expr.weakenAt, Logs.packet, Logs.field, Logs.add, Logs.number]
            exact .pair (.first (.var rfl)) (.pair
              (.binary (.first (.second (.var rfl))) (.var rfl) rfl)
              (.pair (.binary (.first (.second (.second (.var rfl)))) (.var rfl) rfl)
                (.pair (.var rfl) (.binary (leftValue := .word cursor) (.second (.second (.second (.second (.var rfl))))) .word rfl))))
          · exact evaluated

theorem copyPayload_evaluates {memory : LogsSemantics.Words} {offset length cursor : Word}
    {mapping result : LogsSemantics.Words} (copied : LogsSemantics.Copy memory offset length mapping cursor result)
    {environment : Environment} {store : Store} {memoryExpr offsetExpr lengthExpr mappingExpr cursorExpr : Core.Expr}
    (memoryEvaluated : Evaluates environment store memoryExpr (WordMapping.encode memory) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (mappingEvaluated : Evaluates environment store mappingExpr (WordMapping.encode mapping) store)
    (cursorEvaluated : Evaluates environment store cursorExpr (.word cursor) store) :
    ∃ suffix, Evaluates environment store (Logs.copyPayload memoryExpr offsetExpr lengthExpr mappingExpr cursorExpr)
      (.inRight .word (WordMapping.encode result)) (store ++ suffix) := by
  let input := copyInput memory offset length mapping cursor
  let closure := WordMapping.closure Logs.copyType WordMapping.type Logs.copyBody store.length (input :: environment)
  obtain ⟨suffix, body⟩ := copyBody_evaluates copied (store ++ [.inRight .unit closure]) store.length (input :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  apply runHelper_evaluates (.pair memoryEvaluated (.pair offsetEvaluated (.pair lengthEvaluated (.pair mappingEvaluated cursorEvaluated))))
  exact body

/-- Header expressions contain immutable frame arguments. Their evaluation is
stable under the binders and helper allocations used by sequential insertion. -/
def Stable (environment : Environment) (expression : Core.Expr) (value : Value) : Prop :=
  ∀ extra store, Evaluates (extra ++ environment) store
    (expression.rename (fun index => index + extra.length)) value store

theorem Stable.evaluates {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (store : Store) :
    Evaluates environment store expression value store := by
  have evaluated := stable [] store
  change Evaluates environment store (expression.rename Renaming.id) value store at evaluated
  simpa only [Core.Expr.rename_id] using evaluated

theorem Stable.prepend {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (inserted : Value) :
    Stable (inserted :: environment) (expression.weakenAt 0) value := by
  intro extra store
  rw [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
  have renamed : Renaming.comp (fun index => index + extra.length) (Renaming.insertion 0) =
      (fun index => index + (extra ++ [inserted]).length) := by
    funext index
    simp only [Renaming.comp, Renaming.insertion, Nat.zero_le, ↓reduceIte, List.length_append, List.length_singleton]
    omega
  rw [renamed]
  simpa only [List.append_assoc, List.singleton_append] using stable (extra ++ [inserted]) store

theorem Stable.var {environment : Environment} {index : Nat} {value : Value}
    (found : environment[index]? = some value) : Stable environment (.var index) value := by
  intro extra store
  apply Evaluates.var
  simpa only [Nat.add_comm index, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using found

theorem Stable.word (environment : Environment) (value : Word) : Stable environment (.word value) (.word value) :=
  fun _ _ => .word

theorem Stable.first {environment : Environment} {expression : Core.Expr} {first second : Value}
    (stable : Stable environment expression (.pair first second)) : Stable environment (.first expression) first :=
  fun extra store => .first (stable extra store)

theorem Stable.second {environment : Environment} {expression : Core.Expr} {first second : Value}
    (stable : Stable environment expression (.pair first second)) : Stable environment (.second expression) second :=
  fun extra store => .second (stable extra store)

theorem Stable.addOne {environment : Environment} {expression : Core.Expr} {value : Word}
    (stable : Stable environment expression (.word value)) :
    Stable environment (Logs.add expression (Logs.number 1)) (.word (value.add (Word.ofNatModulo 1))) :=
  fun extra store => .binary (stable extra store) .word rfl

inductive WordExpressions (environment : Environment) : List Core.Expr → List Word → Prop where
  | nil : WordExpressions environment [] []
  | cons {expression expressions value values}
      (head : Stable environment expression (.word value))
      (tail : WordExpressions environment expressions values) :
      WordExpressions environment (expression :: expressions) (value :: values)

theorem WordExpressions.prepend {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) (inserted : Value) :
    WordExpressions (inserted :: environment) (expressions.map (·.weakenAt 0)) values := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.prepend inserted) ih

theorem insertWords_evaluates {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values)
    (mapping : LogsSemantics.Words) (cursor : Word) {mappingExpr cursorExpr : Core.Expr}
    (store : Store) (mappingEvaluated : Evaluates environment store mappingExpr (WordMapping.encode mapping) store)
    (cursorStable : Stable environment cursorExpr (.word cursor)) :
    ∃ suffix, Evaluates environment store (Logs.insertWords mappingExpr cursorExpr expressions)
      (.inRight .word (WordMapping.encode (LogsSemantics.insertWords mapping cursor values))) (store ++ suffix) := by
  induction values generalizing environment expressions mapping cursor mappingExpr cursorExpr store with
  | nil =>
      cases related
      exact ⟨[], by simpa only [List.append_nil, Logs.insertWords, LogsSemantics.insertWords, LanguageResult.success] using Evaluates.inRight (leftType := .word) mappingEvaluated⟩
  | cons value values ih =>
      cases related with
      | @cons expression expressions _ _ head tail =>
          let updated := MemorySemantics.insert cursor value mapping
          let inserted := MemoryCorrespondence.insertStore store mapping cursor value environment
          obtain ⟨suffix, rest⟩ := ih (tail.prepend (WordMapping.encode updated)) updated
            (cursor.add (Word.ofNatModulo 1)) inserted (mappingExpr := .var 0)
            (cursorExpr := Logs.add (cursorExpr.weakenAt 0) (Logs.number 1)) (.var rfl)
            ((cursorStable.prepend (WordMapping.encode updated)).addOne)
          refine ⟨[.inRight .unit (WordMapping.closure WordMapping.insertParameter WordMapping.type WordMapping.insertBody store.length
            (.pair (WordMapping.encode mapping) (.pair (.word cursor) (.word value)) :: environment))] ++ suffix, ?_⟩
          rw [← List.append_assoc, Logs.insertWords, LogsSemantics.insertWords]
          apply LanguageResult.bind_success WordMapping.type
          · simpa only [← MemoryCorrespondence.insert_eq] using WordMapping.insert_evaluates mapping cursor value
              mappingEvaluated (cursorStable.evaluates store) (head.evaluates store)
          · exact rest

def wordPacket : List Word → Value
  | [] => .unit
  | [value] => .word value
  | value :: rest => .pair (.word value) (wordPacket rest)

theorem WordExpressions.length {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) : expressions.length = values.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

theorem WordExpressions.packet {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (related : WordExpressions environment expressions values) :
    Stable environment (Logs.packet expressions) (wordPacket values) := by
  induction related with
  | nil => exact fun _ _ => .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head
      | cons next rest => exact fun extra store => .pair (head extra store) (ih extra store)

theorem Stable.field {environment : Environment} {expression : Core.Expr} {values : List Word}
    (stable : Stable environment expression (wordPacket values)) {index : Nat} {value : Word}
    (found : values[index]? = some value) :
    Stable environment (Logs.field index values.length expression) (.word value) := by
  induction values generalizing expression index with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => cases Option.some.inj found; exact stable
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero => cases Option.some.inj found; exact stable.first
          | succ index =>
              simpa [Logs.field] using ih stable.second found

theorem WordExpressions.of_getElem? {environment : Environment} {expressions : List Core.Expr} {values : List Word}
    (length : expressions.length = values.length)
    (related : ∀ (index : Nat) expression value, expressions[index]? = some expression → values[index]? = some value →
      Stable environment expression (.word value)) : WordExpressions environment expressions values := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => exact .nil
      | cons value values => simp at length
  | cons expression expressions ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          exact .cons (related 0 expression value rfl rfl)
            (ih (Nat.succ.inj length) (fun index expression value codeFound valueFound =>
              related (index + 1) expression value codeFound valueFound))

theorem Stable.fields {environment : Environment} {expression : Core.Expr} {values : List Word}
    (stable : Stable environment expression (wordPacket values)) :
    WordExpressions environment ((List.range values.length).map (fun index => Logs.field index values.length expression)) values := by
  apply WordExpressions.of_getElem? (by simp)
  intro index code value codeFound valueFound
  have bound := (List.getElem?_eq_some_iff.mp valueFound).1
  simp only [List.getElem?_map, List.getElem?_range bound, Option.map_some] at codeFound
  cases Option.some.inj codeFound
  exact stable.field valueFound

theorem WordExpressions.append {environment : Environment} {first second : List Core.Expr} {left right : List Word}
    (heads : WordExpressions environment first left) (tails : WordExpressions environment second right) :
    WordExpressions environment (first ++ second) (left ++ right) := by
  induction heads with
  | nil => exact tails
  | cons head tail ih => exact .cons head ih

structure Locations where
  memory : Nat
  memorySize : Nat
  logs : Nat
  logSize : Nat

def Locations.all (locations : Locations) : List Nat :=
  [locations.memory, locations.memorySize, locations.logs, locations.logSize]

structure StateRel (locations : Locations) (state : LogsSemantics.State) (store : Store) : Prop where
  distinct : locations.all.Nodup
  memory : store.read? locations.memory = some (WordMapping.encode state.memory.words)
  memorySize : store.read? locations.memorySize = some (.word state.memory.size)
  logs : store.read? locations.logs = some (WordMapping.encode state.words)
  logSize : store.read? locations.logSize = some (.word state.cursor)

structure Frame (locations : Locations) (initial final : Store) : Prop where
  length : initial.length ≤ final.length
  read : ∀ location value, location ∉ locations.all → initial.read? location = some value → final.read? location = some value

theorem Frame.refl (locations : Locations) (store : Store) : Frame locations store store :=
  ⟨Nat.le_refl _, fun _ _ _ found => found⟩

theorem Frame.trans {locations : Locations} {initial middle final : Store}
    (first : Frame locations initial middle) (second : Frame locations middle final) : Frame locations initial final :=
  ⟨Nat.le_trans first.length second.length, fun location value outside found =>
    second.read location value outside (first.read location value outside found)⟩

theorem Frame.append (locations : Locations) (store suffix : Store) : Frame locations store (store ++ suffix) where
  length := by simp
  read := by
    intro location value _ found
    simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found

theorem Frame.set (locations : Locations) (store : Store) (location : Nat) (value : Value)
    (member : location ∈ locations.all) : Frame locations store (store.set location value) where
  length := by simp
  read := by
    intro other old outside found
    have different : location ≠ other := fun equal => outside (equal ▸ member)
    simpa [Store.read?, different] using found

theorem Frame.touch (locations : Locations) (store : Store) (size offset length : Word) :
    Frame locations store (MemoryCorrespondence.touchStore store locations.memorySize size offset length) where
  length := by rw [MemoryCorrespondence.touchStore_length]; exact Nat.le_refl _
  read := by
    intro location value outside found
    exact (MemoryCorrespondence.touchStore_other store
      (by intro equal; exact outside (by simp [Locations.all, equal])) size offset length).trans found

theorem StateRel.append {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) (suffix : Store) : StateRel locations state (store ++ suffix) where
  distinct := related.distinct
  memory := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.memory).1] using related.memory
  memorySize := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.memorySize).1] using related.memorySize
  logs := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.logs).1] using related.logs
  logSize := by simpa only [Store.read?, List.getElem?_append_left (List.getElem?_eq_some_iff.mp related.logSize).1] using related.logSize

theorem StateRel.touch {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) {offset length size : Word}
    (expanded : MemorySemantics.touchSize? state.memory.size offset length = some size) :
    StateRel locations {state with memory := {state.memory with size := size}}
      (MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  refine ⟨related.distinct, ?_, MemoryCorrespondence.touchStore_read related.memorySize expanded, ?_, ?_⟩
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.memory
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.logs
  · exact (MemoryCorrespondence.touchStore_other store (by intro equal; simp_all) _ _ _).trans related.logSize

def publishStore (locations : Locations) (store : Store) (words : LogsSemantics.Words) (cursor : Word) : Store :=
  (store.set locations.logs (WordMapping.encode words)).set locations.logSize (.word cursor)

theorem StateRel.publish {locations : Locations} {state : LogsSemantics.State} {store : Store}
    (related : StateRel locations state store) (words : LogsSemantics.Words) (cursor : Word) :
    StateRel locations {state with words := words, cursor := cursor} (publishStore locations store words cursor) := by
  have distinct := related.distinct
  simp [Locations.all] at distinct
  have logsBound := (List.getElem?_eq_some_iff.mp related.logs).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.logSize).1
  refine ⟨related.distinct, ?_, ?_, ?_, ?_⟩
  · simpa [publishStore, Store.read?, show locations.logSize ≠ locations.memory by intro equal; simp_all,
      show locations.logs ≠ locations.memory by intro equal; simp_all] using related.memory
  · simpa [publishStore, Store.read?, show locations.logSize ≠ locations.memorySize by intro equal; simp_all,
      show locations.logs ≠ locations.memorySize by intro equal; simp_all] using related.memorySize
  · simp [publishStore, Store.read?, show locations.logSize ≠ locations.logs by intro equal; simp_all, logsBound]
  · simp [publishStore, Store.read?, sizeBound]

theorem Frame.publish (locations : Locations) (store : Store) (words : LogsSemantics.Words) (cursor : Word) :
    Frame locations store (publishStore locations store words cursor) :=
  (Frame.set locations store locations.logs (WordMapping.encode words) (by simp [Locations.all])).trans
    (Frame.set locations _ locations.logSize (.word cursor) (by simp [Locations.all]))

def appendInput (locations : Locations) (address offset length : Word) (topics : List Word) : Value :=
  .pair (.cellRef WordMapping.type locations.memory)
    (.pair (.cellRef .word locations.memorySize) (.pair (.cellRef WordMapping.type locations.logs)
      (.pair (.cellRef .word locations.logSize) (.pair (.word address)
        (.pair (.word offset) (.pair (.word length) (wordPacket topics)))))))

def appendTail (count : Nat) : Core.Expr :=
  .ifE (.binary .wordGt (.var 1) (.var 0))
    (LanguageResult.failure .unit (.word Logs.capacityReason))
    (LanguageResult.bind .unit
      (Memory.touch (Logs.field 1 8 (.var 2)) (Logs.field 5 8 (.var 2)) (Logs.field 6 8 (.var 2)))
      (.letE (.loadCell (Logs.field 0 8 (.var 3)))
        (let headers := [Logs.field 4 8 (.var 4), Logs.number count, Logs.field 6 8 (.var 4)] ++
           (List.range count).map (fun index => Logs.field index count (Logs.field 7 8 (.var 4)))
         LanguageResult.bind .unit
           (Logs.insertWords (.loadCell (Logs.field 2 8 (.var 4))) (.var 3) headers)
           (LanguageResult.bind .unit
             (Logs.copyPayload (.var 1) (Logs.field 5 8 (.var 5)) (Logs.field 6 8 (.var 5))
               (.var 0) (Logs.add (.var 4) (Logs.number (3 + count))))
             (LanguageResult.success
               (.letE (.storeCell (Logs.field 2 8 (.var 6)) (.var 0))
                 (.storeCell (Logs.field 3 8 (.var 7)) (.var 5))))))))

theorem wordCount_evaluates {environment : Environment} {store : Store} {expression : Core.Expr} {length : Word}
    (stable : Stable environment expression (.word length)) :
    Evaluates environment store (Logs.wordCount expression) (.word (LogsSemantics.wordCount length)) store := by
  unfold Logs.wordCount LogsSemantics.wordCount
  apply Evaluates.binary (rightValue := .word (if length.umod (Word.ofNatModulo 32) == Word.zero then Word.zero else Word.ofNatModulo 1))
    (.binary (stable.evaluates store) .word rfl)
  · by_cases multiple : length.umod (Word.ofNatModulo 32) == Word.zero
    · simp only [multiple, ↓reduceIte]
      exact .ifTrue (.binary (.binary (stable.evaluates store) .word rfl) .word
        (by change some (Value.bool (length.umod (Word.ofNatModulo 32) == Word.zero)) = _; rw [multiple])) .word
    · simp only [multiple]
      exact .ifFalse (.binary (.binary (stable.evaluates store) .word rfl) .word
        (by change some (Value.bool (length.umod (Word.ofNatModulo 32) == Word.zero)) = _; rw [Bool.eq_false_iff.mpr multiple])) .word
  · rfl

theorem append_enter {environment : Environment} {store final : Store} {locations : Locations} {state : LogsSemantics.State}
    {memoryRef sizeRef logsRef cursorRef addressExpr offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr}
    {offset length : Word} {topics : List Word} {result : Value}
    (related : StateRel locations state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type locations.memory) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word locations.memorySize) store)
    (logsEvaluated : Evaluates environment store logsRef (.cellRef WordMapping.type locations.logs) store)
    (cursorEvaluated : Evaluates environment store cursorRef (.cellRef .word locations.logSize) store)
    (addressEvaluated : Evaluates environment store addressExpr (.word state.address) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (topicsRelated : WordExpressions environment topicExprs topics) (allowed : topics.length ≤ 4)
    (continued : Evaluates
      (.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor ::
        appendInput locations state.address offset length topics :: environment)
      store (appendTail topics.length) result final) :
    Evaluates environment store (Logs.append memoryRef sizeRef logsRef cursorRef addressExpr topicExprs offsetExpr lengthExpr) result final := by
  have count := topicsRelated.length
  simp only [Logs.append, count, show ¬topics.length > 4 from Nat.not_lt.mpr allowed, ↓reduceIte]
  apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair logsEvaluated (.pair cursorEvaluated
    (.pair addressEvaluated (.pair offsetEvaluated (.pair lengthEvaluated (topicsRelated.packet.evaluates store))))))))
  apply Evaluates.letE (.loadCell (.first (.second (.second (.second (.var rfl))))) related.logSize)
  apply Evaluates.letE
    (.binary (.var rfl) (.binary .word (wordCount_evaluates
      (Stable.first (Stable.second (Stable.second (Stable.second (Stable.second (Stable.second (Stable.second (Stable.var (by rfl)))))))))) rfl) rfl)
  exact continued

theorem appendTail_preserves {locations : Locations} {state finalState : LogsSemantics.State}
    {offset length : Word} {topics : List Word} {result : Semantics.Result Semantics.Value}
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (allowed : topics.length ≤ 4) (environment : Environment) (store : Store)
    (related : StateRel locations state store) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates (.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor ::
        appendInput locations state.address offset length topics :: environment)
        store (appendTail topics.length) target final ∧ StateRel locations finalState final ∧ Frame locations store final := by
  let input := appendInput locations state.address offset length topics
  let entered := Value.word (LogsSemantics.nextCursor state.cursor length topics) :: .word state.cursor :: input :: environment
  have touched := MemoryCorrespondence.touch_evaluates (environment := entered)
    (reference := Logs.field 1 8 (.var 2)) (offsetExpr := Logs.field 5 8 (.var 2))
    (lengthExpr := Logs.field 6 8 (.var 2))
    (.first (.second (.var rfl)))
    (.first (.second (.second (.second (.second (.second (.var rfl)))))))
    (.first (.second (.second (.second (.second (.second (.second (.var rfl)))))))) related.memorySize
  cases appended with
  | topics tooMany => omega
  | capacity allowed overflow =>
      refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
      exact .ifTrue (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, overflow])) (.inLeft .word)
  | memory allowed capacity overflow =>
      simp only [MemoryCorrespondence.touchResult, overflow, MemoryCorrespondence.touchStore_failure overflow] at touched
      refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
      exact .ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, capacity]))
        (LanguageResult.bind_failure .unit touched)
  | @done size words allowed capacity expanded copied =>
      simp only [MemoryCorrespondence.touchResult, expanded] at touched
      let touchedStore := MemoryCorrespondence.touchStore store locations.memorySize state.memory.size offset length
      have touchedRelated := related.touch expanded
      let headerEnvironment := WordMapping.encode state.memory.words :: Value.unit :: entered
      let headerExprs := [Logs.field 4 8 (.var 4), Logs.number topics.length, Logs.field 6 8 (.var 4)] ++
        (List.range topics.length).map (fun index => Logs.field index topics.length (Logs.field 7 8 (.var 4)))
      have inputStable : Stable headerEnvironment (.var 4) input := Stable.var rfl
      have headerRelated : WordExpressions headerEnvironment headerExprs (LogsSemantics.headers state.address length topics) := by
        apply WordExpressions.append
          (.cons inputStable.second.second.second.second.first
            (.cons (Stable.word _ _) (.cons inputStable.second.second.second.second.second.second.first .nil)))
        exact inputStable.second.second.second.second.second.second.second.fields
      let headerWords := LogsSemantics.insertWords state.words state.cursor (LogsSemantics.headers state.address length topics)
      obtain ⟨headerSuffix, inserted⟩ := insertWords_evaluates headerRelated state.words state.cursor touchedStore
        (mappingExpr := .loadCell (Logs.field 2 8 (.var 4))) (cursorExpr := .var 3)
        (.loadCell (.first (.second (.second (.var rfl)))) touchedRelated.logs) (Stable.var rfl)
      let headerStore := touchedStore ++ headerSuffix
      have headerStored := touchedRelated.append headerSuffix
      let payloadEnvironment := WordMapping.encode headerWords :: headerEnvironment
      obtain ⟨payloadSuffix, payload⟩ := copyPayload_evaluates copied
        (environment := payloadEnvironment) (store := headerStore)
        (memoryExpr := .var 1) (offsetExpr := Logs.field 5 8 (.var 5)) (lengthExpr := Logs.field 6 8 (.var 5))
        (mappingExpr := .var 0) (cursorExpr := Logs.add (.var 4) (Logs.number (3 + topics.length)))
        (.var rfl) (.first (.second (.second (.second (.second (.second (.var rfl)))))))
        (.first (.second (.second (.second (.second (.second (.second (.var rfl))))))))
        (.var rfl) (.binary (.var rfl) .word rfl)
      let copiedStore := headerStore ++ payloadSuffix
      have copiedRelated := headerStored.append payloadSuffix
      have distinct := related.distinct
      simp [Locations.all] at distinct
      have logsWritten : copiedStore.write? locations.logs (WordMapping.encode words) =
          some (copiedStore.set locations.logs (WordMapping.encode words)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp copiedRelated.logs).1, rfl⟩
      have cursorRead : Store.read? (copiedStore.set locations.logs (WordMapping.encode words)) locations.logSize = some (.word state.cursor) := by
        rw [Store.write?_preserves_other logsWritten (by intro equal; simp_all)]
        exact copiedRelated.logSize
      have cursorWritten : Store.write? (copiedStore.set locations.logs (WordMapping.encode words)) locations.logSize
          (.word (LogsSemantics.nextCursor state.cursor length topics)) =
          some (publishStore locations copiedStore words (LogsSemantics.nextCursor state.cursor length topics)) :=
        Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp cursorRead).1, rfl⟩
      refine ⟨_, _, .value .unit, ?_, copiedRelated.publish words _,
        ((Frame.touch locations store state.memory.size offset length).trans
          ((Frame.append locations touchedStore headerSuffix).trans
            (Frame.append locations headerStore payloadSuffix))).trans (Frame.publish locations copiedStore words _)⟩
      apply Evaluates.ifFalse (.binary (.var rfl) (.var rfl) (by simp [BinaryOp.apply, capacity]))
      apply LanguageResult.bind_success .unit touched
      apply Evaluates.letE (.loadCell (.first (.var rfl)) touchedRelated.memory)
      apply LanguageResult.bind_success .unit inserted
      apply LanguageResult.bind_success .unit payload
      apply Evaluates.inRight
      apply Evaluates.letE
        (.storeCell (.first (.second (.second (.var rfl)))) copiedRelated.logs (.var rfl) logsWritten)
      exact .storeCell (.first (.second (.second (.second (.var rfl))))) cursorRead (.var rfl) cursorWritten

theorem append_preserves {environment : Environment} {store : Store} {locations : Locations}
    {state finalState : LogsSemantics.State} {result : Semantics.Result Semantics.Value}
    {memoryRef sizeRef logsRef cursorRef addressExpr offsetExpr lengthExpr : Core.Expr} {topicExprs : List Core.Expr}
    {offset length : Word} {topics : List Word}
    (appended : LogsSemantics.Append offset length topics state result finalState)
    (related : StateRel locations state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type locations.memory) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word locations.memorySize) store)
    (logsEvaluated : Evaluates environment store logsRef (.cellRef WordMapping.type locations.logs) store)
    (cursorEvaluated : Evaluates environment store cursorRef (.cellRef .word locations.logSize) store)
    (addressEvaluated : Evaluates environment store addressExpr (.word state.address) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (topicsRelated : WordExpressions environment topicExprs topics) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates environment store (Logs.append memoryRef sizeRef logsRef cursorRef addressExpr topicExprs offsetExpr lengthExpr)
        target final ∧ StateRel locations finalState final ∧ Frame locations store final := by
  by_cases allowed : topics.length ≤ 4
  · obtain ⟨target, final, resultRelated, evaluated, stateRelated, frame⟩ := appendTail_preserves appended allowed environment store related
    exact ⟨target, final, resultRelated, append_enter related memoryEvaluated sizeEvaluated logsEvaluated cursorEvaluated
      addressEvaluated offsetEvaluated lengthEvaluated topicsRelated allowed evaluated, stateRelated, frame⟩
  · cases appended with
    | topics tooMany =>
        refine ⟨_, store, .language _, ?_, related, Frame.refl _ _⟩
        simpa only [Logs.append, topicsRelated.length, show topics.length > 4 from Nat.lt_of_not_ge allowed,
          ↓reduceIte, LanguageResult.failure, Logs.topicReason] using (Evaluates.inLeft (rightType := .unit) (Evaluates.word (value := Word.ofNatModulo 11)))
    | capacity possible _ => contradiction
    | memory possible _ _ => contradiction
    | done possible _ _ _ => contradiction

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem append_rename (memory size logs cursor address : Core.Expr) (topics : List Core.Expr)
    (offset length : Core.Expr) (mapping : Renaming) (allowed : topics.length ≤ 4) :
    (Logs.append memory size logs cursor address topics offset length).rename mapping =
      Logs.append (memory.rename mapping) (size.rename mapping) (logs.rename mapping) (cursor.rename mapping)
        (address.rename mapping) (topics.map (·.rename mapping)) (offset.rename mapping) (length.rename mapping) := by
  rcases topics with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals try (have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at allowed; omega); subst rest)
  all_goals
    simp [Logs.append, List.range_succ, Logs.packet, Logs.field, Logs.wordCount, Logs.add, Logs.number,
      Logs.insertWords, Logs.copyPayload, Logs.copyBody,
      LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
      Memory.touch, Memory.readMemoryWord, WordMapping.lookup, WordMapping.insert,
      WordMapping.runHelper, WordMapping.lookupBody, WordMapping.insertBody, WordMapping.invoke,
      OptionalCell.allocate, OptionalCell.read, Core.Expr.rename, Core.Expr.renameList,
      Renaming.lift, Core.Expr.weakenAt, WordMapping.cons, WordMapping.empty]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end Solcore.Frontend.RustHull.LogsCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryCopyCorrespondence
/-! Retained source snapshots and destination writes execute through the
compiler's memory-copy loop, including all allocated helper closures. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryCopyCorrespondence
open Core MemoryCorrespondence

theorem readMemoryByte_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset : Word)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode entries) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store) :
    ∃ suffix, Evaluates environment store (Memory.readMemoryByte mapping offsetExpr)
      (.inRight .word (.word (MemoryCopySemantics.readByte entries offset))) (store ++ suffix) := by
  let input := Value.pair (WordMapping.encode entries) (.word offset)
  refine ⟨[.inRight .unit (WordMapping.closure WordMapping.lookupParameter .word WordMapping.lookupBody store.length
    (.pair (WordMapping.encode entries) (.word (MemorySemantics.index offset)) :: input :: environment))], ?_⟩
  apply Evaluates.letE (.pair mappingEvaluated offsetEvaluated)
  apply LanguageResult.bind_success .word
    (WordMapping.lookup_evaluates entries (MemorySemantics.index offset)
      (.first (.var rfl)) (.binary (.second (.var rfl)) .word rfl))
  apply Evaluates.inRight
  apply Evaluates.binary (.binary (.second (.var rfl)) .word rfl) (.var rfl)
  simp only [BinaryOp.apply, MemoryCopySemantics.readByte, MemorySemantics.position, lookup_eq]

theorem validRange_evaluates {environment : Environment} {store : Store}
    {offsetExpr lengthExpr : Core.Expr} (offset length : Word)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (offsetWeakened : Evaluates (.word (offset.add length) :: environment) store
      (offsetExpr.weakenAt 0) (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    Evaluates environment store (Memory.validRange offsetExpr lengthExpr)
      (.bool (MemoryCopySemantics.validRange offset length)) store := by
  by_cases empty : length == Word.zero
  · simp only [MemoryCopySemantics.validRange, empty, ↓reduceIte]
    exact .ifTrue (.binary lengthEvaluated .word (by simpa only [BinaryOp.apply, show Word.ofNatModulo 0 = Word.zero from rfl] using congrArg (fun v => some (Value.bool v)) empty)) .bool
  · simp only [MemoryCopySemantics.validRange, empty]
    apply Evaluates.ifFalse
      (.binary lengthEvaluated .word (by simpa only [BinaryOp.apply, show Word.ofNatModulo 0 = Word.zero from rfl] using congrArg (fun v => some (Value.bool v)) (Bool.eq_false_iff.mpr empty)))
    apply Evaluates.letE (.binary offsetEvaluated lengthEvaluated rfl)
    by_cases wrapped : offset > offset.add length
    · simp only [wrapped, ↓reduceIte]
      exact .ifTrue (.binary offsetWeakened (.var rfl) (by simp [BinaryOp.apply, wrapped])) .bool
    · simp only [wrapped, ↓reduceIte]
      exact .ifFalse (.binary offsetWeakened (.var rfl) (by simp [BinaryOp.apply, wrapped]))
        (.unary (.binary (.var rfl) .word rfl) rfl)


theorem readCopied_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset length : Word)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode entries) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store) :
    ∃ suffix, Evaluates environment store
      ((if MemoryCopySemantics.width length = 32 then Memory.readMemoryWord else Memory.readMemoryByte) mapping offsetExpr)
      (.inRight .word (.word (MemoryCopySemantics.copiedWord entries offset length))) (store ++ suffix) := by
  by_cases wide : length > Word.ofNatModulo 31
  · simp only [MemoryCopySemantics.width, MemoryCopySemantics.copiedWord, wide, ↓reduceIte]
    obtain ⟨suffix, extended⟩ := readWordStore_extension store entries offset environment
    exact ⟨suffix, extended ▸ readMemoryWord_evaluates entries offset mappingEvaluated offsetEvaluated⟩
  · simp only [MemoryCopySemantics.width, MemoryCopySemantics.copiedWord, wide, ↓reduceIte]
    exact readMemoryByte_evaluates entries offset mappingEvaluated offsetEvaluated

theorem writeCopied_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr valueExpr : Core.Expr} (entries : MemorySemantics.Entries) (offset length value : Word)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode entries) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (valueEvaluated : Evaluates environment store valueExpr (.word value) store) :
    ∃ suffix, Evaluates environment store
      ((if MemoryCopySemantics.width length = 32 then Memory.writeMemoryWord else Memory.writeMemoryByte) mapping offsetExpr valueExpr)
      (.inRight .word (WordMapping.encode (MemoryCopySemantics.written entries offset length value))) (store ++ suffix) := by
  by_cases wide : length > Word.ofNatModulo 31
  · simp only [MemoryCopySemantics.width, MemoryCopySemantics.written, wide, ↓reduceIte]
    obtain ⟨suffix, extended⟩ := writeWordStore_extension store entries offset value environment
    exact ⟨suffix, extended ▸ writeMemoryWord_evaluates entries offset value mappingEvaluated offsetEvaluated valueEvaluated⟩
  · simp only [MemoryCopySemantics.width, MemoryCopySemantics.written, wide, ↓reduceIte]
    obtain ⟨suffix, extended⟩ := writeByteStore_extension store entries offset value environment
    exact ⟨suffix, extended ▸ writeMemoryByte_evaluates entries offset value mappingEvaluated offsetEvaluated valueEvaluated⟩

def copyInput (sourceWords : MemorySemantics.Entries) (destination source length : Word) (memoryLocation : Nat) : Value :=
  .pair (WordMapping.encode sourceWords) (.pair (.word destination) (.pair (.word source)
    (.pair (.word length) (.cellRef WordMapping.type memoryLocation))))

theorem copyBody_evaluates {sourceWords destinationWords finalWords : MemorySemantics.Entries}
    {destination source length : Word}
    (copied : MemoryCopySemantics.Copy sourceWords destination source length destinationWords finalWords)
    {memoryLocation sizeLocation : Nat} (size : Word) (store : Store) (location : Nat) (captured : Environment)
    (related : StateRel memoryLocation sizeLocation ⟨destinationWords, size⟩ store)
    (installed : WordMapping.Installed store Memory.copyParameter .unit (Memory.copyBody true) location captured)
    (memorySeparate : location ≠ memoryLocation) (sizeSeparate : location ≠ sizeLocation) :
    ∃ final, Evaluates
      (copyInput sourceWords destination source length memoryLocation ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Memory.copyParameter .unit)) location :: captured)
      store (Memory.copyBody true) (.inRight .word .unit) final ∧
      StateRel memoryLocation sizeLocation ⟨finalWords, size⟩ final ∧ Frame memoryLocation sizeLocation store final := by
  induction copied generalizing store with
  | empty sourceWords destinationWords destination source =>
      exact ⟨store, .ifTrue (.binary (.first (.second (.second (.second (.var rfl))))) .word rfl)
        (.inRight .unit), related, Frame.refl _ _ _⟩
  | @step sourceWords destinationWords finalWords destination source length nonempty rest ih =>
      let input := copyInput sourceWords destination source length memoryLocation
      let environment := input :: .cellRef (OptionalCell.cellType (WordMapping.helperType Memory.copyParameter .unit)) location :: captured
      let value := MemoryCopySemantics.copiedWord sourceWords source length
      let updated := MemoryCopySemantics.written destinationWords destination length value
      obtain ⟨readSuffix, readEvaluated⟩ := readCopied_evaluates
        (environment := environment) (store := store)
        (mapping := Memory.field 0 5 (.var 0)) (offsetExpr := Memory.field 2 5 (.var 0)) sourceWords source length
        (.first (.var rfl)) (.first (.second (.second (.var rfl))))
      have readRelated := related.append readSuffix
      obtain ⟨writeSuffix, writeEvaluated⟩ := writeCopied_evaluates
        (environment := .word value :: environment) (store := store ++ readSuffix)
        (mapping := .loadCell (Memory.field 4 5 (.var 1)))
        (offsetExpr := Memory.field 1 5 (.var 1)) (valueExpr := .var 0) destinationWords destination length value
        (.loadCell (.second (.second (.second (.second (.var rfl))))) readRelated.memory)
        (.first (.second (.var rfl))) (.var rfl)
      let written := (store ++ readSuffix) ++ writeSuffix
      let published := written.set memoryLocation (WordMapping.encode updated)
      have beforePublish := readRelated.append writeSuffix
      have afterPublish := beforePublish.writeMemory updated
      have earlierFrame : Frame memoryLocation sizeLocation store published :=
        ((Frame.append _ _ _ readSuffix).trans (Frame.append _ _ _ writeSuffix)).trans (Frame.writeMemory _ _ _ _)
      have installedAfter : WordMapping.Installed published Memory.copyParameter .unit (Memory.copyBody true) location captured :=
        earlierFrame.read _ _ memorySeparate sizeSeparate installed
      obtain ⟨final, recursive, finalRelated, finalFrame⟩ := ih published afterPublish installedAfter
      refine ⟨final, ?_, finalRelated, earlierFrame.trans finalFrame⟩
      have stepEvaluated : Evaluates environment store (Memory.copyStep true (MemoryCopySemantics.width length))
          (.inRight .word .unit) final := by
        apply LanguageResult.bind_success .unit readEvaluated
        apply LanguageResult.bind_success .unit writeEvaluated
        apply Evaluates.letE (bodyStore := published)
        · exact .storeCell (.second (.second (.second (.second (.var rfl))))) beforePublish.memory (.var rfl)
            (Store.write?_eq_some_iff.mpr ⟨(List.getElem?_eq_some_iff.mp beforePublish.memory).1, rfl⟩)
        · apply LogsCorrespondence.invoke_evaluates (body := Memory.copyBody true) (captured := captured)
            (input := copyInput (MemoryCopySemantics.remainingSource sourceWords source length)
              (destination.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
              (source.add (Word.ofNatModulo (MemoryCopySemantics.width length)))
              (length.sub (Word.ofNatModulo (MemoryCopySemantics.width length))) memoryLocation)
            (.var rfl) installedAfter
          · simp [Core.Expr.weakenAt, Memory.packet, Memory.field, Memory.add, Memory.sub, Memory.number, WordMapping.empty]
            apply Evaluates.pair
            · by_cases wrapped : source > Word.ofNatModulo (wordModulus - 1 - MemoryCopySemantics.width length)
              · simp only [MemoryCopySemantics.remainingSource, wrapped, ↓reduceIte]
                exact .ifTrue (.binary (leftValue := .word source) (.first (.second (.second (.var rfl)))) .word
                  (by simp only [BinaryOp.apply, wrapped, decide_true])) (.construct .unit)
              · simp only [MemoryCopySemantics.remainingSource, wrapped, ↓reduceIte]
                exact .ifFalse (.binary (leftValue := .word source) (.first (.second (.second (.var rfl)))) .word
                  (by simp only [BinaryOp.apply, wrapped, decide_false])) (.first (.var rfl))
            · exact .pair (.binary (.first (.second (.var rfl))) .word rfl)
                (.pair (.binary (.first (.second (.second (.var rfl)))) .word rfl)
                  (.pair (.binary (.first (.second (.second (.second (.var rfl))))) .word rfl)
                    (.second (.second (.second (.second (.var rfl)))))))
          · exact recursive
      apply Evaluates.ifFalse
      · apply Evaluates.binary (.first (.second (.second (.second (.var rfl))))) .word
        exact congrArg (fun value => some (Value.bool value)) (beq_eq_false_iff_ne.mpr nonempty)
      · by_cases wide : length > Word.ofNatModulo 31
        · apply Evaluates.ifTrue (.binary (.first (.second (.second (.second (.var rfl))))) .word
            (by simp only [BinaryOp.apply, wide, decide_true]))
          simpa only [MemoryCopySemantics.width, wide, ↓reduceIte] using stepEvaluated
        · apply Evaluates.ifFalse (.binary (.first (.second (.second (.second (.var rfl))))) .word
            (by simp only [BinaryOp.apply, wide, decide_false]))
          simpa only [MemoryCopySemantics.width, wide, ↓reduceIte] using stepEvaluated


theorem copyLoop_preserves {sourceWords destinationWords finalWords : MemorySemantics.Entries}
    {destination source length : Word}
    (copied : MemoryCopySemantics.Copy sourceWords destination source length destinationWords finalWords)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat} {size : Word}
    {sourceMapping destinationExpr sourceExpr lengthExpr memoryRef : Core.Expr}
    (related : StateRel memoryLocation sizeLocation ⟨destinationWords, size⟩ store)
    (sourceMappingEvaluated : Evaluates environment store sourceMapping (WordMapping.encode sourceWords) store)
    (destinationEvaluated : Evaluates environment store destinationExpr (.word destination) store)
    (sourceEvaluated : Evaluates environment store sourceExpr (.word source) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store) :
    ∃ final, Evaluates environment store
      (WordMapping.runHelper Memory.copyParameter .unit (Memory.copyBody true)
        (Memory.packet [sourceMapping, destinationExpr, sourceExpr, lengthExpr, memoryRef]))
      (.inRight .word .unit) final ∧ StateRel memoryLocation sizeLocation ⟨finalWords, size⟩ final ∧
      Frame memoryLocation sizeLocation store final := by
  let input := copyInput sourceWords destination source length memoryLocation
  let closure := WordMapping.closure Memory.copyParameter .unit (Memory.copyBody true) store.length (input :: environment)
  have memoryBound := (List.getElem?_eq_some_iff.mp related.memory).1
  have sizeBound := (List.getElem?_eq_some_iff.mp related.size).1
  obtain ⟨final, body, finalRelated, framed⟩ := copyBody_evaluates copied size
    (store ++ [.inRight .unit closure]) store.length (input :: environment) (related.append _)
    (by simp [WordMapping.Installed, Store.read?, closure])
    (Nat.ne_of_gt memoryBound) (Nat.ne_of_gt sizeBound)
  refine ⟨final, ?_, finalRelated, (Frame.append _ _ store [_]).trans framed⟩
  apply LogsCorrespondence.runHelper_evaluates
    (.pair sourceMappingEvaluated (.pair destinationEvaluated (.pair sourceEvaluated (.pair lengthEvaluated memoryEvaluated))))
  exact body

theorem copyPackedFrom_preserves {sourceWords : MemorySemantics.Entries} {destination source length : Word}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (copied : MemoryCopySemantics.From sourceWords destination source length state result finalState)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef destinationExpr sourceMapping sourceExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (destinationEvaluated : Evaluates environment store destinationExpr (.word destination) store)
    (sourceMappingEvaluated : Evaluates environment store sourceMapping (WordMapping.encode sourceWords) store)
    (sourceEvaluated : Evaluates environment store sourceExpr (.word source) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates environment store (Memory.copyPackedFrom memoryRef sizeRef destinationExpr sourceMapping sourceExpr lengthExpr)
        target final ∧ StateRel memoryLocation sizeLocation finalState final ∧ Frame memoryLocation sizeLocation store final := by
  let input := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word destination) (.pair (WordMapping.encode sourceWords) (.pair (.word source) (.word length)))))
  have touched := touch_evaluates (environment := input :: environment)
    (reference := Memory.field 1 6 (.var 0)) (offsetExpr := Memory.field 2 6 (.var 0)) (lengthExpr := Memory.field 5 6 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.second (.second (.var rfl)))))) related.size
  cases copied with
  | overflow overflow =>
      simp only [touchResult, overflow, touchStore_failure overflow] at touched
      refine ⟨.inLeft .unit (.word Memory.overflowReason), store, .language _, ?_, related, Frame.refl _ _ _⟩
      apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated
        (.pair destinationEvaluated (.pair sourceMappingEvaluated (.pair sourceEvaluated lengthEvaluated)))))
      exact LanguageResult.bind_failure .unit touched
  | @done size words expanded copied =>
      simp only [touchResult, expanded] at touched
      have touchedRelated := related.touch expanded
      obtain ⟨final, evaluated, finalRelated, framed⟩ := copyLoop_preserves copied
        (environment := .unit :: input :: environment)
        (sourceMapping := Memory.field 3 6 (.var 1)) (destinationExpr := Memory.field 2 6 (.var 1))
        (sourceExpr := Memory.field 4 6 (.var 1)) (lengthExpr := Memory.field 5 6 (.var 1))
        (memoryRef := Memory.field 0 6 (.var 1)) touchedRelated
        (.first (.second (.second (.second (.var rfl))))) (.first (.second (.second (.var rfl))))
        (.first (.second (.second (.second (.second (.var rfl)))))) (.second (.second (.second (.second (.second (.var rfl))))))
        (.first (.var rfl))
      refine ⟨.inRight .word .unit, final, .value .unit, ?_, finalRelated,
        (Frame.touch _ _ _ _ _ _).trans framed⟩
      apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated
        (.pair destinationEvaluated (.pair sourceMappingEvaluated (.pair sourceEvaluated lengthEvaluated)))))
      exact LanguageResult.bind_success .unit touched evaluated


theorem mcopy_preserves {destination source length : Word}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (copied : MemoryCopySemantics.Move destination source length state result finalState)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef destinationExpr sourceExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (destinationEvaluated : Evaluates environment store destinationExpr (.word destination) store)
    (sourceEvaluated : Evaluates environment store sourceExpr (.word source) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, Correspondence.ResultRel .unit result target ∧
      Evaluates environment store (Memory.mcopy memoryRef sizeRef destinationExpr sourceExpr lengthExpr)
        target final ∧ StateRel memoryLocation sizeLocation finalState final ∧ Frame memoryLocation sizeLocation store final := by
  let input := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word destination) (.pair (.word source) (.word length))))
  have validDestination := validRange_evaluates (environment := input :: environment) (store := store)
    (offsetExpr := Memory.field 2 5 (.var 0)) (lengthExpr := Memory.field 4 5 (.var 0)) destination length
    (.first (.second (.second (.var rfl))))
    (by simp [Memory.field, Core.Expr.weakenAt]; exact .first (.second (.second (.var rfl))))
    (.second (.second (.second (.second (.var rfl)))))
  have validSource := validRange_evaluates (environment := input :: environment) (store := store)
    (offsetExpr := Memory.field 3 5 (.var 0)) (lengthExpr := Memory.field 4 5 (.var 0)) source length
    (.first (.second (.second (.second (.var rfl)))))
    (by simp [Memory.field, Core.Expr.weakenAt]; exact .first (.second (.second (.second (.var rfl)))))
    (.second (.second (.second (.second (.var rfl)))))
  cases copied with
  | destinationOverflow invalid =>
      refine ⟨.inLeft .unit (.word Memory.overflowReason), store, .language _, ?_, related, Frame.refl _ _ _⟩
      apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair destinationEvaluated (.pair sourceEvaluated lengthEvaluated))))
      exact .ifFalse (by simpa only [invalid] using validDestination) (.inLeft .word)
  | sourceOverflow destinationValid invalid =>
      refine ⟨.inLeft .unit (.word Memory.overflowReason), store, .language _, ?_, related, Frame.refl _ _ _⟩
      apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair destinationEvaluated (.pair sourceEvaluated lengthEvaluated))))
      exact .ifTrue (by simpa only [destinationValid] using validDestination)
        (.ifFalse (by simpa only [invalid] using validSource) (.inLeft .word))
  | @done destinationSize size words destinationValid sourceValid destinationTouched sourceTouched copied =>
      have touchedDestination := touch_evaluates (environment := input :: environment)
        (reference := Memory.field 1 5 (.var 0)) (offsetExpr := Memory.field 2 5 (.var 0)) (lengthExpr := Memory.field 4 5 (.var 0))
        (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
        (.second (.second (.second (.second (.var rfl))))) related.size
      have destinationRelated := related.touch destinationTouched
      have touchedSource := touch_evaluates (environment := .unit :: input :: environment)
        (reference := Memory.field 1 5 (.var 1)) (offsetExpr := Memory.field 3 5 (.var 1)) (lengthExpr := Memory.field 4 5 (.var 1))
        (.first (.second (.var rfl))) (.first (.second (.second (.second (.var rfl)))))
        (.second (.second (.second (.second (.var rfl))))) destinationRelated.size
      have sourceRelated := destinationRelated.touch sourceTouched
      simp only [touchResult, destinationTouched] at touchedDestination
      simp only [touchResult, sourceTouched] at touchedSource
      obtain ⟨final, evaluated, finalRelated, framed⟩ := copyLoop_preserves copied
        (environment := .unit :: .unit :: input :: environment)
        (sourceMapping := .loadCell (Memory.field 0 5 (.var 2))) (destinationExpr := Memory.field 2 5 (.var 2))
        (sourceExpr := Memory.field 3 5 (.var 2)) (lengthExpr := Memory.field 4 5 (.var 2))
        (memoryRef := Memory.field 0 5 (.var 2)) sourceRelated
        (.loadCell (.first (.var rfl)) sourceRelated.memory) (.first (.second (.second (.var rfl))))
        (.first (.second (.second (.second (.var rfl))))) (.second (.second (.second (.second (.var rfl))))) (.first (.var rfl))
      refine ⟨.inRight .word .unit, final, .value .unit, ?_, finalRelated,
        ((Frame.touch _ _ _ _ _ _).trans (Frame.touch _ _ _ _ _ _)).trans framed⟩
      apply Evaluates.letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair destinationEvaluated (.pair sourceEvaluated lengthEvaluated))))
      apply Evaluates.ifTrue (by simpa only [destinationValid] using validDestination)
      apply Evaluates.ifTrue (by simpa only [sourceValid] using validSource)
      exact LanguageResult.bind_success .unit touchedDestination (LanguageResult.bind_success .unit touchedSource evaluated)


set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem copyPackedFrom_rename (memory size destination mapping source length : Core.Expr) (renameIndices : Renaming) :
    (Memory.copyPackedFrom memory size destination mapping source length).rename renameIndices =
      Memory.copyPackedFrom (memory.rename renameIndices) (size.rename renameIndices) (destination.rename renameIndices)
        (mapping.rename renameIndices) (source.rename renameIndices) (length.rename renameIndices) := by
  simp only [Memory.copyPackedFrom, Memory.packet, Core.Expr.rename]
  congr 1
  simp [    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.readMemoryWord, Memory.readMemoryByte, Memory.writeMemoryWord, Memory.writeMemoryByte,
    Memory.copyBody, Memory.copyStep, Memory.validRange, Memory.packet, Memory.field,
    Memory.number, Memory.add, Memory.sub,
    WordMapping.lookup, WordMapping.insert, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.insertBody, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt,
    WordMapping.cons, WordMapping.empty]
  all_goals (repeat' apply And.intro)
  all_goals rfl

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem mcopy_rename (memory size destination source length : Core.Expr) (renameIndices : Renaming) :
    (Memory.mcopy memory size destination source length).rename renameIndices =
      Memory.mcopy (memory.rename renameIndices) (size.rename renameIndices) (destination.rename renameIndices)
        (source.rename renameIndices) (length.rename renameIndices) := by
  simp only [Memory.mcopy, Memory.packet, Core.Expr.rename]
  congr 1
  simp [    LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.readMemoryWord, Memory.readMemoryByte, Memory.writeMemoryWord, Memory.writeMemoryByte,
    Memory.copyBody, Memory.copyStep, Memory.validRange, Memory.packet, Memory.field,
    Memory.number, Memory.add, Memory.sub,
    WordMapping.lookup, WordMapping.insert, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.insertBody, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt,
    WordMapping.cons, WordMapping.empty]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end Solcore.Frontend.RustHull.MemoryCopyCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RuntimeCodeCorrespondence
/-! Values of runtime builder inputs are retained under the actual lexical
binders introduced while allocating frames and collecting their results. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open CodeBuilder ScalarExecution

def CodeValue (depth : Nat) (environment : Core.Environment) (code : Code) (value : Core.Value) : Prop :=
  ∀ extra store, Core.Evaluates (extra ++ environment) store (code (depth + extra.length)) value store

theorem CodeValue.evaluates {depth : Nat} {environment : Core.Environment} {code : Code} {value : Core.Value}
    (related : CodeValue depth environment code value) (store : Core.Store) :
    Core.Evaluates environment store (code depth) value store := by
  simpa only [List.nil_append, List.length_nil, Nat.add_zero] using related [] store

theorem CodeValue.prepend {depth : Nat} {environment : Core.Environment} {code : Code} {value : Core.Value}
    (related : CodeValue depth environment code value) (earlier : Core.Environment) :
    CodeValue (depth + earlier.length) (earlier ++ environment) code value := by
  intro extra store
  simpa only [List.append_assoc, List.length_append, Nat.add_assoc, Nat.add_comm earlier.length extra.length]
    using related (extra ++ earlier) store

theorem CodeValue.bound (depth : Nat) (environment : Core.Environment) (value : Core.Value) :
    CodeValue (depth + 1) (value :: environment) (fun here => .var (here - depth - 1)) value := by
  intro extra store
  apply Core.Evaluates.var
  have index : depth + 1 + extra.length - depth - 1 = extra.length := by omega
  rw [index]
  simp

theorem CodeValue.number (value depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (CodeBuilder.number value) (.word (Core.Word.ofNatModulo value)) :=
  fun _ _ => .word

theorem CodeValue.boolean (value : Bool) (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (CodeBuilder.boolean value) (.bool value) := fun _ _ => .bool

theorem CodeValue.unit (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment CodeBuilder.unit .unit := fun _ _ => .unit

theorem CodeValue.empty (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment CodeBuilder.empty (Core.WordMapping.encode []) := fun _ _ => .construct .unit

theorem CodeValue.mapping (entries : Core.WordMapping.Entries) (depth : Nat) (environment : Core.Environment) :
    CodeValue depth environment (constant (Core.WordMapping.literal entries)) (Core.WordMapping.encode entries) :=
  fun _ _ => Core.WordMapping.literal_evaluates _ _ _

theorem CodeValue.part {depth : Nat} {environment : Core.Environment} {code : Code} {values : List Core.Value}
    (related : CodeValue depth environment code (bundleValues values)) {index : Nat} {value : Core.Value}
    (found : values[index]? = some value) :
    CodeValue depth environment (part index values.length code) value :=
  fun extra store => projectArgument_evaluates (related extra store) found

inductive CodeValues (depth : Nat) (environment : Core.Environment) : List Code → List Core.Value → Prop where
  | nil : CodeValues depth environment [] []
  | cons {code value codes values} (head : CodeValue depth environment code value)
      (tail : CodeValues depth environment codes values) : CodeValues depth environment (code :: codes) (value :: values)

theorem CodeValues.prepend {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) (earlier : Core.Environment) :
    CodeValues (depth + earlier.length) (earlier ++ environment) codes values := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.prepend earlier) ih

theorem CodeValues.append {depth : Nat} {environment : Core.Environment}
    {first second : List Code} {left right : List Core.Value}
    (heads : CodeValues depth environment first left) (tails : CodeValues depth environment second right) :
    CodeValues depth environment (first ++ second) (left ++ right) := by
  induction heads with
  | nil => exact tails
  | cons head tail ih => exact .cons head ih

theorem CodeValues.reverse {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) : CodeValues depth environment codes.reverse values.reverse := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => simpa only [List.reverse_cons] using ih.append (.cons head .nil)

theorem CodeValues.length {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) : codes.length = values.length := by
  induction related with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

theorem CodeValues.of_getElem? {depth : Nat} {environment : Core.Environment}
    {codes : List Code} {values : List Core.Value}
    (length : codes.length = values.length)
    (related : ∀ (index : Nat) code value, codes[index]? = some code → values[index]? = some value →
      CodeValue depth environment code value) : CodeValues depth environment codes values := by
  induction codes generalizing values with
  | nil => cases values <;> simp_all only [List.length_nil, List.length_cons, Nat.zero_ne_add_one]; exact .nil
  | cons code codes ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          refine .cons (related 0 code value rfl rfl) (ih (Nat.succ.inj length) ?_)
          intro index tailCode tailValue codeFound valueFound
          exact related (index + 1) tailCode tailValue codeFound valueFound

theorem CodeValue.packet {depth : Nat} {environment : Core.Environment} {codes : List Code} {values : List Core.Value}
    (related : CodeValues depth environment codes values) :
    CodeValue depth environment (packet codes) (bundleValues values) := by
  intro extra store
  induction related with
  | nil => exact .unit
  | @cons code value codes values head tail ih =>
      cases tail with
      | nil => exact head extra store
      | cons next rest => exact .pair (head extra store) ih

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemorySnapshotAlignedCorrespondence
/-! The aligned traversal retains the source entry order and installs one
ordinary recursive helper. Its recursive calls leave the store unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

def alignedInput (entries : MemorySemantics.Entries) (start last shift : Word) : Value :=
  bundleValues [WordMapping.encode entries, .word start, .word last, .word shift]

theorem alignedBody_evaluates (entries : MemorySemantics.Entries) (start last shift : Word)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody location captured) :
    Evaluates (alignedInput entries start last shift ::
      .cellRef (OptionalCell.cellType (WordMapping.helperType MemorySnapshot.parameter WordMapping.type)) location :: captured)
      store MemorySnapshot.alignedBody (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift entries))) store := by
  induction entries with
  | nil => exact .matchData (.first (.var rfl)) rfl rfl (.inRight (.construct .unit))
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      let payload : Value := .pair (.pair (.word key) (.word value)) (WordMapping.encode rest)
      let input := alignedInput ((key, value) :: rest) start last shift
      let reference : Value := .cellRef (OptionalCell.cellType (WordMapping.helperType MemorySnapshot.parameter WordMapping.type)) location
      let oldEnvironment := payload :: input :: reference :: captured
      let args := bundleValues [payload, input, reference]
      let environment := args :: oldEnvironment
      let argsCode : Code := fun here => .var (here - 0 - 1)
      have argsRelated : CodeValue 1 environment argsCode (bundleValues [payload, input, reference]) :=
        CodeValue.bound 0 oldEnvironment args
      have entryRelated := argsRelated.part (index := 0) rfl
      have pairRelated := entryRelated.part (values := [.pair (.word key) (.word value), WordMapping.encode rest]) (index := 0) rfl
      have keyRelated := pairRelated.part (values := [.word key, .word value]) (index := 0) rfl
      have valueRelated := pairRelated.part (values := [.word key, .word value]) (index := 1) rfl
      have tailRelated := entryRelated.part (values := [.pair (.word key) (.word value), WordMapping.encode rest]) (index := 1) rfl
      have inputRelated := argsRelated.part (index := 1) rfl
      have startRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 1) rfl
      have lastRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 2) rfl
      have shiftRelated := inputRelated.part (values := [WordMapping.encode ((key, value) :: rest), .word start, .word last, .word shift]) (index := 3) rfl
      have referenceRelated := argsRelated.part (index := 2) rfl
      let recurse : Code := fun depth => WordMapping.invoke MemorySnapshot.parameter WordMapping.type
        (part 2 3 argsCode depth)
        (packet [part 1 2 (part 0 3 argsCode), part 1 4 (part 1 3 argsCode),
          part 2 4 (part 1 3 argsCode), part 3 4 (part 1 3 argsCode)] depth)
      have recursed (extra : Environment) : Evaluates (extra ++ environment) store (recurse (1 + extra.length))
          (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest))) store := by
        apply WordMapping.invoke_evaluates ((referenceRelated.prepend extra).evaluates store) installed
        · have argument := (CodeValue.packet (.cons tailRelated (.cons startRelated (.cons lastRelated (.cons shiftRelated .nil))))).prepend
            (WordMapping.closure MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody location captured :: extra)
          simpa [Core.Expr.weakenAt, CodeBuilder.packet, CodeBuilder.part, argsCode, projectArgument, bundle,
            List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, environment]
            using argument.evaluates store
        · exact ih
      unfold MemorySnapshot.alignedBody
      apply Evaluates.matchData (constructor := WordMapping.consConstructor) (.first (.var rfl)) rfl rfl
      apply Evaluates.letE (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))
      by_cases before : start > key
      · simp only [MemorySnapshotSemantics.retain, before, ↓reduceIte]
        exact .ifTrue (.binary (startRelated.evaluates store) (keyRelated.evaluates store) (by simp [BinaryOp.apply, before])) (recursed [])
      · apply Evaluates.ifFalse (.binary (startRelated.evaluates store) (keyRelated.evaluates store) (by simp [BinaryOp.apply, before]))
        by_cases outside : key > Word.ofNatModulo ((wordModulus - 1) / 32)
        · simp only [MemorySnapshotSemantics.retain, before, outside, ↓reduceIte]
          exact .ifTrue (.binary (keyRelated.evaluates store) .word (by simp [BinaryOp.apply, outside])) (recursed [])
        · apply Evaluates.ifFalse (.binary (keyRelated.evaluates store) .word (by simp [BinaryOp.apply, outside]))
          apply Evaluates.letE (.binary (keyRelated.evaluates store) (startRelated.evaluates store) rfl)
          have last' := lastRelated.prepend [.word (key.sub start)]
          by_cases after : key.sub start > last
          · simp only [MemorySnapshotSemantics.retain, before, outside, after, ↓reduceIte]
            exact .ifTrue (.binary (.var rfl) (last'.evaluates store) (by simp [BinaryOp.apply, after])) (recursed [.word (key.sub start)])
          · simp only [MemorySnapshotSemantics.retain, before, outside, after, ↓reduceIte]
            apply Evaluates.ifFalse (.binary (.var rfl) (last'.evaluates store) (by simp [BinaryOp.apply, after]))
            apply LanguageResult.bind_success WordMapping.type (recursed [.word (key.sub start)])
            apply Evaluates.inRight
            apply Evaluates.construct
            apply Evaluates.pair
            · apply Evaluates.pair (.var rfl)
              have value' := valueRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              have shift' := shiftRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              have last'' := lastRelated.prepend [WordMapping.encode (MemorySnapshotSemantics.retain start last shift rest), .word (key.sub start)]
              by_cases finalWord : key.sub start == last
              · simp only [finalWord, ↓reduceIte]
                exact .ifTrue (.binary (.var rfl) (last''.evaluates store) (by simp [BinaryOp.apply, finalWord]))
                  (.binary (.binary (value'.evaluates store) (shift'.evaluates store) rfl) (shift'.evaluates store) rfl)
              · simp only [finalWord, Bool.false_eq_true, ↓reduceIte]
                exact .ifFalse (.binary (.var rfl) (last''.evaluates store) (by simp [BinaryOp.apply, finalWord])) (value'.evaluates store)
            · exact .var rfl

theorem aligned_evaluates {environment : Environment} {initial store : Store}
    {argument : Core.Expr} {entries : MemorySemantics.Entries} {start last shift : Word}
    (evaluated : Evaluates environment initial argument (alignedInput entries start last shift) store) :
    Evaluates environment initial (WordMapping.runHelper MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody argument)
      (.inRight .word (WordMapping.encode (MemorySnapshotSemantics.retain start last shift entries)))
      (WordMapping.installedStore store MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
        (alignedInput entries start last shift) environment) := by
  apply WordMapping.runHelper_evaluates evaluated
  apply alignedBody_evaluates
  simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]

end Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
end
