import Solcore.Frontend.RustHull.MemorySnapshotAlignedCorrespondence
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.EffectStateCorrespondence

/-! Snapshot extraction retains every pre-existing store cell. Both the
aligned traversal and unaligned copying preserve their actual allocations. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
open Core CodeBuilder Correspondence ScalarExecution

inductive ResultRel : Semantics.Result MemorySemantics.Entries → Value → Prop where
  | returned (entries : MemorySemantics.Entries) : ResultRel (.value entries) (.inRight .word (WordMapping.encode entries))
  | language (reason : Word) : ResultRel (.fault (.language reason)) (.inLeft WordMapping.type (.word reason))

def extractTail (args size : Code) : Code :=
  let source := part 0 3 args
  let offset := part 1 3 args
  let length := part 2 3 args
  choose (binary .wordEq length (number 0)) (success empty) <|
  choose (binary .wordEq (binary .wordMod offset (number 32)) (number 0))
    (fun depth => WordMapping.runHelper MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
      (packet [source, binary .wordDiv offset (number 32),
        binary .wordDiv (binary .wordSub length (number 1)) (number 32),
        binary .wordMul (binary .wordMod
          (binary .wordSub (number 32) (binary .wordMod length (number 32))) (number 32))
          (number 8)] depth))
    (bind (allocate WordMapping.type empty) fun destination =>
      bindResult WordMapping.type (fun depth => Memory.copyPackedFrom
        (destination depth) (size depth) (number 0 depth) (source depth) (offset depth) (length depth)) fun _ =>
      success (load destination))

private theorem touch_idempotent {size offset length expanded : Word}
    (checked : MemorySemantics.touchSize? size offset length = some expanded) :
    MemorySemantics.touchSize? expanded offset length = some expanded := by
  unfold MemorySemantics.touchSize? at checked ⊢
  split at checked
  · cases checked
    simp_all
  · dsimp only at checked
    split at checked
    · cases checked
    · split at checked
      · cases checked
      · split at checked <;> cases checked <;> simp_all
        intro contrary
        exact False.elim ((Nat.not_lt_of_ge ‹MemorySemantics.rounded (offset.add length) ≤ size›) contrary)

private theorem touched_retains (store : Store) (length : Word) :
    StoreRetains store (MemoryCorrespondence.touchStore (store ++ [.word Word.zero]) store.length Word.zero Word.zero length) where
  length_le := by rw [MemoryCorrespondence.touchStore_length]; simp
  read := by
    intro location bounded
    rw [MemoryCorrespondence.touchStore_other _ (by omega)]
    simp only [Store.read?, List.getElem?_append_left bounded]

theorem extract_preserves {entries : MemorySemantics.Entries} {offset length : Word}
    {result : Semantics.Result MemorySemantics.Entries}
    (extracted : MemorySnapshotSemantics.Extract entries offset length result)
    {environment : Environment} {store : Store} {mapping offsetExpr lengthExpr : Core.Expr}
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode entries) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, ResultRel result target ∧
      Evaluates environment store (MemorySnapshot.extract mapping offsetExpr lengthExpr) target final ∧
      StoreRetains store final := by
  let input := bundleValues [WordMapping.encode entries, .word offset, .word length]
  let argsCode : Code := fun here => .var (here - 0 - 1)
  let sizeCode : Code := fun here => .var (here - 1 - 1)
  let sizeRef : Value := .cellRef .word store.length
  let allocated := store ++ [Value.word Word.zero]
  let touchedStore := MemoryCorrespondence.touchStore allocated store.length Word.zero Word.zero length
  let entered := [Value.unit, sizeRef, input] ++ environment
  have argsRelated : CodeValue 1 (input :: environment) argsCode (bundleValues [WordMapping.encode entries, .word offset, .word length]) :=
    CodeValue.bound 0 environment input
  have sourceRelated := argsRelated.part (index := 0) rfl
  have offsetRelated := argsRelated.part (index := 1) rfl
  have lengthRelated := argsRelated.part (index := 2) rfl
  have sizeRelated : CodeValue 2 (sizeRef :: input :: environment) sizeCode (.cellRef .word store.length) :=
    CodeValue.bound 1 (input :: environment) sizeRef
  have sizeRead : allocated.read? store.length = some (.word Word.zero) := by simp [allocated, Store.read?]
  have touched := MemoryCorrespondence.touch_evaluates (offset := Word.zero) (sizeRelated.evaluates allocated) .word
    ((lengthRelated.prepend [sizeRef]).evaluates allocated) sizeRead
  have enter {size : Word} (checked : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
      {target : Value} {final : Store}
      (continued : Evaluates entered touchedStore (extractTail argsCode sizeCode 3) target final) :
      Evaluates environment store (MemorySnapshot.extract mapping offsetExpr lengthExpr) target final := by
    apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated lengthEvaluated))
    apply Evaluates.letE (bodyStore := allocated) (.newCell .word)
    apply LanguageResult.bind_success WordMapping.type
    · have successful := touched
      simp only [MemoryCorrespondence.touchResult, checked] at successful
      exact successful
    · exact continued
  cases extracted with
  | overflow invalid =>
      simp only [MemoryCorrespondence.touchResult, invalid, MemoryCorrespondence.touchStore_failure invalid] at touched
      refine ⟨.inLeft WordMapping.type (.word (Word.ofNatModulo 6)), allocated, .language _, ?_, StoreRetains.append _ _⟩
      apply Evaluates.letE (.pair mappingEvaluated (.pair offsetEvaluated lengthEvaluated))
      apply Evaluates.letE (bodyStore := allocated) (.newCell .word)
      exact LanguageResult.bind_failure WordMapping.type touched
  | empty zero =>
      subst length
      refine ⟨.inRight .word (WordMapping.encode []), touchedStore, .returned _, enter rfl ?_, touched_retains store Word.zero⟩
      exact .ifTrue (.binary ((lengthRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word rfl) (.inRight (.construct .unit))
  | aligned checked nonempty alignedOffset =>
      have source' := sourceRelated.prepend [.unit, sizeRef]
      have offset' := offsetRelated.prepend [.unit, sizeRef]
      have length' := lengthRelated.prepend [.unit, sizeRef]
      have copied := aligned_evaluates (start := offset.udiv (Word.ofNatModulo 32))
        (last := MemorySnapshotSemantics.lastIndex length) (shift := MemorySnapshotSemantics.padding length)
        (.pair (source'.evaluates touchedStore) (.pair (.binary (op := .wordDiv) (offset'.evaluates touchedStore) .word rfl)
          (.pair (.binary (op := .wordDiv) (.binary (op := .wordSub) (length'.evaluates touchedStore) .word rfl) .word rfl)
            (.binary (op := .wordMul) (.binary (op := .wordMod) (.binary (op := .wordSub) .word
              (.binary (op := .wordMod) (length'.evaluates touchedStore) .word rfl) rfl) .word rfl) .word rfl))))
      let final := WordMapping.installedStore touchedStore MemorySnapshot.parameter WordMapping.type MemorySnapshot.alignedBody
        (alignedInput entries (offset.udiv (Word.ofNatModulo 32)) (MemorySnapshotSemantics.lastIndex length)
          (MemorySnapshotSemantics.padding length)) entered
      refine ⟨_, final, .returned _, enter checked ?_, (touched_retains store length).trans (StoreRetains.append _ _)⟩
      apply Evaluates.ifFalse (.binary (length'.evaluates touchedStore) .word (by simp [BinaryOp.apply, nonempty, show Word.ofNatModulo 0 = Word.zero from rfl]))
      apply Evaluates.ifTrue (.binary (.binary (offset'.evaluates touchedStore) .word rfl) .word (by simp [BinaryOp.apply, alignedOffset, show Word.ofNatModulo 0 = Word.zero from rfl]))
      exact copied
  | @copied size words checked nonempty unaligned copied =>
      let destination := touchedStore.length
      let destinationRef : Value := .cellRef WordMapping.type destination
      let copyStore := touchedStore ++ [WordMapping.encode []]
      have touchedSize := MemoryCorrespondence.touchStore_read sizeRead checked
      have touchedLength : touchedStore.length = store.length + 1 := by
        rw [MemoryCorrespondence.touchStore_length]
        simp [allocated]
      have destinationRelated := CodeValue.bound 3 entered destinationRef
      have source' := sourceRelated.prepend [destinationRef, .unit, sizeRef]
      have offset' := offsetRelated.prepend [destinationRef, .unit, sizeRef]
      have length' := lengthRelated.prepend [destinationRef, .unit, sizeRef]
      have size' := sizeRelated.prepend [destinationRef, .unit]
      have memoryRelated : MemoryCorrespondence.StateRel destination store.length ⟨[], size⟩ copyStore := by
        refine ⟨by dsimp [destination]; omega, ?_, ?_⟩
        · simp [copyStore, destination, Store.read?]
        · simpa only [copyStore, Store.read?, List.getElem?_append_left (by omega : store.length < touchedStore.length)] using touchedSize
      obtain ⟨target, final, related, evaluated, finalRelated, framed⟩ := MemoryCopyCorrespondence.copyPackedFrom_preserves
        (MemoryCopySemantics.From.done (touch_idempotent checked) copied) memoryRelated
        (destinationRelated.evaluates copyStore) (size'.evaluates copyStore) .word
        (source'.evaluates copyStore) (offset'.evaluates copyStore) (length'.evaluates copyStore)
      cases related with
      | value related =>
          cases related
          have retained : StoreRetains store final := by
            refine ⟨?_, ?_⟩
            · have bound := framed.length
              simp only [copyStore, List.length_append, List.length_cons, List.length_nil] at bound
              omega
            · intro location bounded
              have found : store.read? location = some store[location] := List.getElem?_eq_getElem bounded
              have same := framed.read location _ (by dsimp [destination]; omega) (by omega)
                (by simpa only [copyStore, Store.read?, List.getElem?_append_left (by omega : location < touchedStore.length)] using
                  ((touched_retains store length).read location bounded).trans found)
              exact same.trans found.symm
          refine ⟨.inRight .word (WordMapping.encode words), final, .returned _, enter checked ?_, retained⟩
          apply Evaluates.ifFalse (.binary ((lengthRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word (by simp [BinaryOp.apply, nonempty, show Word.ofNatModulo 0 = Word.zero from rfl]))
          apply Evaluates.ifFalse (.binary (.binary ((offsetRelated.prepend [.unit, sizeRef]).evaluates touchedStore) .word rfl) .word (by simp [BinaryOp.apply, unaligned, show Word.ofNatModulo 0 = Word.zero from rfl]))
          apply Evaluates.letE (bodyStore := copyStore) (.newCell (.construct .unit))
          apply LanguageResult.bind_success WordMapping.type evaluated
          exact .inRight (.loadCell ((destinationRelated.prepend [.unit]).evaluates final) finalRelated.memory)

end Solcore.Frontend.RustHull.MemorySnapshotCorrespondence
