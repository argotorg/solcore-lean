import Solcore.Frontend.RustHull.MemoryCopySemantics
import Solcore.Frontend.RustHull.LogsCorrespondence

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
