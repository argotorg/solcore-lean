import Solcore.Frontend.RustHull.Sha256Implementation
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.ScalarInputCorrespondence

/-! SHA-256 block reading over a retained memory mapping. Padding bytes are
computed without memory writes; every lookup helper allocation is retained. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256BlockCorrespondence
open Core LogsCorrespondence

abbrev wordsValue (words : List Word) : Value := ScalarExecution.bundleValues (words.map Value.word)

theorem paddedByte_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr remainingExpr bitsExpr markerExpr : Core.Expr} (words : MemorySemantics.Entries)
    (offset remaining bits : Word) (markerUsed : Bool) (index : Nat)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode words) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (remainingEvaluated : Evaluates environment store remainingExpr (.word remaining) store)
    (bitsEvaluated : Evaluates environment store bitsExpr (.word bits) store)
    (markerEvaluated : Evaluates environment store markerExpr (.bool markerUsed) store) :
    ∃ suffix, Evaluates environment store
      (Sha256Implementation.paddedByte mapping offsetExpr remainingExpr bitsExpr markerExpr index)
      (.inRight .word (.word (Sha256Semantics.paddedByte words offset remaining bits markerUsed index)))
      (store ++ suffix) := by
  by_cases present : remaining > Word.ofNatModulo index
  · obtain ⟨suffix, evaluated⟩ := MemoryCopyCorrespondence.readMemoryByte_evaluates words
      (offsetExpr := HashBlocks.add offsetExpr (HashBlocks.number index))
      (offset.add (Word.ofNatModulo index)) mappingEvaluated (.binary offsetEvaluated .word rfl)
    refine ⟨suffix, ?_⟩
    simp only [Sha256Semantics.paddedByte, present, ↓reduceIte]
    exact .ifTrue (.binary remainingEvaluated .word (by simp only [BinaryOp.apply, present, decide_true])) evaluated
  · refine ⟨[], ?_⟩
    rw [List.append_nil]
    apply Evaluates.ifFalse (.binary remainingEvaluated .word (by simp only [BinaryOp.apply, present, decide_false]))
    apply Evaluates.inRight
    have markerTest : Evaluates environment store
        (.ifE (.binary .wordEq remainingExpr (HashBlocks.number index)) (.unary .boolNot markerExpr) (.bool false))
        (.bool (if remaining == Word.ofNatModulo index then !markerUsed else false)) store := by
      by_cases equal : remaining == Word.ofNatModulo index
      · simp only [equal, ↓reduceIte]
        exact .ifTrue (.binary remainingEvaluated .word
          (by simpa only [BinaryOp.apply] using congrArg (fun value => some (Value.bool value)) equal))
          (.unary markerEvaluated rfl)
      · simp only [equal]
        have different := Bool.eq_false_iff.mpr equal
        exact .ifFalse (.binary remainingEvaluated .word
          (by simpa only [BinaryOp.apply] using congrArg (fun value => some (Value.bool value)) different)) .bool
    unfold Sha256Semantics.paddedByte
    rw [if_neg present]
    by_cases marker : (if remaining == Word.ofNatModulo index then !markerUsed else false) = true
    · rw [if_pos marker]
      rw [marker] at markerTest
      exact .ifTrue markerTest .word
    · rw [if_neg marker]
      rw [Bool.not_eq_true] at marker
      rw [marker] at markerTest
      apply Evaluates.ifFalse markerTest
      by_cases early : index < 56
      · simp only [early, ↓reduceIte]
        exact .word
      · simp only [early, ↓reduceIte]
        by_cases tail : Word.ofNatModulo 56 > remaining
        · simp only [tail, ↓reduceIte]
          exact .ifTrue (.binary .word remainingEvaluated (by simp only [BinaryOp.apply, tail, decide_true]))
            (.binary .word bitsEvaluated rfl)
        · simp only [tail, ↓reduceIte]
          exact .ifFalse (.binary .word remainingEvaluated (by simp only [BinaryOp.apply, tail, decide_false])) .word

theorem readWord_evaluates (count index : Nat) {environment : Environment} (store : Store)
    {mapping offsetExpr remainingExpr bitsExpr markerExpr accumulatorExpr : Core.Expr}
    {words : MemorySemantics.Entries} {offset remaining bits accumulator : Word} {markerUsed : Bool}
    (mappingStable : Stable environment mapping (WordMapping.encode words))
    (offsetStable : Stable environment offsetExpr (.word offset))
    (remainingStable : Stable environment remainingExpr (.word remaining))
    (bitsStable : Stable environment bitsExpr (.word bits))
    (markerStable : Stable environment markerExpr (.bool markerUsed))
    (accumulatorStable : Stable environment accumulatorExpr (.word accumulator)) :
    ∃ suffix, Evaluates environment store
      (Sha256Implementation.readWord count index mapping offsetExpr remainingExpr bitsExpr markerExpr accumulatorExpr)
      (.inRight .word (.word (Sha256Semantics.readWord words offset remaining bits markerUsed count index accumulator)))
      (store ++ suffix) := by
  induction count generalizing environment store index mapping offsetExpr remainingExpr bitsExpr markerExpr
      accumulatorExpr accumulator with
  | zero => exact ⟨[], by simpa only [List.append_nil, Sha256Implementation.readWord, Sha256Semantics.readWord,
      LanguageResult.success] using Evaluates.inRight (accumulatorStable.evaluates store)⟩
  | succ count ih =>
      obtain ⟨first, byte⟩ := paddedByte_evaluates words offset remaining bits markerUsed index
        (mappingStable.evaluates store) (offsetStable.evaluates store) (remainingStable.evaluates store)
        (bitsStable.evaluates store) (markerStable.evaluates store)
      let value := Sha256Semantics.paddedByte words offset remaining bits markerUsed index
      have updated : Stable (.word value :: environment)
          (.binary .wordOr (accumulatorExpr.weakenAt 0) (HashBlocks.shift (.var 0) (8 * (3 - index % 4))))
          (.word (accumulator.bitOr (value.shiftLeft (Word.ofNatModulo (8 * (3 - index % 4)))))) := by
        intro extra current
        exact .binary (accumulatorStable.prepend (.word value) extra current)
          (.binary (Stable.var (index := 0) rfl extra current) .word rfl) rfl
      obtain ⟨second, rest⟩ := ih (index + 1) (store ++ first)
        (mappingStable.prepend (.word value)) (offsetStable.prepend (.word value))
        (remainingStable.prepend (.word value)) (bitsStable.prepend (.word value))
        (markerStable.prepend (.word value)) updated
      refine ⟨first ++ second, ?_⟩
      rw [← List.append_assoc]
      exact LanguageResult.bind_success .word byte rest

theorem stable_move {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (extraValues : Environment) :
    Stable (extraValues ++ environment) (HashBlocks.move expression extraValues.length) value := by
  intro extra store
  unfold HashBlocks.move
  rw [Core.Expr.rename_comp]
  have renamed : Renaming.comp (fun index => index + extra.length) (fun index => index + extraValues.length) =
      (fun index => index + (extra ++ extraValues).length) := by
    funext index
    simp only [Renaming.comp, List.length_append]
    omega
  rw [renamed]
  simpa only [List.append_assoc] using stable (extra ++ extraValues) store

theorem binds_evaluates {environment : Environment} (store : Store)
    (resultType : Core.Ty) {expressions : List Core.Expr} {values : List Value} {body : Core.Expr} {target : Value}
    (length : expressions.length = values.length)
    (steps : ∀ (index : Nat) expression value extraValues current,
      expressions[index]? = some expression → values[index]? = some value → extraValues.length = index →
      ∃ suffix, Evaluates (extraValues ++ environment) current expression (.inRight .word value) (current ++ suffix))
    (completed : ∀ current, Evaluates (values.reverse ++ environment) current body target current) :
    ∃ suffix, Evaluates environment store (expressions.foldr (LanguageResult.bind resultType) body)
      target (store ++ suffix) := by
  induction expressions generalizing values environment store with
  | nil =>
      have empty := List.length_eq_zero_iff.mp length.symm
      subst values
      exact ⟨[], by simpa only [List.foldr_nil, List.reverse_nil, List.nil_append, List.append_nil] using completed store⟩
  | cons expression expressions ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          obtain ⟨first, head⟩ := steps 0 expression value [] store rfl rfl rfl
          obtain ⟨second, tail⟩ := ih (store ++ first) (Nat.succ.inj length)
            (environment := value :: environment)
            (fun index expression value' extraValues current found known bound => by
              have evaluated := steps (index + 1) expression value' (extraValues ++ [value]) current found known
                (by simp only [List.length_append, List.length_singleton, bound])
              simpa only [List.append_assoc, List.singleton_append] using evaluated)
            (fun current => by simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using completed current)
          refine ⟨first ++ second, ?_⟩
          rw [← List.append_assoc]
          exact LanguageResult.bind_success resultType head tail

theorem packet_evaluates {environment : Environment} {store : Store}
    {expressions : List Core.Expr} {values : List Word}
    (length : expressions.length = values.length)
    (evaluated : ∀ (index : Nat) expression value, expressions[index]? = some expression →
      values[index]? = some value → Evaluates environment store expression (.word value) store) :
    Evaluates environment store (HashBlocks.packet expressions) (wordsValue values) store := by
  induction expressions generalizing values with
  | nil =>
      cases values with
      | nil => exact .unit
      | cons value values => simp at length
  | cons expression expressions ih =>
      cases values with
      | nil => simp at length
      | cons value values =>
          have head := evaluated 0 expression value rfl rfl
          have tail := ih (Nat.succ.inj length) (fun index expression value found known =>
            evaluated (index + 1) expression value found known)
          cases expressions with
          | nil => cases values with
            | nil => exact head
            | cons value values => simp at length
          | cons next expressions =>
              cases values with
              | nil => simp at length
              | cons next values => exact .pair head tail

/-- Mapping, offset, remaining length, bit length, chaining state and marker. -/
def parametersValue (words : MemorySemantics.Entries) (offset remaining bits : Word) (state : List Word)
    (markerUsed : Bool) : Value :=
  .pair (WordMapping.encode words) (.pair (.word offset) (.pair (.word remaining) (.pair (.word bits)
    (.pair (wordsValue state) (.bool markerUsed)))))

theorem readBlock_length (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) :
    (Sha256Semantics.readBlock words offset remaining bits markerUsed).length = 16 := by
  simp only [Sha256Semantics.readBlock, List.length_map, List.length_range]

/-- The sixteen message words are read in order. Lookup allocations append to
the store throughout the block. -/
theorem readBlock_evaluates {environment : Environment} (store : Store) {parameters : Core.Expr}
    {words : MemorySemantics.Entries} {offset remaining bits : Word} {state : List Word} {markerUsed : Bool}
    (parametersStable : Stable environment parameters (parametersValue words offset remaining bits state markerUsed)) :
    ∃ suffix, Evaluates environment store (Sha256Implementation.readBlock parameters)
      (.inRight .word (wordsValue (Sha256Semantics.readBlock words offset remaining bits markerUsed)))
      (store ++ suffix) := by
  unfold Sha256Implementation.readBlock
  apply binds_evaluates store HashBlocks.blockType
    (values := (List.range 16).map (fun index =>
      Value.word (Sha256Semantics.readWord words offset remaining bits markerUsed 4 (4 * index) (Word.ofNatModulo 0))))
  · simp only [List.length_map, List.length_range]
  · intro index expression value extraValues current found known count
    have bound : index < 16 := by
      simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp found).1
    simp only [List.getElem?_map, List.getElem?_range, bound, Option.map_some, Option.some.injEq] at found known
    subst expression
    subst value
    have moved := stable_move parametersStable extraValues
    rw [count] at moved
    exact readWord_evaluates 4 (4 * index) current moved.first moved.second.first moved.second.second.first
      moved.second.second.second.first moved.second.second.second.second.second (Stable.word _ _)
  · intro current
    apply Evaluates.inRight
    apply packet_evaluates (by simp only [Sha256Semantics.readBlock, List.length_map, List.length_range])
    intro index expression value found known
    have bound : index < 16 := by
      simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp found).1
    simp only [Sha256Semantics.readBlock, List.getElem?_map, List.getElem?_range, bound,
      Option.map_some, Option.some.injEq] at found known
    subst expression
    subst value
    apply Evaluates.var
    have back : 15 - index < 16 := by omega
    rw [List.getElem?_append_left (by simpa only [List.length_reverse, List.length_map, List.length_range] using back),
      List.getElem?_reverse (by simpa only [List.length_map, List.length_range] using back)]
    simp only [List.length_map, List.length_range]
    have same : 16 - 1 - (15 - index) = index := by omega
    simp only [same, List.getElem?_map, List.getElem?_range, bound, Option.map_some]

end Solcore.Frontend.RustHull.Sha256BlockCorrespondence
