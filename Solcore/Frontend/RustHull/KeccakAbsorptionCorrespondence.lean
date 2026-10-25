import Solcore.Frontend.RustHull.KeccakSemantics
import Solcore.Frontend.RustHull.Keccak
import Solcore.Frontend.RustHull.MemoryCopyCorrespondence
import Solcore.Frontend.RustHull.KeccakStateCorrespondence

/-! Keccak absorption reads a retained memory mapping. Padding is computed
without memory writes; every allocated lookup helper remains in the store. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakAbsorptionCorrespondence
open Core LogsCorrespondence

theorem paddedByte_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr remainingExpr : Core.Expr} (words : MemorySemantics.Entries)
    (offset remaining : Word) (index : Nat)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode words) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (remainingEvaluated : Evaluates environment store remainingExpr (.word remaining) store) :
    ∃ suffix, Evaluates environment store (Keccak.paddedByte mapping offsetExpr remainingExpr index)
      (.inRight .word (.word (KeccakSemantics.paddedByte words offset remaining index))) (store ++ suffix) := by
  by_cases present : remaining > Word.ofNatModulo index
  · obtain ⟨suffix, evaluated⟩ := MemoryCopyCorrespondence.readMemoryByte_evaluates words
      (offsetExpr := Keccak.add offsetExpr (Keccak.number index))
      (offset.add (Word.ofNatModulo index)) mappingEvaluated (.binary offsetEvaluated .word rfl)
    refine ⟨suffix, ?_⟩
    simp only [KeccakSemantics.paddedByte, present, ↓reduceIte]
    exact .ifTrue (.binary remainingEvaluated .word (by simp only [BinaryOp.apply, present, decide_true])) evaluated
  · refine ⟨[], ?_⟩
    rw [List.append_nil]
    simp only [KeccakSemantics.paddedByte, present, ↓reduceIte]
    apply Evaluates.ifFalse (.binary remainingEvaluated .word (by simp only [BinaryOp.apply, present, decide_false]))
    apply Evaluates.inRight
    apply Evaluates.binary
      (leftValue := .word (if remaining == Word.ofNatModulo index then Word.ofNatModulo 1 else Word.zero))
      (rightValue := .word (Word.ofNatModulo (if index = 135 then 128 else 0)))
    · by_cases equal : remaining == Word.ofNatModulo index
      · simp only [equal, ↓reduceIte]
        exact .ifTrue (.binary remainingEvaluated .word
          (by simpa only [BinaryOp.apply] using congrArg (fun value => some (Value.bool value)) equal)) .word
      · simp only [equal]
        exact .ifFalse (.binary remainingEvaluated .word
          (by simpa only [BinaryOp.apply] using congrArg (fun value => some (Value.bool value)) (Bool.eq_false_iff.mpr equal))) .word
    · exact .word
    · rfl

theorem readLane_evaluates (count index : Nat) {environment : Environment} (store : Store)
    {mapping offsetExpr remainingExpr accumulatorExpr : Core.Expr} {words : MemorySemantics.Entries}
    {offset remaining accumulator : Word}
    (mappingStable : Stable environment mapping (WordMapping.encode words))
    (offsetStable : Stable environment offsetExpr (.word offset))
    (remainingStable : Stable environment remainingExpr (.word remaining))
    (accumulatorStable : Stable environment accumulatorExpr (.word accumulator)) :
    ∃ suffix, Evaluates environment store
      (Keccak.readLane count index mapping offsetExpr remainingExpr accumulatorExpr)
      (.inRight .word (.word (KeccakSemantics.readLane count index words offset remaining accumulator))) (store ++ suffix) := by
  induction count generalizing environment store index mapping offsetExpr remainingExpr accumulatorExpr accumulator with
  | zero => exact ⟨[], by simpa only [List.append_nil, Keccak.readLane, KeccakSemantics.readLane,
      LanguageResult.success] using Evaluates.inRight (accumulatorStable.evaluates store)⟩
  | succ count ih =>
      obtain ⟨first, byte⟩ := paddedByte_evaluates words offset remaining index
        (mappingStable.evaluates store) (offsetStable.evaluates store) (remainingStable.evaluates store)
      let value := KeccakSemantics.paddedByte words offset remaining index
      have updated : Stable (.word value :: environment)
          (.binary .wordOr (accumulatorExpr.weakenAt 0) (Keccak.shift (.var 0) (8 * (index % 8))))
          (.word (accumulator.bitOr (value.shiftLeft (Word.ofNatModulo (8 * (index % 8)))))) := by
        intro extra current
        exact .binary (accumulatorStable.prepend (.word value) extra current)
          (.binary (Stable.var (index := 0) rfl extra current) .word rfl) rfl
      obtain ⟨second, rest⟩ := ih (index + 1) (store ++ first)
        (mappingStable.prepend (.word value)) (offsetStable.prepend (.word value))
        (remainingStable.prepend (.word value)) updated
      refine ⟨first ++ second, ?_⟩
      rw [← List.append_assoc]
      exact LanguageResult.bind_success .word byte rest

private theorem stable_move {environment : Environment} {expression : Core.Expr} {value : Value}
    (stable : Stable environment expression value) (extraValues : Environment) :
    Stable (extraValues ++ environment) (Keccak.move expression extraValues.length) value := by
  intro extra store
  unfold Keccak.move
  rw [Core.Expr.rename_comp]
  have renamed : Renaming.comp (fun index => index + extra.length) (fun index => index + extraValues.length) =
      (fun index => index + (extra ++ extraValues).length) := by
    funext index
    simp only [Renaming.comp, List.length_append]
    omega
  rw [renamed]
  simpa only [List.append_assoc] using stable (extra ++ extraValues) store

private theorem binds_evaluates {environment : Environment} (store : Store)
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

private theorem digest_fold_evaluates {environment : Environment} {store : Store}
    {stateExpr accumulatorExpr : Core.Expr} {state : KeccakSemantics.State} {accumulator : Word}
    (length : state.length = 25) (stateEvaluated : Evaluates environment store stateExpr (KeccakPermutationCorrespondence.stateValue state) store)
    (accumulatorEvaluated : Evaluates environment store accumulatorExpr (.word accumulator) store)
    (indices : List Nat) (bounded : ∀ index ∈ indices, index < 32) :
    Evaluates environment store
      (indices.foldl (fun output index => .binary .wordOr output
        (Keccak.shift (.binary .wordByte (Keccak.number (31 - index % 8)) (Keccak.lane (index / 8) stateExpr))
          (8 * (31 - index)))) accumulatorExpr)
      (.word (indices.foldl (fun output index => output.bitOr
        ((Word.byteAt (Word.ofNatModulo (31 - index % 8)) (KeccakSemantics.lane state (index / 8))).shiftLeft
          (Word.ofNatModulo (8 * (31 - index))))) accumulator)) store := by
  induction indices generalizing accumulator accumulatorExpr with
  | nil => exact accumulatorEvaluated
  | cons index indices ih =>
      have bound := bounded index (.head _)
      exact ih (.binary accumulatorEvaluated
        (.binary (.binary .word (KeccakPermutationCorrespondence.lane_evaluates length (by omega) stateEvaluated) rfl)
          .word rfl) rfl) (fun index member => bounded index (.tail _ member))

theorem digest_evaluates {environment : Environment} {store : Store}
    {stateExpr : Core.Expr} {state : KeccakSemantics.State}
    (length : state.length = 25)
    (stateEvaluated : Evaluates environment store stateExpr (KeccakPermutationCorrespondence.stateValue state) store) :
    Evaluates environment store (Keccak.digest stateExpr) (.word (KeccakSemantics.digest state)) store :=
  digest_fold_evaluates length stateEvaluated .word _ (fun _ member => List.mem_range.mp member)

theorem absorbBlock_length (words : MemorySemantics.Entries) (offset remaining : Word) (state : KeccakSemantics.State) :
    (KeccakSemantics.absorbBlock words offset remaining state).length = 25 := by
  simp only [KeccakSemantics.absorbBlock, List.length_map, List.length_range]

/-- The seventeen rate lanes are read in order, then combined with the full
25-lane state. Lookup allocations append to the store throughout the block. -/
theorem absorbBlock_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr remainingExpr stateExpr : Core.Expr}
    {words : MemorySemantics.Entries} {offset remaining : Word} {state : KeccakSemantics.State}
    (length : state.length = 25)
    (mappingStable : Stable environment mapping (WordMapping.encode words))
    (offsetStable : Stable environment offsetExpr (.word offset))
    (remainingStable : Stable environment remainingExpr (.word remaining))
    (stateStable : Stable environment stateExpr (KeccakPermutationCorrespondence.stateValue state)) :
    ∃ suffix, Evaluates environment store (Keccak.absorbBlock mapping offsetExpr remainingExpr stateExpr)
      (.inRight .word (KeccakPermutationCorrespondence.stateValue (KeccakSemantics.absorbBlock words offset remaining state)))
      (store ++ suffix) := by
  unfold Keccak.absorbBlock
  apply binds_evaluates store Keccak.stateType
    (values := (List.range 17).map (fun index => Value.word (KeccakSemantics.readLane 8 (8 * index) words offset remaining Word.zero)))
  · simp only [List.length_map, List.length_range]
  · intro index expression value extraValues current found known count
    have bound : index < 17 := by
      simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp found).1
    simp only [List.getElem?_map, List.getElem?_range, bound, Option.map_some, Option.some.injEq] at found known
    subst expression
    subst value
    have mappingMoved := stable_move mappingStable extraValues
    have offsetMoved := stable_move offsetStable extraValues
    have remainingMoved := stable_move remainingStable extraValues
    rw [count] at mappingMoved offsetMoved remainingMoved
    exact readLane_evaluates 8 (8 * index) current mappingMoved offsetMoved remainingMoved (Stable.word _ Word.zero)
  · intro current
    apply Evaluates.inRight
    apply KeccakPermutationCorrespondence.packet_evaluates
      (by simp only [KeccakSemantics.absorbBlock, List.length_map, List.length_range])
    intro index expression value found known
    have bound : index < 25 := by
      simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp found).1
    simp only [KeccakSemantics.absorbBlock, List.getElem?_map, List.getElem?_range, bound,
      Option.map_some, Option.some.injEq] at found known
    subst expression
    subst value
    have stateEvaluated := stateStable
      (((List.range 17).map (fun index => Value.word (KeccakSemantics.readLane 8 (8 * index) words offset remaining Word.zero))).reverse) current
    simp only [List.length_reverse, List.length_map, List.length_range] at stateEvaluated
    have lane := KeccakPermutationCorrespondence.lane_evaluates length bound stateEvaluated
    by_cases read : index < 17
    · simp only [read, ↓reduceIte]
      apply Evaluates.binary (rightValue := .word (KeccakSemantics.readLane 8 (8 * index) words offset remaining Word.zero)) lane
      · apply Evaluates.var
        have back : 16 - index < 17 := by omega
        rw [List.getElem?_append_left (by simpa only [List.length_reverse, List.length_map, List.length_range] using back),
          List.getElem?_reverse (by simpa only [List.length_map, List.length_range] using back)]
        simp only [List.length_map, List.length_range]
        have same : 17 - 1 - (16 - index) = index := by omega
        simp only [same, List.getElem?_map, List.getElem?_range, read, Option.map_some]
      · rfl
    · simpa only [read, ↓reduceIte, Keccak.move] using lane

end Solcore.Frontend.RustHull.KeccakAbsorptionCorrespondence
