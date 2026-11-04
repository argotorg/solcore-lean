import Solcore.Frontend.RustHull.Semantics.Digests
import Solcore.Frontend.RustHull.Precompiles
import Solcore.Frontend.RustHull.Internal.LoweringFacts
import Solcore.Frontend.RustHull.Internal.MemoryState

/-!
# Digest proofs

The Core Keccak, SHA-256 and RIPEMD-160 against their independent definitions, block by block.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakStateCorrespondence
/-! The emitted Keccak permutation evaluates to the independent lane algorithm.
Round closures preserve the store, including every existing helper allocation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
open Core

abbrev stateValue (state : KeccakSemantics.State) : Value :=
  ScalarExecution.bundleValues (state.map Value.word)

theorem packet_evaluates {environment : Environment} {store : Store}
    {expressions : List Core.Expr} {values : List Word}
    (length : expressions.length = values.length)
    (evaluated : ∀ (index : Nat) expression value, expressions[index]? = some expression →
      values[index]? = some value → Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Keccak.packet expressions) (stateValue values) store := by
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

theorem field_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {values : List Word} {index : Nat} {value : Word}
    (evaluated : Evaluates environment store expression (stateValue values) store)
    (found : values[index]? = some value) :
    Evaluates environment store (Keccak.field index values.length expression) (.word value) store := by
  induction values generalizing expression index with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => cases Option.some.inj found; exact evaluated
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero => cases Option.some.inj found; exact .first evaluated
          | succ index => simpa [Keccak.field] using ih (.second evaluated) found

theorem lane_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {state : KeccakSemantics.State} {index : Nat}
    (length : state.length = 25) (bound : index < 25)
    (evaluated : Evaluates environment store expression (stateValue state) store) :
    Evaluates environment store (Keccak.lane index expression) (.word (KeccakSemantics.lane state index)) store := by
  have found := List.getElem?_eq_getElem (show index < state.length by omega)
  have field := field_evaluates evaluated found
  simpa only [Keccak.lane, length, KeccakSemantics.lane, found, Option.getD_some] using field

theorem rotate_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {value : Word} (distance : Nat)
    (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Keccak.rotate expression distance)
      (.word (KeccakSemantics.rotate value distance)) store := by
  by_cases zero : distance = 0
  · simpa only [Keccak.rotate, KeccakSemantics.rotate, zero, ↓reduceIte] using evaluated
  · simp only [Keccak.rotate, KeccakSemantics.rotate, zero, ↓reduceIte]
    exact .binary (.binary (.binary evaluated .word rfl) (.binary evaluated .word rfl) rfl) .word rfl

theorem source_eq {index : Nat} (bound : index < 25) : Keccak.source index = KeccakSemantics.source index := by
  have finite : ∀ index ∈ List.range 25, Keccak.source index = KeccakSemantics.source index := by decide
  exact finite index (List.mem_range.mpr bound)

theorem zeroState_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store Keccak.zeroState (stateValue (List.replicate 25 Word.zero)) store := by
  apply packet_evaluates (by simp)
  intro index expression value found known
  simp only [List.getElem?_replicate] at found known
  by_cases bound : index < 25
  · simp only [bound, ↓reduceIte, Option.some.injEq] at found known
    subst expression
    subst value
    exact .word
  · simp [bound] at found

theorem round_length (state : KeccakSemantics.State) (constant : Nat) :
    (KeccakSemantics.round state constant).length = 25 := by
  simp [KeccakSemantics.round]

theorem permute_length (state : KeccakSemantics.State) (length : state.length = 25) :
    (KeccakSemantics.permute state).length = 25 := by
  unfold KeccakSemantics.permute
  generalize KeccakSemantics.constants = constants
  induction constants generalizing state with
  | nil => exact length
  | cons constant constants ih => exact ih _ (round_length state constant)

end Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakAbsorptionCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
/-! The actual 24-round Core permutation implements the independent lane transform. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
open Core

theorem xor_lanes_evaluates {environment : Environment} {store : Store}
    {state : KeccakSemantics.State} {stateExpr accumulatorExpr : Core.Expr} {accumulator : Word}
    (length : state.length = 25) (column : Nat) (rows : List Nat)
    (bounds : ∀ row ∈ rows, column + 5 * row < 25)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store)
    (accumulatorEvaluated : Evaluates environment store accumulatorExpr (.word accumulator) store) :
    Evaluates environment store
      (rows.foldl (fun parity row => Keccak.xor parity (Keccak.lane (column + 5 * row) stateExpr)) accumulatorExpr)
      (.word (rows.foldl (fun parity row => parity.bitXor (KeccakSemantics.lane state (column + 5 * row))) accumulator)) store := by
  induction rows generalizing accumulatorExpr accumulator with
  | nil => exact accumulatorEvaluated
  | cons row rows ih =>
      apply ih (fun next member => bounds next (.tail _ member))
      exact .binary accumulatorEvaluated (lane_evaluates length (bounds row (.head _)) stateEvaluated) rfl

theorem parity_evaluates {environment : Environment} {store : Store}
    {state : KeccakSemantics.State} {stateExpr : Core.Expr}
    (length : state.length = 25) (column : Nat) (bound : column < 5)
    (evaluated : Evaluates environment store stateExpr (stateValue state) store) :
    Evaluates environment store
      ((List.range 5).foldl (fun parity row => Keccak.xor parity (Keccak.lane (column + 5 * row) stateExpr)) (Keccak.number 0))
      (.word (KeccakSemantics.parity state column)) store := by
  apply xor_lanes_evaluates length column (List.range 5) _ evaluated .word
  intro row member
  have := List.mem_range.mp member
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
 theorem roundBody_evaluates (state : KeccakSemantics.State) (constant : Nat)
    (length : state.length = 25) (captured : Environment) (store : Store) :
    Evaluates (.pair (stateValue state) (.word (Word.ofNatModulo constant)) :: captured) store
      Keccak.roundBody (stateValue (KeccakSemantics.round state constant)) store := by
  simp only [Keccak.roundBody, List.range_succ, List.range_zero,
    List.map_cons, List.map_nil, List.nil_append, List.cons_append, List.foldr_cons, List.foldr_nil]
  apply Evaluates.letE (parity_evaluates length 0 (by decide) (.first (.var rfl)))
  apply Evaluates.letE (parity_evaluates length 1 (by decide) (.first (.var rfl)))
  apply Evaluates.letE (parity_evaluates length 2 (by decide) (.first (.var rfl)))
  apply Evaluates.letE (parity_evaluates length 3 (by decide) (.first (.var rfl)))
  apply Evaluates.letE (parity_evaluates length 4 (by decide) (.first (.var rfl)))
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.delta state 0))
  · exact .binary (.var rfl) (rotate_evaluates 1 (.var rfl)) rfl
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.delta state 1))
  · exact .binary (.var rfl) (rotate_evaluates 1 (.var rfl)) rfl
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.delta state 2))
  · exact .binary (.var rfl) (rotate_evaluates 1 (.var rfl)) rfl
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.delta state 3))
  · exact .binary (.var rfl) (rotate_evaluates 1 (.var rfl)) rfl
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.delta state 4))
  · exact .binary (.var rfl) (rotate_evaluates 1 (.var rfl)) rfl
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 0))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 1))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 2))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 3))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 4))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 5))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 6))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 7))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 8))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 9))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 10))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 11))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 12))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 13))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 14))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 15))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 16))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 17))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 18))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 19))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 20))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 21))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 22))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 23))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply Evaluates.letE (boundValue := .word (KeccakSemantics.rotated state 24))
  · exact rotate_evaluates _ (.binary (lane_evaluates length (by decide) (.first (.var rfl))) (.var rfl) rfl)
  apply packet_evaluates (by simp [KeccakSemantics.round])
  intro index expression value found known
  have bound : index < 25 := by
    have := (List.getElem?_eq_some_iff.mp known).1
    simpa [KeccakSemantics.round] using this
  simp only [KeccakSemantics.round, List.getElem?_map, List.getElem?_range bound,
    Option.map_some, Option.some.injEq] at known
  subst value
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 ∨ index = 11 ∨ index = 12 ∨ index = 13 ∨ index = 14 ∨ index = 15 ∨ index = 16 ∨ index = 17 ∨ index = 18 ∨ index = 19 ∨ index = 20 ∨ index = 21 ∨ index = 22 ∨ index = 23 ∨ index = 24 := by omega
  rcases choices with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
    subst expression
    first
    | exact .binary (.binary (.var rfl) (.binary (.unary (.var rfl) rfl) (.var rfl) rfl) rfl)
        (.second (.var rfl)) rfl
    | exact .binary (.var rfl) (.binary (.unary (.var rfl) rfl) (.var rfl) rfl) rfl

theorem roundCalls_evaluates (constants : List Nat) (depth : Nat)
    (state : KeccakSemantics.State) (length : state.length = 25)
    (environment captured : Environment) (store : Store)
    (current : environment[0]? = some (stateValue state))
    (function : environment[depth + 1]? = some
      (.closure (.product Keccak.stateType .word) Keccak.stateType Keccak.roundBody captured)) :
    Evaluates environment store (Keccak.roundCalls depth constants)
      (stateValue (constants.foldl KeccakSemantics.round state)) store := by
  induction constants generalizing depth state environment with
  | nil => exact .var current
  | cons constant constants ih =>
      apply Evaluates.letE (.apply (.var function) (.pair (.var current) .word)
        (roundBody_evaluates state constant length captured store))
      exact ih (depth + 1) (KeccakSemantics.round state constant) (round_length state constant)
        (stateValue (KeccakSemantics.round state constant) :: environment) rfl
        (by simpa only [Nat.add_assoc, List.getElem?_cons_succ] using function)

theorem permute_evaluates {environment : Environment} {initial store : Store}
    {expression : Core.Expr} {state : KeccakSemantics.State} (length : state.length = 25)
    (evaluated : Evaluates
      (.closure (.product Keccak.stateType .word) Keccak.stateType Keccak.roundBody environment :: environment)
      initial (expression.weakenAt 0) (stateValue state) store) :
    Evaluates environment initial (Keccak.permute expression)
      (stateValue (KeccakSemantics.permute state)) store := by
  apply Evaluates.letE .lambda
  apply Evaluates.letE evaluated
  exact roundCalls_evaluates Keccak.constants 0 state length _ environment store rfl rfl

theorem permute_var_evaluates {environment : Environment} {store : Store}
    {state : KeccakSemantics.State} {index : Nat} (length : state.length = 25)
    (found : environment[index]? = some (stateValue state)) :
    Evaluates environment store (Keccak.permute (.var index))
      (stateValue (KeccakSemantics.permute state)) store := by
  apply permute_evaluates length
  simp only [Core.Expr.weakenAt, Nat.zero_le, ↓reduceIte]
  exact .var found

end Solcore.Frontend.RustHull.KeccakPermutationCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.KeccakHashCorrespondence
/-! Independent block absorption drives the emitted recursive helper and
hash expression. Padding allocations preserve the actual memory cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.KeccakHashCorrespondence
open Core MemoryCorrespondence KeccakPermutationCorrespondence KeccakAbsorptionCorrespondence

def input (words : MemorySemantics.Entries) (offset remaining : Word) (state : KeccakSemantics.State) : Value :=
  .pair (WordMapping.encode words) (.pair (.word offset) (.pair (.word remaining) (stateValue state)))

theorem absorbBody_evaluates {words : MemorySemantics.Entries} {offset remaining result : Word}
    {state : KeccakSemantics.State} (absorbed : KeccakSemantics.Absorb words offset remaining state result)
    (length : state.length = 25) (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Keccak.parameterType .word Keccak.absorbBody location captured) :
    ∃ suffix, Evaluates
      (input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured)
      store Keccak.absorbBody (.inRight .word (.word result)) (store ++ suffix) := by
  induction absorbed generalizing store with
  | last offset remaining state short =>
      let environment := input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := absorbBlock_evaluates (environment := environment) (store := store)
        (mapping := Keccak.field 0 4 (.var 0)) (offsetExpr := Keccak.field 1 4 (.var 0))
        (remainingExpr := Keccak.field 2 4 (.var 0)) (stateExpr := Keccak.field 3 4 (.var 0))
        length (LogsCorrespondence.Stable.var rfl).first (LogsCorrespondence.Stable.var rfl).second.first
        (LogsCorrespondence.Stable.var rfl).second.second.first (LogsCorrespondence.Stable.var rfl).second.second.second
      refine ⟨suffix, ?_⟩
      apply LanguageResult.bind_success .word blockEvaluated
      apply Evaluates.letE (permute_var_evaluates (absorbBlock_length words offset remaining state) rfl)
      apply Evaluates.ifTrue
      · exact .binary .word (.first (.second (.second (.var rfl)))) (by simp [BinaryOp.apply, short])
      · exact .inRight (digest_evaluates (permute_length _ (absorbBlock_length words offset remaining state)) (.var rfl))
  | @more offset remaining state result full rest ih =>
      let environment := input words offset remaining state ::
        .cellRef (OptionalCell.cellType (WordMapping.helperType Keccak.parameterType .word)) location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := absorbBlock_evaluates (environment := environment) (store := store)
        (mapping := Keccak.field 0 4 (.var 0)) (offsetExpr := Keccak.field 1 4 (.var 0))
        (remainingExpr := Keccak.field 2 4 (.var 0)) (stateExpr := Keccak.field 3 4 (.var 0))
        length (LogsCorrespondence.Stable.var rfl).first (LogsCorrespondence.Stable.var rfl).second.first
        (LogsCorrespondence.Stable.var rfl).second.second.first (LogsCorrespondence.Stable.var rfl).second.second.second
      obtain ⟨tail, bodyEvaluated⟩ := ih (permute_length _ (absorbBlock_length words offset remaining state)) (store ++ suffix)
        (LogsCorrespondence.installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      apply Evaluates.letE (permute_var_evaluates (absorbBlock_length words offset remaining state) rfl)
      apply Evaluates.ifFalse
      · exact .binary .word (.first (.second (.second (.var rfl)))) (by simp [BinaryOp.apply, full])
      · apply LogsCorrespondence.invoke_evaluates (body := Keccak.absorbBody) (captured := captured)
          (input := input words (offset.add (Word.ofNatModulo 136)) (remaining.sub (Word.ofNatModulo 136))
            (KeccakSemantics.permute (KeccakSemantics.absorbBlock words offset remaining state)))
          (.var rfl) (LogsCorrespondence.installed_append installed suffix)
        · simp [Core.Expr.weakenAt, Keccak.packet, Keccak.field, Keccak.add, Keccak.number]
          exact .pair (.first (.var rfl)) (.pair (.binary (.first (.second (.var rfl))) .word rfl)
            (.pair (.binary (leftValue := .word remaining) (.first (.second (.second (.var rfl)))) .word rfl) (.var rfl)))
        · exact bodyEvaluated

theorem absorb_evaluates {words : MemorySemantics.Entries} {offset remaining result : Word}
    {state : KeccakSemantics.State} (absorbed : KeccakSemantics.Absorb words offset remaining state result)
    (length : state.length = 25)
    {environment : Environment} {store : Store} {mapping offsetExpr remainingExpr stateExpr : Core.Expr}
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode words) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (remainingEvaluated : Evaluates environment store remainingExpr (.word remaining) store)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store) :
    ∃ suffix, Evaluates environment store
      (WordMapping.runHelper Keccak.parameterType .word Keccak.absorbBody
        (Keccak.packet [mapping, offsetExpr, remainingExpr, stateExpr]))
      (.inRight .word (.word result)) (store ++ suffix) := by
  let argument := input words offset remaining state
  let closure := WordMapping.closure Keccak.parameterType .word Keccak.absorbBody store.length (argument :: environment)
  obtain ⟨suffix, body⟩ := absorbBody_evaluates absorbed length
    (store ++ [.inRight .unit closure]) store.length (argument :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  exact LogsCorrespondence.runHelper_evaluates
    (.pair mappingEvaluated (.pair offsetEvaluated (.pair remainingEvaluated stateEvaluated))) body

theorem hash_preserves {offset length : Word}
    {state finalState : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (hashed : KeccakSemantics.Hash offset length state result finalState)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ target final, Correspondence.ResultRel .word result target ∧
      Evaluates environment store (Keccak.hash memoryRef sizeRef offsetExpr lengthExpr) target final ∧
      StateRel memoryLocation sizeLocation finalState final ∧ Frame memoryLocation sizeLocation store final := by
  let argument := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word offset) (.word length)))
  have touched := touch_evaluates (environment := argument :: environment)
    (reference := Keccak.field 1 4 (.var 0)) (offsetExpr := Keccak.field 2 4 (.var 0)) (lengthExpr := Keccak.field 3 4 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.var rfl)))) related.size
  cases hashed with
  | overflow overflow =>
      simp only [touchResult, overflow, touchStore_failure overflow] at touched
      refine ⟨.inLeft .word (.word Memory.overflowReason), store, .language _, ?_, related, Frame.refl _ _ _⟩
      exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
        (LanguageResult.bind_failure .word touched)
  | @done size result touchedSize absorbed =>
      simp only [touchResult, touchedSize] at touched
      have touchedRelated := related.touch touchedSize
      obtain ⟨suffix, evaluated⟩ := absorb_evaluates absorbed (by simp)
        (environment := .unit :: argument :: environment)
        (mapping := .loadCell (Keccak.field 0 4 (.var 1))) (offsetExpr := Keccak.field 2 4 (.var 1))
        (remainingExpr := Keccak.field 3 4 (.var 1)) (stateExpr := Keccak.zeroState)
        (.loadCell (.first (.var rfl)) touchedRelated.memory)
        (.first (.second (.second (.var rfl)))) (.second (.second (.second (.var rfl))))
        (zeroState_evaluates _ _)
      refine ⟨.inRight .word (.word result), _, .value (.word result), ?_, touchedRelated.append suffix,
        (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ suffix)⟩
      exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
        (LanguageResult.bind_success .word touched evaluated)

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem hash_rename (memory size offset length : Core.Expr) (mapping : Renaming) :
    (Keccak.hash memory size offset length).rename mapping =
      Keccak.hash (memory.rename mapping) (size.rename mapping) (offset.rename mapping) (length.rename mapping) := by
  simp only [Keccak.hash, Keccak.packet, Core.Expr.rename]
  congr 1
  simp [LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Memory.touch, Memory.add, Memory.number, Memory.packet, Memory.field,
    Keccak.field, Keccak.absorbBody, Keccak.absorbBlock, Keccak.readLane, Keccak.paddedByte,
    Keccak.digest, Keccak.permute, Keccak.roundCalls, Keccak.roundBody,
    Keccak.constants, Keccak.rotations, Keccak.source, Keccak.destination,
    Keccak.packet, Keccak.number, Keccak.xor, Keccak.add, Keccak.shift,
    Keccak.move, Keccak.lane, Keccak.zeroState, Keccak.rotate,
    Memory.readMemoryByte, List.range_succ,
    WordMapping.lookup, WordMapping.runHelper, WordMapping.lookupBody,
    WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    Core.Expr.rename, Core.Expr.renameList, Core.Renaming.lift, Core.Expr.weakenAt]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end Solcore.Frontend.RustHull.KeccakHashCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160Implementation
/-! `HashBlocks` and `Ripemd160` keep their builders private. This module
restates the RIPEMD-160 instance with public names; `hash_eq` and
`compress_eq` prove by `rfl` that the restatement is the implemented expression,
including its step tables. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160Implementation
open Core HashBlocks

def lane (index : Nat) (state : Core.Expr) : Core.Expr := field index 5 state
def initial : Core.Expr := packet ([0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0].map number)

def nonlinear (phase : Nat) (x y z : Core.Expr) : Core.Expr := match phase with
  | 0 => xor (xor x y) z
  | 1 => .binary .wordOr (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
  | 2 => xor (.binary .wordOr x (.unary .wordNot y)) z
  | 3 => .binary .wordOr (.binary .wordAnd x z) (.binary .wordAnd y (.unary .wordNot z))
  | _ => xor x (.binary .wordOr y (.unary .wordNot z))

/-- One step of a line; the state is the expression `state` and the selected
message word is `message`. -/
def step (phase constant rotation : Nat) (state message : Core.Expr) : Core.Expr :=
  let t := sum32 [rotateLeft (sum32 [lane 0 state,
    nonlinear phase (lane 1 state) (lane 2 state) (lane 3 state), message, number constant]) rotation,
    lane 4 state]
  let state := state.weakenAt 0
  .letE t (packet [lane 4 state, .var 0, lane 1 state, rotateLeft (lane 2 state) 10, lane 3 state])

/-- Step `index` of both lines: the line pair is bound at index 0 and the
original (chaining, block) pair at index `index + 1`. -/
def round (index : Nat) : Core.Expr :=
  let message := Core.Expr.second (.var (index + 1))
  .pair
    (step (index / 16) (Ripemd160Semantics.leftConstants[index / 16]?.getD 0)
      (Ripemd160Semantics.leftRotations[index]?.getD 0)
      (.first (.var 0)) (field (Ripemd160Semantics.leftWords[index]?.getD 0) 16 message))
    (step (4 - index / 16) (Ripemd160Semantics.rightConstants[index / 16]?.getD 0)
      (Ripemd160Semantics.rightRotations[index]?.getD 0)
      (.second (.var 0)) (field (Ripemd160Semantics.rightWords[index]?.getD 0) 16 message))

/-- After eighty rounds the original pair is at index 81 and the final lines at 0. -/
def result : Core.Expr :=
  let old := Core.Expr.first (.var 81)
  let left := Core.Expr.first (.var 0)
  let right := Core.Expr.second (.var 0)
  packet [sum32 [lane 1 old, lane 2 left, lane 3 right],
    sum32 [lane 2 old, lane 3 left, lane 4 right], sum32 [lane 3 old, lane 4 left, lane 0 right],
    sum32 [lane 4 old, lane 0 left, lane 1 right], sum32 [lane 0 old, lane 1 left, lane 2 right]]

def compress (state block : Core.Expr) : Core.Expr :=
  .letE (.pair state block)
    (.letE (.pair (.first (.var 0)) (.first (.var 0))) (((List.range 80).map round).foldr Core.Expr.letE result))

def digest (state : Core.Expr) : Core.Expr :=
  (List.range 20).foldl (fun result index =>
    .binary .wordOr (shift result 8)
      (.binary .wordByte (number (31 - index % 4)) (lane (index / 4) state))) (number 0)

def paddedByte (mapping offset remaining bits markerUsed : Core.Expr) (index : Nat) : Core.Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (31 - (index - 56))) bits)
            (number 0))))

def readWord : Nat → Nat → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte mapping offset remaining bits markerUsed index)
        (readWord count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0) (shift (.var 0) (8 * (index % 4)))))

def readBlock (parameters : Core.Expr) : Core.Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

def parameterType : Core.Ty := types [WordMapping.type, .word, .word, .word, Ripemd160.stateType, .bool]

/-- Parameters: mapping, offset, remaining length, bit length, chaining state
and whether the marker byte was already written. -/
def absorbBody : Core.Expr :=
  LanguageResult.bind .word (readBlock (.var 0))
    (.letE (compress (field 4 6 (.var 1)) (.var 0))
      (let params := Core.Expr.var 2
       let next := fun offset remaining marker =>
         WordMapping.invoke parameterType .word (.var 3)
           (packet [field 0 6 params, offset, remaining, field 3 6 params, .var 0, marker])
       .ifE (.binary .wordGt (field 2 6 params) (number 63))
         (next (add (field 1 6 params) (number 64))
           (.binary .wordSub (field 2 6 params) (number 64)) (.bool false))
         (.ifE (.binary .wordGt (field 2 6 params) (number 55))
           (next (field 1 6 params) (number 0) (.bool true))
           (LanguageResult.success (digest (.var 0))))))

def hash (memoryReference sizeReference offset length : Core.Expr) : Core.Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper parameterType .word absorbBody
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1), field 3 4 (.var 1),
          .binary .wordAnd (.binary .wordMul (field 3 4 (.var 1)) (number 8)) (number (2 ^ 64 - 1)),
          initial, .bool false])))

theorem compress_eq (state block : Core.Expr) : Ripemd160.compress state block = compress state block := rfl

theorem hash_eq (memoryReference sizeReference offset length : Core.Expr) :
    Ripemd160.hash memoryReference sizeReference offset length =
      hash memoryReference sizeReference offset length := rfl

end Solcore.Frontend.RustHull.Ripemd160Implementation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256Implementation
/-! `HashBlocks` and `Sha256` keep their builders private. This module restates
the SHA-256 instance with public names; `hash_eq` and `compress_eq` prove by
`rfl` that the restatement is the implemented expression. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256Implementation
open Core HashBlocks

def lane (index : Nat) (state : Core.Expr) : Core.Expr := field index 8 state
def initial : Core.Expr := packet ([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19].map number)
def constants : List Nat := Sha256Semantics.constants

def xor3 (a b c : Core.Expr) : Core.Expr := xor (xor a b) c
def small0 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 7) (rotateRight x 18) (.binary .wordShr x (number 3))
def small1 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 17) (rotateRight x 19) (.binary .wordShr x (number 10))
def large0 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 2) (rotateRight x 13) (rotateRight x 22)
def large1 (x : Core.Expr) : Core.Expr := xor3 (rotateRight x 6) (rotateRight x 11) (rotateRight x 25)
def choose (x y z : Core.Expr) : Core.Expr := xor (.binary .wordAnd x y) (.binary .wordAnd (.unary .wordNot x) z)
def majority (x y z : Core.Expr) : Core.Expr :=
  xor3 (.binary .wordAnd x y) (.binary .wordAnd x z) (.binary .wordAnd y z)

/-- One round: the state is bound at index 0 and W(t) at index 64. -/
def round (constant : Nat) : Core.Expr :=
  let state := Core.Expr.var 0
  let t1 := sum32 [lane 7 state, large1 (lane 4 state), choose (lane 4 state) (lane 5 state) (lane 6 state),
    number constant, .var 64]
  let t2 := sum32 [large0 (lane 0 (.var 1)), majority (lane 0 (.var 1)) (lane 1 (.var 1)) (lane 2 (.var 1))]
  .letE t1 (.letE t2 (packet [sum32 [.var 1, .var 0], lane 0 (.var 2), lane 1 (.var 2),
    lane 2 (.var 2), sum32 [lane 3 (.var 2), .var 1], lane 4 (.var 2), lane 5 (.var 2), lane 6 (.var 2)]))

def scheduleWord (index : Nat) : Core.Expr :=
  if index < 16 then field index 16 (.second (.var index))
  else sum32 [small1 (.var 1), .var 6, small0 (.var 14), .var 15]

def completed : Core.Expr :=
  packet ((List.range 8).map fun index => sum32 [lane index (.var 64), lane index (.var 0)])

def compress (state block : Core.Expr) : Core.Expr :=
  .letE (.pair state block)
    (((List.range 64).map scheduleWord).foldr Core.Expr.letE
      (.letE (.first (.var 64)) ((constants.map round).foldr Core.Expr.letE completed)))

def digest (state : Core.Expr) : Core.Expr :=
  (List.range 8).foldl (fun result index => .binary .wordOr (shift result 32) (lane index state)) (number 0)

def paddedByte (mapping offset remaining bits markerUsed : Core.Expr) (index : Nat) : Core.Expr :=
  .ifE (.binary .wordGt remaining (number index))
    (Memory.readMemoryByte mapping (add offset (number index)))
    (LanguageResult.success
      (.ifE (.ifE (.binary .wordEq remaining (number index)) (.unary .boolNot markerUsed) (.bool false))
        (number 128)
        (if index < 56 then number 0
          else .ifE (.binary .wordGt (number 56) remaining)
            (.binary .wordByte (number (24 + (index - 56))) bits)
            (number 0))))

def readWord : Nat → Nat → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | 0, _, _, _, _, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, index, mapping, offset, remaining, bits, markerUsed, accumulator =>
      LanguageResult.bind .word (paddedByte mapping offset remaining bits markerUsed index)
        (readWord count (index + 1) (mapping.weakenAt 0) (offset.weakenAt 0)
          (remaining.weakenAt 0) (bits.weakenAt 0) (markerUsed.weakenAt 0)
          (.binary .wordOr (accumulator.weakenAt 0) (shift (.var 0) (8 * (3 - index % 4)))))

def readBlock (parameters : Core.Expr) : Core.Expr :=
  let computations := (List.range 16).map fun index =>
    let params := move parameters index
    readWord 4 (4 * index) (field 0 6 params) (field 1 6 params)
      (field 2 6 params) (field 3 6 params) (field 5 6 params) (number 0)
  computations.foldr (LanguageResult.bind blockType)
    (LanguageResult.success (packet ((List.range 16).map fun index => .var (15 - index))))

def parameterType : Core.Ty := types [WordMapping.type, .word, .word, .word, Sha256.stateType, .bool]

/-- Parameters: mapping, offset, remaining length, bit length, chaining state
and whether the marker byte was already written. -/
def absorbBody : Core.Expr :=
  LanguageResult.bind .word (readBlock (.var 0))
    (.letE (compress (field 4 6 (.var 1)) (.var 0))
      (let params := Core.Expr.var 2
       let next := fun offset remaining marker =>
         WordMapping.invoke parameterType .word (.var 3)
           (packet [field 0 6 params, offset, remaining, field 3 6 params, .var 0, marker])
       .ifE (.binary .wordGt (field 2 6 params) (number 63))
         (next (add (field 1 6 params) (number 64))
           (.binary .wordSub (field 2 6 params) (number 64)) (.bool false))
         (.ifE (.binary .wordGt (field 2 6 params) (number 55))
           (next (field 1 6 params) (number 0) (.bool true))
           (LanguageResult.success (digest (.var 0))))))

def hash (memoryReference sizeReference offset length : Core.Expr) : Core.Expr :=
  .letE (packet [memoryReference, sizeReference, offset, length])
    (LanguageResult.bind .word
      (Memory.touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (field 3 4 (.var 0)))
      (WordMapping.runHelper parameterType .word absorbBody
        (packet [.loadCell (field 0 4 (.var 1)), field 2 4 (.var 1), field 3 4 (.var 1),
          .binary .wordAnd (.binary .wordMul (field 3 4 (.var 1)) (number 8)) (number (2 ^ 64 - 1)),
          initial, .bool false])))

theorem compress_eq (state block : Core.Expr) : Sha256.compress state block = compress state block := rfl

theorem hash_eq (memoryReference sizeReference offset length : Core.Expr) :
    Sha256.hash memoryReference sizeReference offset length = hash memoryReference sizeReference offset length := rfl

end Solcore.Frontend.RustHull.Sha256Implementation
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256BlockCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160BlockCorrespondence
/-! RIPEMD-160 block reading over a retained memory mapping: little-endian
message words and bit length. Padding bytes are computed without memory
writes; every lookup helper allocation is retained. The generic packet, binding
and parameter lemmas are shared with SHA-256. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160BlockCorrespondence
open Core LogsCorrespondence Sha256BlockCorrespondence

theorem paddedByte_evaluates {environment : Environment} {store : Store}
    {mapping offsetExpr remainingExpr bitsExpr markerExpr : Core.Expr} (words : MemorySemantics.Entries)
    (offset remaining bits : Word) (markerUsed : Bool) (index : Nat)
    (mappingEvaluated : Evaluates environment store mapping (WordMapping.encode words) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (remainingEvaluated : Evaluates environment store remainingExpr (.word remaining) store)
    (bitsEvaluated : Evaluates environment store bitsExpr (.word bits) store)
    (markerEvaluated : Evaluates environment store markerExpr (.bool markerUsed) store) :
    ∃ suffix, Evaluates environment store
      (Ripemd160Implementation.paddedByte mapping offsetExpr remainingExpr bitsExpr markerExpr index)
      (.inRight .word (.word (Ripemd160Semantics.paddedByte words offset remaining bits markerUsed index)))
      (store ++ suffix) := by
  by_cases present : remaining > Word.ofNatModulo index
  · obtain ⟨suffix, evaluated⟩ := MemoryCopyCorrespondence.readMemoryByte_evaluates words
      (offsetExpr := HashBlocks.add offsetExpr (HashBlocks.number index))
      (offset.add (Word.ofNatModulo index)) mappingEvaluated (.binary offsetEvaluated .word rfl)
    refine ⟨suffix, ?_⟩
    simp only [Ripemd160Semantics.paddedByte, present, ↓reduceIte]
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
    unfold Ripemd160Semantics.paddedByte
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
      (Ripemd160Implementation.readWord count index mapping offsetExpr remainingExpr bitsExpr markerExpr accumulatorExpr)
      (.inRight .word (.word (Ripemd160Semantics.readWord words offset remaining bits markerUsed count index accumulator)))
      (store ++ suffix) := by
  induction count generalizing environment store index mapping offsetExpr remainingExpr bitsExpr markerExpr
      accumulatorExpr accumulator with
  | zero => exact ⟨[], by simpa only [List.append_nil, Ripemd160Implementation.readWord, Ripemd160Semantics.readWord,
      LanguageResult.success] using Evaluates.inRight (accumulatorStable.evaluates store)⟩
  | succ count ih =>
      obtain ⟨first, byte⟩ := paddedByte_evaluates words offset remaining bits markerUsed index
        (mappingStable.evaluates store) (offsetStable.evaluates store) (remainingStable.evaluates store)
        (bitsStable.evaluates store) (markerStable.evaluates store)
      let value := Ripemd160Semantics.paddedByte words offset remaining bits markerUsed index
      have updated : Stable (.word value :: environment)
          (.binary .wordOr (accumulatorExpr.weakenAt 0) (HashBlocks.shift (.var 0) (8 * (index % 4))))
          (.word (accumulator.bitOr (value.shiftLeft (Word.ofNatModulo (8 * (index % 4)))))) := by
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

theorem readBlock_length (words : MemorySemantics.Entries) (offset remaining bits : Word) (markerUsed : Bool) :
    (Ripemd160Semantics.readBlock words offset remaining bits markerUsed).length = 16 := by
  simp only [Ripemd160Semantics.readBlock, List.length_map, List.length_range]

/-- The sixteen message words are read in order. Lookup allocations append to
the store throughout the block. -/
theorem readBlock_evaluates {environment : Environment} (store : Store) {parameters : Core.Expr}
    {words : MemorySemantics.Entries} {offset remaining bits : Word} {state : List Word} {markerUsed : Bool}
    (parametersStable : Stable environment parameters (parametersValue words offset remaining bits state markerUsed)) :
    ∃ suffix, Evaluates environment store (Ripemd160Implementation.readBlock parameters)
      (.inRight .word (wordsValue (Ripemd160Semantics.readBlock words offset remaining bits markerUsed)))
      (store ++ suffix) := by
  unfold Ripemd160Implementation.readBlock
  apply binds_evaluates store HashBlocks.blockType
    (values := (List.range 16).map (fun index =>
      Value.word (Ripemd160Semantics.readWord words offset remaining bits markerUsed 4 (4 * index) (Word.ofNatModulo 0))))
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
    apply packet_evaluates (by simp only [Ripemd160Semantics.readBlock, List.length_map, List.length_range])
    intro index expression value found known
    have bound : index < 16 := by
      simpa only [List.length_map, List.length_range] using (List.getElem?_eq_some_iff.mp found).1
    simp only [Ripemd160Semantics.readBlock, List.getElem?_map, List.getElem?_range, bound,
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

end Solcore.Frontend.RustHull.Ripemd160BlockCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160CompressCorrespondence
/-! The actual RIPEMD-160 compression and digest Core expressions evaluate to
the independent specification. The implementation complements words with the
256-bit `wordNot` while the specification complements within 32 bits; the two
nonlinear functions agree modulo 2^32, which is all the enclosing `sum32`
observes, so no bound on the chaining words is needed. Every expression is
pure: the store is returned unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160CompressCorrespondence
open Core

abbrev stateValue (words : List Core.Word) : Core.Value :=
  ScalarExecution.bundleValues (words.map Core.Value.word)

/-! ## Masking to 32 bits -/

theorem mask32_val (value : Word) : (Ripemd160Semantics.mask32 value).val = value.val % 2 ^ 32 := by
  change (value.val &&& (2 ^ 32 - 1) % wordModulus) % wordModulus = value.val % 2 ^ 32
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - 1 < wordModulus by decide), Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem mask32_lt (value : Word) : (Ripemd160Semantics.mask32 value).val < 2 ^ 32 := by
  rw [mask32_val]
  exact Nat.mod_lt _ (by decide)

theorem mask32_eq_iff {left right : Word} :
    Ripemd160Semantics.mask32 left = Ripemd160Semantics.mask32 right ↔ left.val % 2 ^ 32 = right.val % 2 ^ 32 :=
  ⟨fun related => by simpa only [mask32_val] using congrArg Fin.val related,
    fun related => Fin.ext (by rw [mask32_val, mask32_val, related])⟩

theorem pow_dvd_wordModulus : 2 ^ 32 ∣ wordModulus := Nat.pow_dvd_pow 2 (by decide)

/-- Word addition respects equality modulo 2^32, since 2^32 divides the word modulus. -/
theorem mask32_add_congr {left right : Word} (value : Word)
    (related : Ripemd160Semantics.mask32 left = Ripemd160Semantics.mask32 right) :
    Ripemd160Semantics.mask32 (left.add value) = Ripemd160Semantics.mask32 (right.add value) := by
  rw [mask32_eq_iff] at related ⊢
  change (left + value).val % 2 ^ 32 = (right + value).val % 2 ^ 32
  rw [Fin.val_add, Fin.val_add, Nat.mod_mod_of_dvd _ pow_dvd_wordModulus, Nat.mod_mod_of_dvd _ pow_dvd_wordModulus,
    Nat.add_mod, related, ← Nat.add_mod]

theorem mask32_add_congr_right {left right : Word} (value : Word)
    (related : Ripemd160Semantics.mask32 left = Ripemd160Semantics.mask32 right) :
    Ripemd160Semantics.mask32 (value.add left) = Ripemd160Semantics.mask32 (value.add right) := by
  rw [mask32_eq_iff] at related ⊢
  change (value + left).val % 2 ^ 32 = (value + right).val % 2 ^ 32
  rw [Fin.val_add, Fin.val_add, Nat.mod_mod_of_dvd _ pow_dvd_wordModulus, Nat.mod_mod_of_dvd _ pow_dvd_wordModulus,
    Nat.add_mod, related, ← Nat.add_mod]

theorem mask32_foldl_add_congr (values : List Word) :
    ∀ {left right : Word}, Ripemd160Semantics.mask32 left = Ripemd160Semantics.mask32 right →
      Ripemd160Semantics.mask32 (values.foldl Word.add left) =
        Ripemd160Semantics.mask32 (values.foldl Word.add right) := by
  induction values with
  | nil => intro _ _ related; exact related
  | cons value values ih => intro _ _ related; exact ih (mask32_add_congr value related)

/-- `sum32` sees its second addend only modulo 2^32. -/
theorem sum32_congr {left right : Word} (first : Word) (rest : List Word)
    (related : Ripemd160Semantics.mask32 left = Ripemd160Semantics.mask32 right) :
    Ripemd160Semantics.sum32 (first :: left :: rest) = Ripemd160Semantics.sum32 (first :: right :: rest) :=
  mask32_foldl_add_congr rest (mask32_add_congr_right _ related)

/-! ## The nonlinear functions -/

theorem bitAnd_val (left right : Word) : (left.bitAnd right).val = left.val &&& right.val := by
  change (left.val &&& right.val) % wordModulus = _
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left left.isLt)

theorem bitOr_val (left right : Word) : (left.bitOr right).val = left.val ||| right.val := by
  change (left.val ||| right.val) % wordModulus = _
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow left.isLt right.isLt)

theorem bitXor_val (left right : Word) : (left.bitXor right).val = left.val ^^^ right.val := by
  change (left.val ^^^ right.val) % wordModulus = _
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow left.isLt right.isLt)

/-- f(j, x, y, z) as the implementation computes it, complementing all 256 bits. -/
def nonlinear256 : Nat → Word → Word → Word → Word
  | 0, x, y, z => (x.bitXor y).bitXor z
  | 1, x, y, z => (x.bitAnd y).bitOr (x.bitNot.bitAnd z)
  | 2, x, y, z => (x.bitOr y.bitNot).bitXor z
  | 3, x, y, z => (x.bitAnd z).bitOr (y.bitAnd z.bitNot)
  | _, x, y, z => x.bitXor (y.bitOr z.bitNot)

/-- Below bit 32 the complement and `not32` agree, and masking distributes over the
bit operations, so both functions agree modulo 2^32 for all inputs. -/
theorem mask32_nonlinear256 (phase : Nat) (x y z : Word) :
    Ripemd160Semantics.mask32 (nonlinear256 phase x y z) =
      Ripemd160Semantics.mask32 (Ripemd160Semantics.nonlinear phase x y z) := by
  apply Fin.ext
  rw [mask32_val, mask32_val]
  apply Nat.eq_of_testBit_eq
  intro i
  match phase with
  | 0 => simp only [nonlinear256, Ripemd160Semantics.nonlinear]
  | 1 =>
      simp only [nonlinear256, Ripemd160Semantics.nonlinear, Ripemd160Semantics.not32, mask32_val, bitAnd_val,
        bitOr_val, Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or]
      cases decide (i < 32) <;> cases x.val.testBit i <;> cases y.val.testBit i <;> cases z.val.testBit i <;>
        cases x.bitNot.val.testBit i <;> rfl
  | 2 =>
      simp only [nonlinear256, Ripemd160Semantics.nonlinear, Ripemd160Semantics.not32, mask32_val, bitOr_val,
        bitXor_val, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_xor]
      cases decide (i < 32) <;> cases x.val.testBit i <;> cases z.val.testBit i <;>
        cases y.bitNot.val.testBit i <;> rfl
  | 3 =>
      simp only [nonlinear256, Ripemd160Semantics.nonlinear, Ripemd160Semantics.not32, mask32_val, bitAnd_val,
        bitOr_val, Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_or]
      cases decide (i < 32) <;> cases x.val.testBit i <;> cases y.val.testBit i <;> cases z.val.testBit i <;>
        cases z.bitNot.val.testBit i <;> rfl
  | _ + 4 =>
      simp only [nonlinear256, Ripemd160Semantics.nonlinear, Ripemd160Semantics.not32, mask32_val, bitOr_val,
        bitXor_val, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_xor]
      cases decide (i < 32) <;> cases x.val.testBit i <;> cases y.val.testBit i <;>
        cases z.bitNot.val.testBit i <;> rfl

/-! ## Lengths and bounds of the specification -/

theorem initial_length : Ripemd160Semantics.initial.length = 5 := rfl

theorem step_length (round constant rotation : Nat) (state : List Word) (word : Word) :
    (Ripemd160Semantics.step round constant rotation state word).length = 5 := rfl

/-- The final combination of the chaining words with both lines. -/
def combine (state : Ripemd160Semantics.State) (lines : Ripemd160Semantics.State × Ripemd160Semantics.State) :
    Ripemd160Semantics.State :=
  [Ripemd160Semantics.sum32 [Ripemd160Semantics.lane state 1, Ripemd160Semantics.lane lines.1 2,
      Ripemd160Semantics.lane lines.2 3],
    Ripemd160Semantics.sum32 [Ripemd160Semantics.lane state 2, Ripemd160Semantics.lane lines.1 3,
      Ripemd160Semantics.lane lines.2 4],
    Ripemd160Semantics.sum32 [Ripemd160Semantics.lane state 3, Ripemd160Semantics.lane lines.1 4,
      Ripemd160Semantics.lane lines.2 0],
    Ripemd160Semantics.sum32 [Ripemd160Semantics.lane state 4, Ripemd160Semantics.lane lines.1 0,
      Ripemd160Semantics.lane lines.2 1],
    Ripemd160Semantics.sum32 [Ripemd160Semantics.lane state 0, Ripemd160Semantics.lane lines.1 1,
      Ripemd160Semantics.lane lines.2 2]]

theorem compress_eq_combine (state block : List Word) :
    Ripemd160Semantics.compress state block =
      combine state ((List.range 80).foldl (Ripemd160Semantics.steps block) (state, state)) := rfl

theorem compress_length (state block : List Core.Word) : (Ripemd160Semantics.compress state block).length = 5 :=
  rfl

/-! ## Evaluation of the shared builders -/

/-- Each expression evaluates to the matching word without touching the store. -/
inductive WordsEvaluate (environment : Environment) (store : Store) : List Core.Expr → List Word → Prop where
  | nil : WordsEvaluate environment store [] []
  | cons {expression : Core.Expr} {expressions : List Core.Expr} {value : Word} {values : List Word}
      (head : Evaluates environment store expression (.word value) store)
      (tail : WordsEvaluate environment store expressions values) :
      WordsEvaluate environment store (expression :: expressions) (value :: values)

theorem wordsEvaluate_map {environment : Environment} {store : Store}
    (builder : Nat → Core.Expr) (denotation : Nat → Word) :
    ∀ (indices : List Nat),
      (∀ index ∈ indices, Evaluates environment store (builder index) (.word (denotation index)) store) →
      WordsEvaluate environment store (indices.map builder) (indices.map denotation)
  | [], _ => .nil
  | index :: indices, evaluated =>
      .cons (evaluated index (.head _)) (wordsEvaluate_map builder denotation indices fun next member =>
        evaluated next (.tail _ member))

theorem packet_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    Evaluates environment store (HashBlocks.packet expressions) (stateValue values) store := by
  induction related with
  | nil => exact .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head
      | cons _ _ => exact .pair head ih

theorem field_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {values : List Word} {index : Nat} {value : Word}
    (evaluated : Evaluates environment store expression (stateValue values) store)
    (found : values[index]? = some value) :
    Evaluates environment store (HashBlocks.field index values.length expression) (.word value) store := by
  induction values generalizing expression index with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => cases Option.some.inj found; exact evaluated
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero => cases Option.some.inj found; exact .first evaluated
          | succ index => simpa [HashBlocks.field] using ih (.second evaluated) found

theorem lane_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {state : List Word} {index : Nat}
    (length : state.length = 5) (bound : index < 5)
    (evaluated : Evaluates environment store expression (stateValue state) store) :
    Evaluates environment store (Ripemd160Implementation.lane index expression)
      (.word (Ripemd160Semantics.lane state index)) store := by
  have found := List.getElem?_eq_getElem (show index < state.length by omega)
  have field := field_evaluates evaluated found
  simpa only [Ripemd160Implementation.lane, length, Ripemd160Semantics.lane, found, Option.getD_some] using field

theorem messageWord_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {block : List Word} {index : Nat}
    (length : block.length = 16) (bound : index < 16)
    (evaluated : Evaluates environment store expression (stateValue block) store) :
    Evaluates environment store (HashBlocks.field index 16 expression)
      (.word (Ripemd160Semantics.messageWord block index)) store := by
  have found := List.getElem?_eq_getElem (show index < block.length by omega)
  have field := field_evaluates evaluated found
  simpa only [length, Ripemd160Semantics.messageWord, found, Option.getD_some] using field

theorem foldl_add_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    ∀ {accumulator : Core.Expr} {total : Word}, Evaluates environment store accumulator (.word total) store →
      Evaluates environment store (expressions.foldl HashBlocks.add accumulator)
        (.word (values.foldl Word.add total)) store := by
  induction related with
  | nil => intro _ _ evaluated; exact evaluated
  | cons head _ ih => intro _ _ evaluated; exact ih (.binary evaluated head rfl)

theorem sum32_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    Evaluates environment store (HashBlocks.sum32 expressions) (.word (Ripemd160Semantics.sum32 values)) store :=
  .binary (foldl_add_evaluates related .word) .word rfl

theorem rotateLeft_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (distance : Nat) (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (HashBlocks.rotateLeft expression distance)
      (.word (Ripemd160Semantics.rotateLeft value distance)) store :=
  .binary (.binary (.binary evaluated .word rfl) (.binary evaluated .word rfl) rfl) .word rfl

theorem numbers_evaluates (environment : Environment) (store : Store) (values : List Nat) :
    Evaluates environment store (HashBlocks.packet (values.map HashBlocks.number))
      (stateValue (values.map Word.ofNatModulo)) store :=
  packet_evaluates (wordsEvaluate_map HashBlocks.number Word.ofNatModulo values fun _ _ => .word)

theorem initial_evaluates (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store Ripemd160Implementation.initial (stateValue Ripemd160Semantics.initial) store :=
  numbers_evaluates environment store _

theorem nonlinear_evaluates {environment : Environment} {store : Store} {x y z : Core.Expr}
    {xValue yValue zValue : Word} (phase : Nat)
    (xEvaluated : Evaluates environment store x (.word xValue) store)
    (yEvaluated : Evaluates environment store y (.word yValue) store)
    (zEvaluated : Evaluates environment store z (.word zValue) store) :
    Evaluates environment store (Ripemd160Implementation.nonlinear phase x y z)
      (.word (nonlinear256 phase xValue yValue zValue)) store := by
  match phase with
  | 0 => exact .binary (.binary xEvaluated yEvaluated rfl) zEvaluated rfl
  | 1 => exact .binary (.binary xEvaluated yEvaluated rfl) (.binary (.unary xEvaluated rfl) zEvaluated rfl) rfl
  | 2 => exact .binary (.binary xEvaluated (.unary yEvaluated rfl) rfl) zEvaluated rfl
  | 3 => exact .binary (.binary xEvaluated zEvaluated rfl) (.binary yEvaluated (.unary zEvaluated rfl) rfl) rfl
  | _ + 4 => exact .binary xEvaluated (.binary yEvaluated (.unary zEvaluated rfl) rfl) rfl

/-! ## Steps, rounds and the final combination -/

/-- One step of a line. The step binds T, so the body reads the line through `weakenAt 0`. -/
theorem step_evaluates {environment : Environment} {store : Store} {stateExpr message : Core.Expr}
    {state : List Word} {word : Word} (phase constant rotation : Nat) (length : state.length = 5)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store)
    (shiftedEvaluated :
      ∀ value, Evaluates (value :: environment) store (stateExpr.weakenAt 0) (stateValue state) store)
    (messageEvaluated : Evaluates environment store message (.word word) store) :
    Evaluates environment store (Ripemd160Implementation.step phase constant rotation stateExpr message)
      (stateValue (Ripemd160Semantics.step phase constant rotation state word)) store := by
  have inner := sum32_evaluates (.cons (lane_evaluates (index := 0) length (by decide) stateEvaluated)
    (.cons (nonlinear_evaluates phase (lane_evaluates (index := 1) length (by decide) stateEvaluated)
      (lane_evaluates (index := 2) length (by decide) stateEvaluated)
      (lane_evaluates (index := 3) length (by decide) stateEvaluated))
    (.cons messageEvaluated (.cons (.word (value := Word.ofNatModulo constant)) .nil))))
  rw [sum32_congr _ _ (mask32_nonlinear256 phase _ _ _)] at inner
  apply Evaluates.letE (sum32_evaluates (.cons (rotateLeft_evaluates rotation inner)
    (.cons (lane_evaluates (index := 4) length (by decide) stateEvaluated) .nil)))
  exact packet_evaluates (.cons (lane_evaluates length (by decide) (shiftedEvaluated _))
    (.cons (.var rfl) (.cons (lane_evaluates length (by decide) (shiftedEvaluated _))
    (.cons (rotateLeft_evaluates 10 (lane_evaluates length (by decide) (shiftedEvaluated _)))
    (.cons (lane_evaluates length (by decide) (shiftedEvaluated _)) .nil)))))

theorem leftWords_lt {index : Nat} (bound : index < 80) : Ripemd160Semantics.leftWords[index]?.getD 0 < 16 :=
  (by decide : ∀ index, index < 80 → Ripemd160Semantics.leftWords[index]?.getD 0 < 16) index bound

theorem rightWords_lt {index : Nat} (bound : index < 80) : Ripemd160Semantics.rightWords[index]?.getD 0 < 16 :=
  (by decide : ∀ index, index < 80 → Ripemd160Semantics.rightWords[index]?.getD 0 < 16) index bound

/-- Under one more binding, the pair at index 0 is read through `weakenAt 0` at index 1. -/
theorem first_weakened_evaluates {environment : Environment} {store : Store} {left right : Value}
    (value : Value) (current : environment[0]? = some (.pair left right)) :
    Evaluates (value :: environment) store ((Expr.first (.var 0)).weakenAt 0) left store := by
  simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
  exact .first (.var current)

theorem second_weakened_evaluates {environment : Environment} {store : Store} {left right : Value}
    (value : Value) (current : environment[0]? = some (.pair left right)) :
    Evaluates (value :: environment) store ((Expr.second (.var 0)).weakenAt 0) right store := by
  simp only [Expr.weakenAt, Nat.zero_le, ↓reduceIte]
  exact .second (.var current)

/-- Round `index` reads the line pair at index 0 and the original (chaining, block) pair at
index `index + 1`. -/
theorem round_evaluates {environment : Environment} {store : Store} {state block : List Word}
    {lines : Ripemd160Semantics.State × Ripemd160Semantics.State} {index : Nat} (bound : index < 80)
    (blockLength : block.length = 16) (leftLength : lines.1.length = 5) (rightLength : lines.2.length = 5)
    (current : environment[0]? = some (.pair (stateValue lines.1) (stateValue lines.2)))
    (original : environment[index + 1]? = some (.pair (stateValue state) (stateValue block))) :
    Evaluates environment store (Ripemd160Implementation.round index)
      (.pair (stateValue (Ripemd160Semantics.steps block lines index).1)
        (stateValue (Ripemd160Semantics.steps block lines index).2)) store :=
  .pair
    (step_evaluates _ _ _ leftLength (.first (.var current)) (fun _ => first_weakened_evaluates _ current)
      (messageWord_evaluates blockLength (leftWords_lt bound) (.second (.var original))))
    (step_evaluates _ _ _ rightLength (.second (.var current)) (fun _ => second_weakened_evaluates _ current)
      (messageWord_evaluates blockLength (rightWords_lt bound) (.second (.var original))))

/-- After eighty rounds the original pair sits at index 81 and the final lines at index 0. -/
theorem result_evaluates {environment : Environment} {store : Store} {state block : List Word}
    {lines : Ripemd160Semantics.State × Ripemd160Semantics.State} (stateLength : state.length = 5)
    (leftLength : lines.1.length = 5) (rightLength : lines.2.length = 5)
    (current : environment[0]? = some (.pair (stateValue lines.1) (stateValue lines.2)))
    (original : environment[81]? = some (.pair (stateValue state) (stateValue block))) :
    Evaluates environment store Ripemd160Implementation.result (stateValue (combine state lines)) store :=
  packet_evaluates (.cons (sum32_evaluates (.cons (lane_evaluates stateLength (by decide) (.first (.var original)))
      (.cons (lane_evaluates leftLength (by decide) (.first (.var current)))
      (.cons (lane_evaluates rightLength (by decide) (.second (.var current))) .nil))))
    (.cons (sum32_evaluates (.cons (lane_evaluates stateLength (by decide) (.first (.var original)))
      (.cons (lane_evaluates leftLength (by decide) (.first (.var current)))
      (.cons (lane_evaluates rightLength (by decide) (.second (.var current))) .nil))))
    (.cons (sum32_evaluates (.cons (lane_evaluates stateLength (by decide) (.first (.var original)))
      (.cons (lane_evaluates leftLength (by decide) (.first (.var current)))
      (.cons (lane_evaluates rightLength (by decide) (.second (.var current))) .nil))))
    (.cons (sum32_evaluates (.cons (lane_evaluates stateLength (by decide) (.first (.var original)))
      (.cons (lane_evaluates leftLength (by decide) (.first (.var current)))
      (.cons (lane_evaluates rightLength (by decide) (.second (.var current))) .nil))))
    (.cons (sum32_evaluates (.cons (lane_evaluates stateLength (by decide) (.first (.var original)))
      (.cons (lane_evaluates leftLength (by decide) (.first (.var current)))
      (.cons (lane_evaluates rightLength (by decide) (.second (.var current))) .nil)))) .nil)))))

/-- The rounds from `start` on, with the original pair `start + 1` entries deep. -/
theorem rounds_evaluates {store : Store} {state block : List Word} (stateLength : state.length = 5)
    (blockLength : block.length = 16) (count : Nat) :
    ∀ (start : Nat) (lines : Ripemd160Semantics.State × Ripemd160Semantics.State) (environment : Environment),
      start + count = 80 → lines.1.length = 5 → lines.2.length = 5 →
      environment[0]? = some (.pair (stateValue lines.1) (stateValue lines.2)) →
      environment[start + 1]? = some (.pair (stateValue state) (stateValue block)) →
      Evaluates environment store
        (((List.range' start count).map Ripemd160Implementation.round).foldr Core.Expr.letE
          Ripemd160Implementation.result)
        (stateValue (combine state ((List.range' start count).foldl (Ripemd160Semantics.steps block) lines)))
        store := by
  induction count with
  | zero =>
      intro start lines environment total leftLength rightLength current original
      have : start = 80 := by omega
      subst this
      exact result_evaluates stateLength leftLength rightLength current original
  | succ count ih =>
      intro start lines environment total leftLength rightLength current original
      rw [List.range'_succ, List.map_cons, List.foldr_cons, List.foldl_cons]
      apply Evaluates.letE (round_evaluates (by omega) blockLength leftLength rightLength current original)
      exact ih (start + 1) _ _ (by omega) (step_length _ _ _ _ _) (step_length _ _ _ _ _) rfl original

/-- The compression binds the (chaining, block) pair, then the line pair, then one
`letE` per round. The specification and the implementation agree modulo 2^32
for every state, so no bound on the chaining words is needed. -/
theorem compress_evaluates {environment : Core.Environment} {stateExpr blockExpr : Core.Expr}
    {state block : List Core.Word} (stateLength : state.length = 5) (blockLength : block.length = 16)
    (stateEvaluated : ∀ store, Core.Evaluates environment store stateExpr (stateValue state) store)
    (blockEvaluated : ∀ store, Core.Evaluates environment store blockExpr (stateValue block) store)
    (store : Core.Store) :
    Core.Evaluates environment store (Ripemd160Implementation.compress stateExpr blockExpr)
      (stateValue (Ripemd160Semantics.compress state block)) store := by
  unfold Ripemd160Implementation.compress
  refine Evaluates.letE (.pair (stateEvaluated store) (blockEvaluated store)) ?_
  refine Evaluates.letE (boundValue := .pair (stateValue state) (stateValue state)) (bodyStore := store) ?_ ?_
  · exact .pair (.first (.var rfl)) (.first (.var rfl))
  rw [compress_eq_combine, List.range_eq_range']
  exact rounds_evaluates stateLength blockLength 80 0 (state, state) _ rfl stateLength stateLength rfl rfl

/-! ## The digest -/

theorem digestFold_evaluates {environment : Environment} {store : Store} {stateExpr : Core.Expr}
    {state : List Word} (length : state.length = 5)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store) :
    ∀ (indices : List Nat), (∀ index ∈ indices, index < 20) →
      ∀ (accumulator : Core.Expr) (total : Word), Evaluates environment store accumulator (.word total) store →
      Evaluates environment store
        (indices.foldl (fun result index => .binary .wordOr (HashBlocks.shift result 8)
          (.binary .wordByte (HashBlocks.number (31 - index % 4))
            (Ripemd160Implementation.lane (index / 4) stateExpr))) accumulator)
        (.word (indices.foldl (fun result index => (result.shiftLeft (Word.ofNatModulo 8)).bitOr
          ((Word.ofNatModulo (31 - index % 4)).byteAt (Ripemd160Semantics.lane state (index / 4)))) total)) store
  | [], _, _, _, evaluated => evaluated
  | index :: indices, bounds, _, _, evaluated =>
      digestFold_evaluates length stateEvaluated indices (fun next member => bounds next (.tail _ member)) _ _
        (.binary (.binary evaluated .word rfl)
          (.binary .word (lane_evaluates length (by have := bounds index (.head _); omega) stateEvaluated) rfl) rfl)

theorem digest_evaluates {environment : Core.Environment} {stateExpr : Core.Expr} {state : List Core.Word}
    (stateLength : state.length = 5)
    (stateEvaluated : ∀ store, Core.Evaluates environment store stateExpr (stateValue state) store)
    (store : Core.Store) :
    Core.Evaluates environment store (Ripemd160Implementation.digest stateExpr)
      (.word (Ripemd160Semantics.digest state)) store :=
  digestFold_evaluates stateLength (stateEvaluated store) (List.range 20)
    (fun _ member => List.mem_range.mp member) _ _ .word

end Solcore.Frontend.RustHull.Ripemd160CompressCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Ripemd160HashCorrespondence
/-! The independent RIPEMD-160 block sequence drives the actual recursive
helper and hash expression. Lookup allocations preserve the actual memory
cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Ripemd160HashCorrespondence
open Core MemoryCorrespondence LogsCorrespondence Sha256BlockCorrespondence

abbrev helperReference (location : Nat) : Value :=
  .cellRef (OptionalCell.cellType (WordMapping.helperType Ripemd160Implementation.parameterType .word)) location

theorem absorbBody_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Ripemd160Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 5) (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Ripemd160Implementation.parameterType .word
      Ripemd160Implementation.absorbBody location captured) :
    ∃ suffix, Evaluates (parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured)
      store Ripemd160Implementation.absorbBody (.inRight .word (.word result)) (store ++ suffix) := by
  induction absorbed generalizing store with
  | @last offset remaining state markerUsed short fits =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := Ripemd160BlockCorrespondence.readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Ripemd160Semantics.readBlock words offset remaining bits markerUsed
      refine ⟨suffix, ?_⟩
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Ripemd160CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (Ripemd160BlockCorrespondence.readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, fits, decide_false]))
      exact .inRight (Ripemd160CompressCorrespondence.digest_evaluates
        (environment := wordsValue (Ripemd160Semantics.compress state block) :: wordsValue block :: environment)
        (stateExpr := .var 0) (Ripemd160CompressCorrespondence.compress_length state block) (fun _ => .var rfl) _)
  | @spill offset remaining state markerUsed result short spills rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := Ripemd160BlockCorrespondence.readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Ripemd160Semantics.readBlock words offset remaining bits markerUsed
      let next := Ripemd160Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Ripemd160CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Ripemd160CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (Ripemd160BlockCorrespondence.readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, spills, decide_true]))
      apply invoke_evaluates (body := Ripemd160Implementation.absorbBody) (captured := captured)
        (input := parametersValue words offset (Word.ofNatModulo 0) bits next true)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number]
        exact .pair (.first (.var rfl)) (.pair (.first (.second (.var rfl))) (.pair .word
          (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated
  | @more offset remaining state markerUsed result full rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := Ripemd160BlockCorrespondence.readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Ripemd160Semantics.readBlock words offset remaining bits markerUsed
      let next := Ripemd160Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Ripemd160CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Ripemd160CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (Ripemd160BlockCorrespondence.readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, full, decide_true]))
      apply invoke_evaluates (body := Ripemd160Implementation.absorbBody) (captured := captured)
        (input := parametersValue words (offset.add (Word.ofNatModulo 64)) (remaining.sub (Word.ofNatModulo 64))
          bits next false)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number, HashBlocks.add]
        exact .pair (.first (.var rfl)) (.pair (.binary (.first (.second (.var rfl))) .word rfl)
          (.pair (.binary (.first (.second (.second (.var rfl)))) .word rfl)
            (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated

theorem absorb_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Ripemd160Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 5) {environment : Environment} {store : Store}
    {argument : Core.Expr}
    (argumentEvaluated : Evaluates environment store argument
      (parametersValue words offset remaining bits state markerUsed) store) :
    ∃ suffix, Evaluates environment store
      (WordMapping.runHelper Ripemd160Implementation.parameterType .word Ripemd160Implementation.absorbBody argument)
      (.inRight .word (.word result)) (store ++ suffix) := by
  let input := parametersValue words offset remaining bits state markerUsed
  let closure := WordMapping.closure Ripemd160Implementation.parameterType .word Ripemd160Implementation.absorbBody
    store.length (input :: environment)
  obtain ⟨suffix, body⟩ := absorbBody_evaluates absorbed length
    (store ++ [.inRight .unit closure]) store.length (input :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  exact runHelper_evaluates argumentEvaluated body

/-- The actual RIPEMD-160 expression touches the input range, then digests it
with the independent block sequence. Only the memory size cell changes. -/
theorem hash_preserves {offset length size result : Word} {state : MemorySemantics.State}
    (touched : MemorySemantics.touchSize? state.size offset length = some size)
    (digested : Ripemd160Semantics.Digest state.words offset length result)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ final, Evaluates environment store (Ripemd160.hash memoryRef sizeRef offsetExpr lengthExpr)
        (.inRight .word (.word result)) final ∧
      StateRel memoryLocation sizeLocation {state with size := size} final ∧
      Frame memoryLocation sizeLocation store final := by
  rw [Ripemd160Implementation.hash_eq]
  let argument := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word offset) (.word length)))
  have touchedEvaluated := touch_evaluates (environment := argument :: environment)
    (reference := HashBlocks.field 1 4 (.var 0)) (offsetExpr := HashBlocks.field 2 4 (.var 0))
    (lengthExpr := HashBlocks.field 3 4 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.var rfl)))) related.size
  simp only [touchResult, touched] at touchedEvaluated
  have touchedRelated := related.touch touched
  obtain ⟨suffix, evaluated⟩ := absorb_evaluates digested Ripemd160CompressCorrespondence.initial_length
    (environment := .unit :: argument :: environment)
    (argument := HashBlocks.packet [.loadCell (HashBlocks.field 0 4 (.var 1)), HashBlocks.field 2 4 (.var 1),
      HashBlocks.field 3 4 (.var 1),
      .binary .wordAnd (.binary .wordMul (HashBlocks.field 3 4 (.var 1)) (HashBlocks.number 8))
        (HashBlocks.number (2 ^ 64 - 1)),
      Ripemd160Implementation.initial, .bool false])
    (.pair (.loadCell (.first (.var rfl)) touchedRelated.memory) (.pair (.first (.second (.second (.var rfl))))
      (.pair (.second (.second (.second (.var rfl))))
        (.pair (.binary (.binary (.second (.second (.second (.var rfl)))) .word rfl) .word rfl)
          (.pair (Ripemd160CompressCorrespondence.initial_evaluates _ _) .bool)))))
  refine ⟨_, ?_, touchedRelated.append suffix, (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ suffix)⟩
  exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
    (LanguageResult.bind_success .word touchedEvaluated evaluated)

end Solcore.Frontend.RustHull.Ripemd160HashCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256CompressCorrespondence
/-! The actual SHA-256 compression and digest Core expressions evaluate to the
independent FIPS 180-4 specification. Every expression is pure: the store is
returned unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256CompressCorrespondence
open Core

abbrev stateValue (words : List Core.Word) : Core.Value :=
  ScalarExecution.bundleValues (words.map Core.Value.word)

/-- Each expression evaluates to the matching word without touching the store. -/
inductive WordsEvaluate (environment : Environment) (store : Store) : List Core.Expr → List Word → Prop where
  | nil : WordsEvaluate environment store [] []
  | cons {expression : Core.Expr} {expressions : List Core.Expr} {value : Word} {values : List Word}
      (head : Evaluates environment store expression (.word value) store)
      (tail : WordsEvaluate environment store expressions values) :
      WordsEvaluate environment store (expression :: expressions) (value :: values)

theorem wordsEvaluate_map {environment : Environment} {store : Store}
    (builder : Nat → Core.Expr) (denotation : Nat → Word) :
    ∀ (indices : List Nat),
      (∀ index ∈ indices, Evaluates environment store (builder index) (.word (denotation index)) store) →
      WordsEvaluate environment store (indices.map builder) (indices.map denotation)
  | [], _ => .nil
  | index :: indices, evaluated =>
      .cons (evaluated index (.head _)) (wordsEvaluate_map builder denotation indices fun next member =>
        evaluated next (.tail _ member))

theorem packet_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    Evaluates environment store (HashBlocks.packet expressions) (stateValue values) store := by
  induction related with
  | nil => exact .unit
  | cons head tail ih =>
      cases tail with
      | nil => exact head
      | cons _ _ => exact .pair head ih

theorem field_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {values : List Word} {index : Nat} {value : Word}
    (evaluated : Evaluates environment store expression (stateValue values) store)
    (found : values[index]? = some value) :
    Evaluates environment store (HashBlocks.field index values.length expression) (.word value) store := by
  induction values generalizing expression index with
  | nil => simp at found
  | cons head tail ih =>
      cases tail with
      | nil =>
          cases index with
          | zero => cases Option.some.inj found; exact evaluated
          | succ index => simp at found
      | cons next rest =>
          cases index with
          | zero => cases Option.some.inj found; exact .first evaluated
          | succ index => simpa [HashBlocks.field] using ih (.second evaluated) found

theorem lane_evaluates {environment : Environment} {store : Store}
    {expression : Core.Expr} {state : List Word} {index : Nat}
    (length : state.length = 8) (bound : index < 8)
    (evaluated : Evaluates environment store expression (stateValue state) store) :
    Evaluates environment store (Sha256Implementation.lane index expression)
      (.word (Sha256Semantics.lane state index)) store := by
  have found := List.getElem?_eq_getElem (show index < state.length by omega)
  have field := field_evaluates evaluated found
  simpa only [Sha256Implementation.lane, length, Sha256Semantics.lane, found, Option.getD_some] using field

theorem foldl_add_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    ∀ {accumulator : Core.Expr} {total : Word}, Evaluates environment store accumulator (.word total) store →
      Evaluates environment store (expressions.foldl HashBlocks.add accumulator)
        (.word (values.foldl Word.add total)) store := by
  induction related with
  | nil => intro _ _ evaluated; exact evaluated
  | cons head _ ih => intro _ _ evaluated; exact ih (.binary evaluated head rfl)

theorem sum32_evaluates {environment : Environment} {store : Store} {expressions : List Core.Expr}
    {values : List Word} (related : WordsEvaluate environment store expressions values) :
    Evaluates environment store (HashBlocks.sum32 expressions) (.word (Sha256Semantics.sum32 values)) store :=
  .binary (foldl_add_evaluates related .word) .word rfl

theorem rotateLeft_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (distance : Nat) (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (HashBlocks.rotateLeft expression distance)
      (.word (Sha256Semantics.rotateLeft value distance)) store :=
  .binary (.binary (.binary evaluated .word rfl) (.binary evaluated .word rfl) rfl) .word rfl

theorem rotateRight_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (distance : Nat) (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (HashBlocks.rotateRight expression distance)
      (.word (Sha256Semantics.rotateRight value distance)) store :=
  rotateLeft_evaluates (32 - distance) evaluated

theorem xor3_evaluates {environment : Environment} {store : Store} {first second third : Core.Expr}
    {firstValue secondValue thirdValue : Word}
    (firstEvaluated : Evaluates environment store first (.word firstValue) store)
    (secondEvaluated : Evaluates environment store second (.word secondValue) store)
    (thirdEvaluated : Evaluates environment store third (.word thirdValue) store) :
    Evaluates environment store (Sha256Implementation.xor3 first second third)
      (.word (Sha256Semantics.xor3 firstValue secondValue thirdValue)) store :=
  .binary (.binary firstEvaluated secondEvaluated rfl) thirdEvaluated rfl

theorem small0_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Sha256Implementation.small0 expression)
      (.word (Sha256Semantics.small0 value)) store :=
  xor3_evaluates (rotateRight_evaluates 7 evaluated) (rotateRight_evaluates 18 evaluated)
    (.binary evaluated .word rfl)

theorem small1_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Sha256Implementation.small1 expression)
      (.word (Sha256Semantics.small1 value)) store :=
  xor3_evaluates (rotateRight_evaluates 17 evaluated) (rotateRight_evaluates 19 evaluated)
    (.binary evaluated .word rfl)

theorem large0_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Sha256Implementation.large0 expression)
      (.word (Sha256Semantics.large0 value)) store :=
  xor3_evaluates (rotateRight_evaluates 2 evaluated) (rotateRight_evaluates 13 evaluated)
    (rotateRight_evaluates 22 evaluated)

theorem large1_evaluates {environment : Environment} {store : Store} {expression : Core.Expr}
    {value : Word} (evaluated : Evaluates environment store expression (.word value) store) :
    Evaluates environment store (Sha256Implementation.large1 expression)
      (.word (Sha256Semantics.large1 value)) store :=
  xor3_evaluates (rotateRight_evaluates 6 evaluated) (rotateRight_evaluates 11 evaluated)
    (rotateRight_evaluates 25 evaluated)

theorem choose_evaluates {environment : Environment} {store : Store} {x y z : Core.Expr}
    {xValue yValue zValue : Word}
    (xEvaluated : Evaluates environment store x (.word xValue) store)
    (yEvaluated : Evaluates environment store y (.word yValue) store)
    (zEvaluated : Evaluates environment store z (.word zValue) store) :
    Evaluates environment store (Sha256Implementation.choose x y z)
      (.word (Sha256Semantics.choose xValue yValue zValue)) store :=
  .binary (.binary xEvaluated yEvaluated rfl) (.binary (.unary xEvaluated rfl) zEvaluated rfl) rfl

theorem majority_evaluates {environment : Environment} {store : Store} {x y z : Core.Expr}
    {xValue yValue zValue : Word}
    (xEvaluated : Evaluates environment store x (.word xValue) store)
    (yEvaluated : Evaluates environment store y (.word yValue) store)
    (zEvaluated : Evaluates environment store z (.word zValue) store) :
    Evaluates environment store (Sha256Implementation.majority x y z)
      (.word (Sha256Semantics.majority xValue yValue zValue)) store :=
  xor3_evaluates (.binary xEvaluated yEvaluated rfl) (.binary xEvaluated zEvaluated rfl)
    (.binary yEvaluated zEvaluated rfl)

theorem initial_length : Sha256Semantics.initial.length = 8 := rfl

theorem round_length (state : List Word) (word : Word) (constant : Nat) :
    (Sha256Semantics.round state word constant).length = 8 := rfl

theorem compress_length (state block : List Word) : (Sha256Semantics.compress state block).length = 8 := by
  simp [Sha256Semantics.compress]

theorem numbers_evaluates (environment : Environment) (store : Store) (values : List Nat) :
    Evaluates environment store (HashBlocks.packet (values.map HashBlocks.number))
      (stateValue (values.map Word.ofNatModulo)) store :=
  packet_evaluates (wordsEvaluate_map HashBlocks.number Word.ofNatModulo values fun _ _ => .word)

theorem initial_evaluates (environment : Core.Environment) (store : Core.Store) :
    Core.Evaluates environment store Sha256Implementation.initial (stateValue Sha256Semantics.initial) store :=
  numbers_evaluates environment store _

/-- One round reads the current state at index 0 and W(t) at index 64. -/
theorem round_evaluates {environment : Environment} {store : Store} {state : List Word} {word : Word}
    (constant : Nat) (length : state.length = 8)
    (current : environment[0]? = some (stateValue state))
    (scheduled : environment[64]? = some (.word word)) :
    Evaluates environment store (Sha256Implementation.round constant)
      (stateValue (Sha256Semantics.round state word constant)) store := by
  apply Evaluates.letE
  · exact sum32_evaluates (.cons (lane_evaluates length (by decide) (.var current))
      (.cons (large1_evaluates (lane_evaluates length (by decide) (.var current)))
      (.cons (choose_evaluates (lane_evaluates length (by decide) (.var current))
        (lane_evaluates length (by decide) (.var current)) (lane_evaluates length (by decide) (.var current)))
      (.cons .word (.cons (.var scheduled) .nil)))))
  apply Evaluates.letE
  · exact sum32_evaluates (.cons (large0_evaluates (lane_evaluates length (by decide) (.var current)))
      (.cons (majority_evaluates (lane_evaluates length (by decide) (.var current))
        (lane_evaluates length (by decide) (.var current)) (lane_evaluates length (by decide) (.var current))) .nil))
  exact packet_evaluates (.cons (sum32_evaluates (.cons (.var rfl) (.cons (.var rfl) .nil)))
    (.cons (lane_evaluates length (by decide) (.var current))
    (.cons (lane_evaluates length (by decide) (.var current))
    (.cons (lane_evaluates length (by decide) (.var current))
    (.cons (sum32_evaluates (.cons (lane_evaluates length (by decide) (.var current)) (.cons (.var rfl) .nil)))
    (.cons (lane_evaluates length (by decide) (.var current))
    (.cons (lane_evaluates length (by decide) (.var current))
    (.cons (lane_evaluates length (by decide) (.var current)) .nil))))))))

/-- The chaining addition reads the initial state at index 64 and the final state at index 0. -/
theorem completed_evaluates {environment : Environment} {store : Store} {initial final : List Word}
    (initialLength : initial.length = 8) (finalLength : final.length = 8)
    (initialFound : environment[64]? = some (stateValue initial))
    (current : environment[0]? = some (stateValue final)) :
    Evaluates environment store Sha256Implementation.completed
      (stateValue ((List.range 8).map fun index =>
        Sha256Semantics.sum32 [Sha256Semantics.lane initial index, Sha256Semantics.lane final index])) store := by
  apply packet_evaluates
  apply wordsEvaluate_map
  intro index member
  have bound := List.mem_range.mp member
  exact sum32_evaluates (.cons (lane_evaluates initialLength bound (.var initialFound))
    (.cons (lane_evaluates finalLength bound (.var current)) .nil))

/-- The remaining rounds, with the initial state `depth` entries deep and the
remaining schedule word `k` at index `64 - k`. -/
theorem rounds_evaluates (constants : List Nat) :
    ∀ (words : List Word) (depth : Nat) {initial state : List Word} (environment : Environment) (store : Store),
      words.length = constants.length → depth + constants.length = 64 →
      initial.length = 8 → state.length = 8 →
      environment[0]? = some (stateValue state) →
      environment[depth]? = some (stateValue initial) →
      (∀ (k j : Nat) (word : Word), j + k = 64 → words[k]? = some word → environment[j]? = some (.word word)) →
      Evaluates environment store
        ((constants.map Sha256Implementation.round).foldr Core.Expr.letE Sha256Implementation.completed)
        (stateValue ((List.range 8).map fun index => Sha256Semantics.sum32 [Sha256Semantics.lane initial index,
          Sha256Semantics.lane ((words.zip constants).foldl
            (fun current (word, constant) => Sha256Semantics.round current word constant) state) index])) store := by
  induction constants with
  | nil =>
      intro words depth initial state environment store lengths total initialLength length current initialFound _
      cases words with
      | nil =>
          have : depth = 64 := by simpa using total
          subst this
          exact completed_evaluates initialLength length initialFound current
      | cons _ _ => simp at lengths
  | cons constant constants ih =>
      intro words depth initial state environment store lengths total initialLength length current initialFound scheduled
      cases words with
      | nil => simp at lengths
      | cons word words =>
          simp only [List.map_cons, List.foldr_cons, List.zip_cons_cons, List.foldl_cons]
          apply Evaluates.letE (round_evaluates constant length current (scheduled 0 64 word rfl rfl))
          apply ih words (depth + 1) _ store (Nat.succ.inj lengths) (by simp at total; omega) initialLength
            (round_length state word constant) rfl initialFound
          intro k j next sum found
          have bound : k < words.length := (List.getElem?_eq_some_iff.mp found).1
          have short : words.length < 64 := by simp at total lengths; omega
          cases j with
          | zero => omega
          | succ j => exact scheduled (k + 1) j next (by omega) found

theorem extend_length (count : Nat) :
    ∀ (recent : List Word), (Sha256Semantics.extend count recent).length = recent.length + count := by
  induction count with
  | zero => intro recent; rfl
  | succ count ih =>
      intro recent
      rw [Sha256Semantics.extend, ih, List.length_cons]
      omega

theorem recent_evaluates {store : Store} {recent : List Word} {rest : Environment} {index : Nat}
    (bound : index < recent.length) :
    Evaluates (recent.map Value.word ++ rest) store (.var index) (.word (recent[index]?.getD Word.zero)) store := by
  apply Evaluates.var
  rw [List.getElem?_append_left (by simpa using bound), List.getElem?_map, List.getElem?_eq_getElem bound]
  rfl

/-- Schedule words 16 to 63 extend the recent words held newest first. -/
theorem scheduleExtend_evaluates {store : Store} (count : Nat) :
    ∀ (start : Nat) (recent : List Word) (rest : Environment) (body : Core.Expr) (result : Value),
      16 ≤ start → 16 ≤ recent.length →
      Evaluates ((Sha256Semantics.extend count recent).map Value.word ++ rest) store body result store →
      Evaluates (recent.map Value.word ++ rest) store
        (((List.range' start count).map Sha256Implementation.scheduleWord).foldr Core.Expr.letE body) result store := by
  induction count with
  | zero => intro _ _ _ _ _ _ _ evaluated; exact evaluated
  | succ count ih =>
      intro start recent rest body result lower longer evaluated
      rw [List.range'_succ, List.map_cons, List.foldr_cons]
      have word : Sha256Implementation.scheduleWord start =
          HashBlocks.sum32 [Sha256Implementation.small1 (.var 1), .var 6, Sha256Implementation.small0 (.var 14), .var 15] := by
        simp only [Sha256Implementation.scheduleWord, if_neg (Nat.not_lt.mpr lower)]
      rw [word]
      apply Evaluates.letE (sum32_evaluates (.cons (small1_evaluates (recent_evaluates (by omega)))
        (.cons (recent_evaluates (by omega)) (.cons (small0_evaluates (recent_evaluates (by omega)))
        (.cons (recent_evaluates (by omega)) .nil)))))
      exact ih (start + 1) (_ :: recent) rest body result (by omega) (by simp; omega) evaluated

/-- Schedule words 0 to 15 copy the block fields; the block pair sits just past the words read so far. -/
theorem scheduleBlock_evaluates {store : Store} {block : List Word} (blockLength : block.length = 16)
    {stateVal : Value} (count : Nat) :
    ∀ (start : Nat) (rest : Environment) (body : Core.Expr) (result : Value), start + count = 16 →
      Evaluates (block.reverse.map Value.word ++ .pair stateVal (stateValue block) :: rest) store body result store →
      Evaluates ((block.take start).reverse.map Value.word ++ .pair stateVal (stateValue block) :: rest) store
        (((List.range' start count).map Sha256Implementation.scheduleWord).foldr Core.Expr.letE body) result store := by
  induction count with
  | zero =>
      intro start rest body result total evaluated
      have : start = block.length := by omega
      subst this
      simpa only [List.take_length, List.range'_zero, List.map_nil, List.foldr_nil] using evaluated
  | succ count ih =>
      intro start rest body result total evaluated
      have bound : start < block.length := by omega
      rw [List.range'_succ, List.map_cons, List.foldr_cons]
      have word : Sha256Implementation.scheduleWord start = HashBlocks.field start 16 (.second (.var start)) := by
        simp only [Sha256Implementation.scheduleWord, if_pos (show start < 16 by omega)]
      rw [word]
      have found : ((block.take start).reverse.map Value.word ++ .pair stateVal (stateValue block) :: rest)[start]? =
          some (.pair stateVal (stateValue block)) := by
        rw [List.getElem?_append_right (by simp; omega)]
        simp [Nat.min_eq_left (Nat.le_of_lt bound)]
      have field := field_evaluates (store := store) (.second (.var found)) (List.getElem?_eq_getElem bound)
      rw [blockLength] at field
      apply Evaluates.letE field
      have step : (block.take (start + 1)).reverse = block[start] :: (block.take start).reverse := by
        rw [← List.take_append_getElem bound, List.reverse_append, List.reverse_singleton, List.singleton_append]
      have next := ih (start + 1) rest body result (by omega) evaluated
      rw [step] at next
      exact next

theorem compress_evaluates {environment : Core.Environment} {stateExpr blockExpr : Core.Expr}
    {state block : List Core.Word} (stateLength : state.length = 8) (blockLength : block.length = 16)
    (stateEvaluated : ∀ store, Core.Evaluates environment store stateExpr (stateValue state) store)
    (blockEvaluated : ∀ store, Core.Evaluates environment store blockExpr (stateValue block) store)
    (store : Core.Store) :
    Core.Evaluates environment store (Sha256Implementation.compress stateExpr blockExpr)
      (stateValue (Sha256Semantics.compress state block)) store := by
  unfold Sha256Implementation.compress
  apply Evaluates.letE (.pair (stateEvaluated store) (blockEvaluated store))
  rw [show List.range 64 = List.range' 0 16 ++ List.range' 16 48 from rfl, List.map_append, List.foldr_append]
  apply scheduleBlock_evaluates blockLength 16 0 environment _ _ rfl
  apply scheduleExtend_evaluates 48 16 block.reverse _ _ _ (by omega) (by simp [blockLength])
  have extended : (Sha256Semantics.extend 48 block.reverse).length = 64 := by
    rw [extend_length, List.length_reverse, blockLength]
  have found : ((Sha256Semantics.extend 48 block.reverse).map Value.word ++
      .pair (stateValue state) (stateValue block) :: environment)[64]? =
        some (.pair (stateValue state) (stateValue block)) := by
    rw [List.getElem?_append_right (by simp [extended])]
    simp [extended]
  apply Evaluates.letE (.first (.var found))
  have rounds := rounds_evaluates Sha256Semantics.constants (Sha256Semantics.schedule block) 0
    (initial := state) (state := state)
    (stateValue state :: ((Sha256Semantics.extend 48 block.reverse).map Value.word ++
      .pair (stateValue state) (stateValue block) :: environment)) store
    (by simp [Sha256Semantics.schedule, extended, Sha256Semantics.constants]) rfl stateLength stateLength rfl rfl
    (by
      intro k j word sum found
      have bound : k < (Sha256Semantics.schedule block).length := (List.getElem?_eq_some_iff.mp found).1
      simp only [Sha256Semantics.schedule, List.length_reverse, extended] at bound
      rw [Sha256Semantics.schedule, List.getElem?_reverse (by simpa [extended] using bound), extended] at found
      cases j with
      | zero => omega
      | succ j =>
          rw [List.getElem?_cons_succ, List.getElem?_append_left (by simp [extended]; omega), List.getElem?_map]
          have : j = 64 - 1 - k := by omega
          rw [this, found]
          rfl)
  exact rounds

theorem digestFold_evaluates {environment : Environment} {store : Store} {stateExpr : Core.Expr}
    {state : List Word} (length : state.length = 8)
    (stateEvaluated : Evaluates environment store stateExpr (stateValue state) store) :
    ∀ (indices : List Nat), (∀ index ∈ indices, index < 8) →
      ∀ (accumulator : Core.Expr) (total : Word), Evaluates environment store accumulator (.word total) store →
      Evaluates environment store
        (indices.foldl (fun result index => .binary .wordOr (HashBlocks.shift result 32)
          (Sha256Implementation.lane index stateExpr)) accumulator)
        (.word (indices.foldl (fun result index => (result.shiftLeft (Word.ofNatModulo 32)).bitOr
          (Sha256Semantics.lane state index)) total)) store
  | [], _, _, _, evaluated => evaluated
  | index :: indices, bounds, _, _, evaluated =>
      digestFold_evaluates length stateEvaluated indices (fun next member => bounds next (.tail _ member)) _ _
        (.binary (.binary evaluated .word rfl) (lane_evaluates length (bounds index (.head _)) stateEvaluated) rfl)

theorem digest_evaluates {environment : Core.Environment} {stateExpr : Core.Expr} {state : List Core.Word}
    (stateLength : state.length = 8)
    (stateEvaluated : ∀ store, Core.Evaluates environment store stateExpr (stateValue state) store)
    (store : Core.Store) :
    Core.Evaluates environment store (Sha256Implementation.digest stateExpr)
      (.word (Sha256Semantics.digest state)) store :=
  digestFold_evaluates stateLength (stateEvaluated store) (List.range 8)
    (fun _ member => List.mem_range.mp member) _ _ .word

end Solcore.Frontend.RustHull.Sha256CompressCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Sha256HashCorrespondence
/-! The independent SHA-256 block sequence drives the actual recursive helper
and hash expression. Lookup allocations preserve the actual memory cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Sha256HashCorrespondence
open Core MemoryCorrespondence LogsCorrespondence Sha256BlockCorrespondence

abbrev helperReference (location : Nat) : Value :=
  .cellRef (OptionalCell.cellType (WordMapping.helperType Sha256Implementation.parameterType .word)) location

theorem absorbBody_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Sha256Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 8) (store : Store) (location : Nat) (captured : Environment)
    (installed : WordMapping.Installed store Sha256Implementation.parameterType .word
      Sha256Implementation.absorbBody location captured) :
    ∃ suffix, Evaluates (parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured)
      store Sha256Implementation.absorbBody (.inRight .word (.word result)) (store ++ suffix) := by
  induction absorbed generalizing store with
  | @last offset remaining state markerUsed short fits =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      refine ⟨suffix, ?_⟩
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, fits, decide_false]))
      exact .inRight (Sha256CompressCorrespondence.digest_evaluates
        (environment := wordsValue (Sha256Semantics.compress state block) :: wordsValue block :: environment)
        (stateExpr := .var 0) (Sha256CompressCorrespondence.compress_length state block) (fun _ => .var rfl) _)
  | @spill offset remaining state markerUsed result short spills rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      let next := Sha256Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Sha256CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifFalse (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, short, decide_false]))
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, spills, decide_true]))
      apply invoke_evaluates (body := Sha256Implementation.absorbBody) (captured := captured)
        (input := parametersValue words offset (Word.ofNatModulo 0) bits next true)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number]
        exact .pair (.first (.var rfl)) (.pair (.first (.second (.var rfl))) (.pair .word
          (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated
  | @more offset remaining state markerUsed result full rest ih =>
      let environment := parametersValue words offset remaining bits state markerUsed :: helperReference location :: captured
      obtain ⟨suffix, blockEvaluated⟩ := readBlock_evaluates (environment := environment) store
        (parameters := .var 0) (Stable.var rfl)
      let block := Sha256Semantics.readBlock words offset remaining bits markerUsed
      let next := Sha256Semantics.compress state block
      obtain ⟨tail, bodyEvaluated⟩ := ih (Sha256CompressCorrespondence.compress_length state block) (store ++ suffix)
        (installed_append installed suffix)
      refine ⟨suffix ++ tail, ?_⟩
      rw [← List.append_assoc]
      apply LanguageResult.bind_success .word blockEvaluated
      have compressed := Sha256CompressCorrespondence.compress_evaluates
        (environment := wordsValue block :: environment) (stateExpr := HashBlocks.field 4 6 (.var 1))
        (blockExpr := .var 0) length (readBlock_length ..)
        (fun _ => .first (.second (.second (.second (.second (.var rfl)))))) (fun _ => .var rfl) (store ++ suffix)
      apply Evaluates.letE compressed
      apply Evaluates.ifTrue (.binary (.first (.second (.second (.var rfl)))) .word
        (by simp only [BinaryOp.apply, full, decide_true]))
      apply invoke_evaluates (body := Sha256Implementation.absorbBody) (captured := captured)
        (input := parametersValue words (offset.add (Word.ofNatModulo 64)) (remaining.sub (Word.ofNatModulo 64))
          bits next false)
        (.var rfl) (installed_append installed suffix)
      · simp [Core.Expr.weakenAt, HashBlocks.packet, HashBlocks.field, HashBlocks.number, HashBlocks.add]
        exact .pair (.first (.var rfl)) (.pair (.binary (.first (.second (.var rfl))) .word rfl)
          (.pair (.binary (.first (.second (.second (.var rfl)))) .word rfl)
            (.pair (.first (.second (.second (.second (.var rfl))))) (.pair (.var rfl) .bool))))
      · exact bodyEvaluated

theorem absorb_evaluates {words : MemorySemantics.Entries} {bits offset remaining result : Word}
    {state : List Word} {markerUsed : Bool}
    (absorbed : Sha256Semantics.Absorb words bits offset remaining state markerUsed result)
    (length : state.length = 8) {environment : Environment} {store : Store}
    {argument : Core.Expr}
    (argumentEvaluated : Evaluates environment store argument
      (parametersValue words offset remaining bits state markerUsed) store) :
    ∃ suffix, Evaluates environment store
      (WordMapping.runHelper Sha256Implementation.parameterType .word Sha256Implementation.absorbBody argument)
      (.inRight .word (.word result)) (store ++ suffix) := by
  let input := parametersValue words offset remaining bits state markerUsed
  let closure := WordMapping.closure Sha256Implementation.parameterType .word Sha256Implementation.absorbBody
    store.length (input :: environment)
  obtain ⟨suffix, body⟩ := absorbBody_evaluates absorbed length
    (store ++ [.inRight .unit closure]) store.length (input :: environment)
    (by simp [WordMapping.Installed, Store.read?, closure])
  refine ⟨[.inRight .unit closure] ++ suffix, ?_⟩
  rw [← List.append_assoc]
  exact runHelper_evaluates argumentEvaluated body

/-- The actual SHA-256 expression touches the input range, then digests it with
the independent block sequence. Only the memory size cell changes. -/
theorem hash_preserves {offset length size result : Word} {state : MemorySemantics.State}
    (touched : MemorySemantics.touchSize? state.size offset length = some size)
    (digested : Sha256Semantics.Digest state.words offset length result)
    {environment : Environment} {store : Store} {memoryLocation sizeLocation : Nat}
    {memoryRef sizeRef offsetExpr lengthExpr : Core.Expr}
    (related : StateRel memoryLocation sizeLocation state store)
    (memoryEvaluated : Evaluates environment store memoryRef (.cellRef WordMapping.type memoryLocation) store)
    (sizeEvaluated : Evaluates environment store sizeRef (.cellRef .word sizeLocation) store)
    (offsetEvaluated : Evaluates environment store offsetExpr (.word offset) store)
    (lengthEvaluated : Evaluates environment store lengthExpr (.word length) store) :
    ∃ final, Evaluates environment store (Sha256.hash memoryRef sizeRef offsetExpr lengthExpr)
        (.inRight .word (.word result)) final ∧
      StateRel memoryLocation sizeLocation {state with size := size} final ∧
      Frame memoryLocation sizeLocation store final := by
  rw [Sha256Implementation.hash_eq]
  let argument := Value.pair (.cellRef WordMapping.type memoryLocation) (.pair (.cellRef .word sizeLocation)
    (.pair (.word offset) (.word length)))
  have touchedEvaluated := touch_evaluates (environment := argument :: environment)
    (reference := HashBlocks.field 1 4 (.var 0)) (offsetExpr := HashBlocks.field 2 4 (.var 0))
    (lengthExpr := HashBlocks.field 3 4 (.var 0))
    (.first (.second (.var rfl))) (.first (.second (.second (.var rfl))))
    (.second (.second (.second (.var rfl)))) related.size
  simp only [touchResult, touched] at touchedEvaluated
  have touchedRelated := related.touch touched
  obtain ⟨suffix, evaluated⟩ := absorb_evaluates digested Sha256CompressCorrespondence.initial_length
    (environment := .unit :: argument :: environment)
    (argument := HashBlocks.packet [.loadCell (HashBlocks.field 0 4 (.var 1)), HashBlocks.field 2 4 (.var 1),
      HashBlocks.field 3 4 (.var 1),
      .binary .wordAnd (.binary .wordMul (HashBlocks.field 3 4 (.var 1)) (HashBlocks.number 8))
        (HashBlocks.number (2 ^ 64 - 1)),
      Sha256Implementation.initial, .bool false])
    (.pair (.loadCell (.first (.var rfl)) touchedRelated.memory) (.pair (.first (.second (.second (.var rfl))))
      (.pair (.second (.second (.second (.var rfl))))
        (.pair (.binary (.binary (.second (.second (.second (.var rfl)))) .word rfl) .word rfl)
          (.pair (Sha256CompressCorrespondence.initial_evaluates _ _) .bool)))))
  refine ⟨_, ?_, touchedRelated.append suffix, (Frame.touch _ _ _ _ _ _).trans (Frame.append _ _ _ suffix)⟩
  exact .letE (.pair memoryEvaluated (.pair sizeEvaluated (.pair offsetEvaluated lengthEvaluated)))
    (LanguageResult.bind_success .word touchedEvaluated evaluated)

end Solcore.Frontend.RustHull.Sha256HashCorrespondence
end
