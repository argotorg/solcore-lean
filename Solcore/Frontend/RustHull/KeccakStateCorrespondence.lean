import Solcore.Frontend.RustHull.KeccakSemantics
import Solcore.Frontend.RustHull.Keccak
import Solcore.Frontend.RustHull.ScalarInputCorrespondence

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
