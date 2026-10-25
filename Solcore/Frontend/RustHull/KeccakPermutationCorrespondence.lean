import Solcore.Frontend.RustHull.KeccakStateCorrespondence

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
