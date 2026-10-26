import Solcore.Frontend.RustHull.Ripemd160Implementation
import Solcore.Frontend.RustHull.ScalarInputCorrespondence

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
