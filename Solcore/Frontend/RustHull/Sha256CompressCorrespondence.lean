import Solcore.Frontend.RustHull.Sha256Implementation
import Solcore.Frontend.RustHull.ScalarInputCorrespondence

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
