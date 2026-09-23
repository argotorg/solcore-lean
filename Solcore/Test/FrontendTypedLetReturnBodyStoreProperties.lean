import Solcore.Frontend.TypedLetReturnBody

/-! Exact source replay does not identify stores or erase pending work.
Core loads demonstrate why preservation alone cannot establish independence. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyStore

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetStore", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-store.sol"⟩, 163, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name : String) (value : Syntax.Expr) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => (returned (ref previous)).value
  | name :: rest, previous => binding name (ref previous) :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def seedTable : LocalNameTable := [("seed", id 0)]
private def seedEnv (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem chainCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))

theorem arbitrary_length_raw_paths_replay_actual_values_without_typing_or_name_freshness
    (names : List String) (value : Core.Value) (first replacement : Core.Store) :
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) first (chain names "seed") value first ∧
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) replacement (chain names "seed") value replacement ∧
    TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv value) replacement (chain names "seed") value replacement (3 * names.length + 1) := by
  have original := chainCost names "seed" seedTable (seedEnv value) value first (.identifier .head .head)
  exact ⟨original.erase, original.erase.change_store replacement, original.change_store replacement⟩

theorem bidirectional_replay_requires_the_claimed_final_store_to_equal_its_own_initial_store
    (names : List String) (actual value : Core.Value) (first finalStore replacement : Core.Store) (cost : Nat) :
    (TypedLetReturnBodyEvaluates owner seedTable (seedEnv actual) first (chain names "seed") value finalStore ↔
      finalStore = first ∧ TypedLetReturnBodyEvaluates owner seedTable (seedEnv actual) replacement (chain names "seed") value replacement) ∧
    (TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual) first (chain names "seed") value finalStore cost ↔
      finalStore = first ∧ TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual) replacement (chain names "seed") value replacement cost) :=
  ⟨typedLetReturnBodyEvaluates_store_iff, typedLetReturnBodyEvaluatesWithCost_store_iff⟩

theorem replacement_success_cannot_justify_an_incorrect_original_final_store
    (names : List String) (value : Core.Value) (first replacement : Core.Store) (different : replacement ≠ first) :
    TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) replacement (chain names "seed") value replacement ∧
    ¬ TypedLetReturnBodyEvaluates owner seedTable (seedEnv value) first (chain names "seed") value replacement := by
  refine ⟨(chainCost names "seed" seedTable (seedEnv value) value replacement (.identifier .head .head)).erase, ?_⟩
  intro wrong
  exact different ((typedLetReturnBodyEvaluates_store_iff (replacement := replacement)).mp wrong).1

private def subtract (left right : String) : Syntax.Expr := ⟨span, .binary (ref left) ⟨span, .subtract⟩ (ref right)⟩
private def table : LocalNameTable := [("right", id 2), ("left", id 1), ("c", id 0)]
private def staticInputs : LocalTypeInputs :=
  ⟨[⟨"right", id 2, .word⟩, ⟨"left", id 1, .word⟩, ⟨"c", id 0, .bool⟩], by decide⟩
private def environment (choice : Bool) (left right : Core.Word) : Resolved.Environment :=
  [(id 2, .word right), (id 1, .word left), (id 0, .bool choice)]
private def inputs (choice : Bool) (left right : Core.Word) : LocalInputs :=
  ⟨[⟨"right", id 2, .word, .word right, .word⟩, ⟨"left", id 1, .word, .word left, .word⟩,
    ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 2, id 1, id 0].Nodup; decide⟩
private def tailBody : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "left")) (some (returned (subtract "right" "left")))⟩]⟩
private def body : Syntax.Block := ⟨span, binding "unused" (subtract "left" "right") :: tailBody.value⟩
private def tailCore : Core.Expr := .ifE (.var 3) (.var 2) (.binary .wordSub (.var 1) (.var 2))
private def core : Core.Expr := .letE (.binary .wordSub (.var 1) (.var 0)) tailCore
private def result (choice : Bool) (left right : Core.Word) : Core.Value := .word (if choice then left else right.sub left)
private def required (choice : Bool) : Nat := if choice then 11 else 15
private theorem elaborated : TypedLetReturnBodyElaborates (types .word) owner staticInputs body core .word :=
  .binding (.named .head) (by decide)
    (.subtract (.identifier (.tail (by decide) .head)) (.identifier .head))
    (.binary (.var (.tail (by decide) .head)) (.var .head)) (.binary (.var (.tail (by decide) .head)) (.var .head))
    (.terminal (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.var (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.single (.expression (.identifier (.tail (by decide) (.tail (by decide) .head)))
        (.var (.tail (by decide) (.tail (by decide) .head))) (.var (.tail (by decide) (.tail (by decide) .head)))))
      (.single (.expression (.subtract (.identifier (.tail (by decide) .head)) (.identifier (.tail (by decide) (.tail (by decide) .head))))
        (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))
        (.binary (.var (.tail (by decide) .head)) (.var (.tail (by decide) (.tail (by decide) .head))))))))
private theorem costed (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) store body (result choice left right) store (required choice) := by
  have leftC : LocalExpressionEvaluatesWithCost table (environment choice left right) store (ref "left") (.word left) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have rightC : LocalExpressionEvaluatesWithCost table (environment choice left right) store (ref "right") (.word right) store 1 := .identifier .head .head
  have initial : LocalExpressionEvaluatesWithCost table (environment choice left right) store (subtract "left" "right") (.word (left.sub right)) store 5 :=
    .subtract leftC rightC
  have c : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have l : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "left") (.word left) store 1 := .identifier (.tail (by decide) (.tail (by decide) .head)) (.tail (by decide) (.tail (by decide) .head))
  have r : LocalExpressionEvaluatesWithCost (("unused", id 3) :: table) ((id 3, .word (left.sub right)) :: environment choice left right)
      store (ref "right") (.word right) store 1 := .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  cases choice
  · exact TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
      (annotation := annotation) (tailCost := 8) initial (.terminal (.ifFalse c (.single (.expression (.subtract r l)))))
  · exact TypedLetReturnBodyEvaluatesWithCost.binding (owner := owner) (name := ⟨span, "unused"⟩)
      (annotation := annotation) (tailCost := 4) initial (.terminal (.ifTrue c (.single (.expression l))))
private theorem runExact (choice : Bool) (left right : Core.Word) (store : Core.Store) (fuel : Nat) (observed : Core.StatefulRunResult)
    (ran : Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) = observed) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body store = some (.word, observed) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core, elaborated.complete, ran⟩

theorem unused_noncommutative_initializers_and_asymmetric_arms_retain_their_own_exact_costs
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) first body (result choice left right) first (required choice) ∧
    TypedLetReturnBodyEvaluatesWithCost owner table (environment choice left right) replacement body (result choice left right) replacement (required choice) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (required choice) body replacement = some (.word, .done (result choice left right) replacement) :=
  ⟨costed choice left right first, (costed choice left right first).change_store replacement,
    runExact choice left right replacement _ _
      ((((costed choice left right first).change_store replacement).checked_runStateful_done_iff elaborated.complete rfl).mpr (Nat.le_refl _))⟩

theorem actual_typed_same_fuel_observations_replay_values_and_exhaustion_not_complete_states
    (choice : Bool) (left right : Core.Word) (value : Core.Value) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first = some (.word, .done value first) ↔
      (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement = some (.word, .done value replacement)) ∧
    ((∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first = some (.word, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement = some (.word, .outOfFuel checkpoint)) :=
  ⟨(inputs choice left right).runTypedLetReturnBody?_done_store_iff (types .word) owner fuel body first replacement .word value,
    (inputs choice left right).runTypedLetReturnBody?_outOfFuel_store_iff (types .word) owner fuel body first replacement .word⟩

theorem independent_eleven_or_fifteen_step_thresholds_hold_at_every_fuel_in_each_store
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body first =
      some (.word, .done (result choice left right) first) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice left right).runTypedLetReturnBody? (types .word) owner fuel body replacement =
      some (.word, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  have checked : (inputs choice left right).checkTypedLetReturnBody? (types .word) owner body = some (core, .word) := elaborated.complete
  simp only [LocalInputs.runTypedLetReturnBody?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact ⟨(costed choice left right first).checked_runStateful_done_iff elaborated.complete rfl,
    ((costed choice left right first).change_store replacement).checked_runStateful_outOfFuel_iff elaborated.complete rfl⟩

private def initializerCheckpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryRight .wordSub (.var 0) [.word right, .word left, .bool choice],
    .letBody tailCore [.word right, .word left, .bool choice]], store⟩
private def tailCheckpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 2) (.binary .wordSub (.var 1) (.var 2))
    [.word (left.sub right), .word right, .word left, .bool choice]], store⟩
private theorem initialExhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body store = some (.word, .outOfFuel (initializerCheckpoint choice left right store)) :=
  runExact choice left right store 3 _ rfl
private theorem tailExhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body store = some (.word, .outOfFuel (tailCheckpoint choice left right store)) := by
  apply runExact choice left right store 9 _
  cases choice <;> rfl
theorem distinct_nonempty_stores_remain_distinct_in_initializer_and_tail_checkpoints
    (choice : Bool) (left right : Core.Word) (tail : Core.Store) :
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body (.unit :: tail) =
      some (.word, .outOfFuel (initializerCheckpoint choice left right (.unit :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 3 body (.bool true :: tail) =
      some (.word, .outOfFuel (initializerCheckpoint choice left right (.bool true :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body (.unit :: tail) =
      some (.word, .outOfFuel (tailCheckpoint choice left right (.unit :: tail))) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner 9 body (.bool true :: tail) =
      some (.word, .outOfFuel (tailCheckpoint choice left right (.bool true :: tail))) ∧
    initializerCheckpoint choice left right (.unit :: tail) ≠ initializerCheckpoint choice left right (.bool true :: tail) ∧
    tailCheckpoint choice left right (.unit :: tail) ≠ tailCheckpoint choice left right (.bool true :: tail) := by
  refine ⟨initialExhausted choice left right _, initialExhausted choice left right _,
    tailExhausted choice left right _, tailExhausted choice left right _, ?_, ?_⟩ <;>
    intro same <;> have stored := congrArg Core.State.store same <;> cases stored

theorem each_genuine_checkpoint_resumes_its_own_store_through_the_unused_initializer
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    Core.runStateful 6 (initializerCheckpoint choice left right first) = .outOfFuel (tailCheckpoint choice left right first) ∧
    Core.runStateful (required choice - 9) (tailCheckpoint choice left right replacement) = .done (result choice left right) replacement ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (3 + additional) body first =
      some (.word, Core.runStateful additional (initializerCheckpoint choice left right first)) ∧
    (inputs choice left right).runTypedLetReturnBody? (types .word) owner (9 + additional) body replacement =
      some (.word, Core.runStateful additional (tailCheckpoint choice left right replacement)) :=
  ⟨by cases choice <;> rfl, by cases choice <;> rfl,
    LocalInputs.runTypedLetReturnBody?_resume (initialExhausted choice left right first) additional,
    LocalInputs.runTypedLetReturnBody?_resume (tailExhausted choice left right replacement) additional⟩

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def seedInputs {type : Core.Ty} (actual : Actual type) := LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem oneElaborated (type : Core.Ty) : TypedLetReturnBodyElaborates (types type) owner
    (LocalTypeInputs.empty.bindFresh owner "seed" type) (chain ["x"] "seed") (.letE (.var 0) (.var 0)) type :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem oneCompleted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (seedInputs actual).runTypedLetReturnBody? (types type) owner 4 (chain ["x"] "seed") store = some (type, .done actual.val store) :=
  LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨_, (oneElaborated type).complete, rfl⟩
theorem actual_cells_and_captured_closures_replay_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (seedInputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnBody? (types (.cell .word)) owner 4 (chain ["x"] "seed") replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (seedInputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnBody?
      (types (.function .bool .word)) owner 4 (chain ["x"] "seed") replacement = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) :=
  ⟨(LocalInputs.runTypedLetReturnBody?_done_store_iff _ _ owner _ _ first replacement _ _).mp (oneCompleted _ first),
    (LocalInputs.runTypedLetReturnBody?_done_store_iff _ _ owner _ _ first replacement _ _).mp (oneCompleted _ first)⟩

theorem unknown_annotations_replay_raw_but_fail_whole_checking_in_every_store
    {type : Core.Ty} (actual : Actual type) (first replacement : Core.Store) (fuel : Nat) :
    TypedLetReturnBodyEvaluatesWithCost owner seedTable (seedEnv actual.val) replacement (chain ["x"] "seed") actual.val replacement 4 ∧
    (seedInputs actual).runTypedLetReturnBody? [] owner fuel (chain ["x"] "seed") first = none ∧
    (seedInputs actual).runTypedLetReturnBody? [] owner fuel (chain ["x"] "seed") replacement = none := by
  have rejected : (seedInputs actual).checkTypedLetReturnBody? [] owner (chain ["x"] "seed") = none := by
    simp [LocalInputs.checkTypedLetReturnBody?, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation, TypeNameTable.lookup?]
  exact ⟨(chainCost ["x"] "seed" seedTable (seedEnv actual.val) actual.val first (.identifier .head .head)).change_store replacement,
    LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected, LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr rejected⟩

theorem old_tree_shapes_keep_the_same_store_observation_contract
    (actual : LocalInputs) (typeNames : TypeNameTable) (fuel : Nat) (condition : Syntax.Expr) (yes no : Syntax.Block)
    (first replacement : Core.Store) (type : Core.Ty) (value : Core.Value) :
    (actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ first = some (type, .done value first) ↔
      actual.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ replacement = some (type, .done value replacement)) := by
  rw [actual.runTypedLetReturnBody?_conditional]
  exact actual.runTerminalReturnTree?_done_store_iff fuel _ first replacement type value

theorem a_core_load_preserves_each_store_but_cannot_replay_its_original_value_at_another_store
    (left right : Core.Word) (different : left ≠ right) :
    (∀ (before after : Core.Store) (value : Core.Value),
      Core.Evaluates [.cellRef .word 0] before (.loadCell (.var 0)) value after → after = before) ∧
    Core.Evaluates [.cellRef .word 0] [.word left] (.loadCell (.var 0)) (.word left) [.word left] ∧
    Core.Evaluates [.cellRef .word 0] [.word right] (.loadCell (.var 0)) (.word right) [.word right] ∧
    ¬ Core.Evaluates [.cellRef .word 0] [.word right] (.loadCell (.var 0)) (.word left) [.word right] := by
  refine ⟨?_, .loadCell (.var rfl) rfl, .loadCell (.var rfl) rfl, ?_⟩
  · intro before after value evaluation
    cases evaluation with
    | loadCell reference _ => cases reference; rfl
  · intro replay
    have same := (Core.evaluation_deterministic replay (Core.Evaluates.loadCell (.var rfl) rfl)).1
    exact different (Core.Value.word.inj same)

theorem pending_core_loads_can_fault_or_exhaust_at_zero_fuel_depending_on_the_store (word : Core.Word) :
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ ∧
    Core.runStateful 1 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ = .done (.word word) [.word word] ∧
    Core.runStateful 4 ⟨.eval (.letE (.var 0) (.var 0)) [.cellRef .word 0], [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ := ⟨rfl, rfl, rfl, rfl⟩

end Tests.FrontendTypedLetReturnBodyStore
