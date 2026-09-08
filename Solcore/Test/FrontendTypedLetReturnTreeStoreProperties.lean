import Solcore.Frontend.TypedLetReturnTreeStoreProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeProperties

/-! Replay retains values and costs but not the store fields of full results.
Pending loads delimit the claim; they are not part of the source body. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeStore
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeStore", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-tree-store.sol"⟩, 37, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name previous : String) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some (ref previous))⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name previous (branch guard (tree rest name) (returned name))
private def seedTable : LocalNameTable := [("seed", id 0)]
private def unaligned (value decoy : Core.Value) : Resolved.Environment := [(id 9, decoy), (id 0, value)]
private theorem treeCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have arithmetic : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [arithmetic, tree, binding, branch, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem independent (names : List String) (value decoy : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) store (tree names "seed") value store (10 * names.length + 1) :=
  treeCost names "seed" seedTable _ value store (.identifier .head (.tail (by decide) .head))

theorem arbitrary_raw_lists_and_unaligned_values_replay_without_name_or_type_assumptions
    (names : List String) (value decoy : Core.Value) (first replacement : Core.Store) :
    (unaligned value decoy).ids ≠ seedTable.map Prod.snd ∧
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) first (tree names "seed") value first ∧
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement ∧
    TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement (10 * names.length + 1) := by
  have original := independent names value decoy first
  exact ⟨(by intro same; cases same), original.erase, original.erase.change_store replacement, original.change_store replacement⟩

theorem both_replay_equivalences_retain_the_original_final_store_equality
    (names : List String) (actual decoy value : Core.Value) (first finalStore replacement : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluates owner seedTable (unaligned actual decoy) first (tree names "seed") value finalStore ↔
      finalStore = first ∧ TypedLetReturnTreeEvaluates owner seedTable (unaligned actual decoy) replacement (tree names "seed") value replacement) ∧
    (TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned actual decoy) first (tree names "seed") value finalStore cost ↔
      finalStore = first ∧ TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned actual decoy) replacement (tree names "seed") value replacement cost) :=
  ⟨typedLetReturnTreeEvaluates_store_iff, typedLetReturnTreeEvaluatesWithCost_store_iff⟩

theorem a_replacement_path_cannot_validate_an_arbitrary_original_final_store
    (names : List String) (value decoy : Core.Value) (first replacement : Core.Store) (different : replacement ≠ first) :
    TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) replacement (tree names "seed") value replacement ∧
    ¬ TypedLetReturnTreeEvaluates owner seedTable (unaligned value decoy) first (tree names "seed") value replacement ∧
    ¬ TypedLetReturnTreeEvaluatesWithCost owner seedTable (unaligned value decoy) first (tree names "seed") value replacement (10 * names.length + 1) := by
  refine ⟨(independent names value decoy replacement).erase, ?_, ?_⟩
  · intro wrong
    exact different ((typedLetReturnTreeEvaluates_store_iff (replacement := replacement)).mp wrong).1
  · intro wrong
    exact different ((typedLetReturnTreeEvaluatesWithCost_store_iff (replacement := replacement)).mp wrong).1

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def staticInputs (type : Core.Ty) : LocalTypeInputs := ⟨[⟨"seed", id 1, type⟩, ⟨"c", id 0, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def inputs {type : Core.Ty} (choice : Bool) (actual : Actual type) : LocalInputs :=
  ⟨[⟨"seed", id 1, type, actual.val, actual.property⟩, ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def environment (choice : Bool) (value : Core.Value) : Resolved.Environment := [(id 1, value), (id 0, .bool choice)]
private def thenBody := binding "unused" "seed" (returned "seed")
private def body := branch (ref "c") thenBody (returned "seed")
private def core : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 1)) (.var 0)
private def required (choice : Bool) : Nat := if choice then 7 else 4
private theorem elaborated (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (staticInputs type) body core type :=
  .conditional (.identifier (.tail (by change "seed" ≠ "c"; decide) .head))
    (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))
    (.binding (.named .head) (by change "unused" ∉ ["seed", "c"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier (.tail (by change "unused" ≠ "seed"; decide) .head))
        (.var (.tail (by change id 2 ≠ id 1; decide) .head)) (.var (.tail (by change id 2 ≠ id 1; decide) .head)))))
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem costed (choice : Bool) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs .unit).names (environment choice value) store body value store (required choice) := by
  have c : LocalExpressionEvaluatesWithCost (staticInputs .unit).names (environment choice value) store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have seed : LocalExpressionEvaluatesWithCost (staticInputs .unit).names (environment choice value) store (ref "seed") value store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse c (.single (.expression seed))
  · have tailSeed : LocalExpressionEvaluatesWithCost (("unused", id 2) :: (staticInputs .unit).names)
        ((id 2, value) :: environment true value) store (ref "seed") value store 1 :=
      .identifier (.tail (by decide) .head) (.tail (by decide) .head)
    exact .ifTrue c (.binding (owner := owner) (name := ⟨span, "unused"⟩) (annotation := annotation) seed (.single (.expression tailSeed)))
private theorem runExact {type : Core.Ty} (choice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (result : Core.StatefulRunResult) (ran : Core.runStateful fuel (Core.State.initial core [actual.val, .bool choice] store) = result) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, result) :=
  LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨core, (elaborated type).complete, ran⟩
private theorem completed {type : Core.Ty} (choice : Bool) (actual : Actual type) (store : Core.Store) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body store = some (type, .done actual.val store) :=
  runExact choice actual store _ _ (by cases choice <;> rfl)

theorem unused_work_and_asymmetric_selected_costs_replay_at_their_own_stores {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) first body actual.val first (required choice) ∧
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) replacement body actual.val replacement (required choice) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement = some (type, .done actual.val replacement) :=
  ⟨costed choice actual.val first, (costed choice actual.val first).change_store replacement,
    ((inputs choice actual).runTypedLetReturnTree?_done_store_iff (types type) owner _ body first replacement type actual.val).mp (completed choice actual first)⟩

theorem every_fuel_preserves_own_store_observations_and_the_independent_threshold {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (value : Core.Value) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .done value first) ↔
      (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement = some (type, .done value replacement)) ∧
    ((∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement = some (type, .outOfFuel checkpoint)) ∧
    ((inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body first = some (type, .done actual.val first) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice actual).runTypedLetReturnTree? (types type) owner fuel body replacement =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  refine ⟨(inputs choice actual).runTypedLetReturnTree?_done_store_iff (types type) owner fuel body first replacement type value,
    (inputs choice actual).runTypedLetReturnTree?_outOfFuel_store_iff (types type) owner fuel body first replacement type, ?_⟩
  have checked : (inputs choice actual).checkTypedLetReturnTree? (types type) owner body = some (core, type) := (elaborated type).complete
  simp only [LocalInputs.runTypedLetReturnTree?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact ⟨(costed choice actual.val first).checked_runStateful_done_iff (inputs := staticInputs type) (elaborated type).complete rfl,
    ((costed choice actual.val first).change_store replacement).checked_runStateful_outOfFuel_iff (inputs := staticInputs type) (elaborated type).complete rfl⟩

theorem equal_completed_values_do_not_make_full_results_equal {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) (different : first ≠ replacement) :
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body first = some (type, .done actual.val first) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement = some (type, .done actual.val replacement) ∧
    (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body first ≠
      (inputs choice actual).runTypedLetReturnTree? (types type) owner (required choice) body replacement := by
  refine ⟨completed choice actual first, completed choice actual replacement, ?_⟩
  rw [completed, completed]
  intro same
  cases same
  exact different rfl

private def ifCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 1)) (.var 0) [value, .bool true]], store⟩
private def initCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 1) [value, .bool true]], store⟩
private def tailCheckpoint (value : Core.Value) (store : Core.Store) : Core.State := ⟨.eval (.var 1) [value, value, .bool true], [], store⟩
private theorem ifExhausted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body store = some (type, .outOfFuel (ifCheckpoint actual.val store)) := runExact true actual store _ _ rfl
private theorem initExhausted {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body store = some (type, .outOfFuel (initCheckpoint actual.val store)) := runExact true actual store _ _ rfl

theorem distinct_stores_are_retained_in_conditional_initializer_and_tail_states {type : Core.Ty}
    (actual : Actual type) (first replacement : Core.Store) (different : first ≠ replacement) :
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body first = some (type, .outOfFuel (ifCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 2 body replacement = some (type, .outOfFuel (ifCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body first = some (type, .outOfFuel (initCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 5 body replacement = some (type, .outOfFuel (initCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 6 body first = some (type, .outOfFuel (tailCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner 6 body replacement = some (type, .outOfFuel (tailCheckpoint actual.val replacement)) ∧
    ifCheckpoint actual.val first ≠ ifCheckpoint actual.val replacement ∧ initCheckpoint actual.val first ≠ initCheckpoint actual.val replacement ∧
    tailCheckpoint actual.val first ≠ tailCheckpoint actual.val replacement := by
  refine ⟨ifExhausted actual first, ifExhausted actual replacement, initExhausted actual first, initExhausted actual replacement,
    runExact true actual first _ _ rfl, runExact true actual replacement _ _ rfl, ?_, ?_, ?_⟩ <;>
    intro same <;> exact different (congrArg Core.State.store same)

theorem each_genuine_checkpoint_resumes_its_own_store_for_all_additional_fuel {type : Core.Ty}
    (actual : Actual type) (first replacement : Core.Store) (additional : Nat) :
    Core.runStateful 3 (ifCheckpoint actual.val first) = .outOfFuel (initCheckpoint actual.val first) ∧
    Core.runStateful 1 (initCheckpoint actual.val replacement) = .outOfFuel (tailCheckpoint actual.val replacement) ∧
    Core.runStateful 2 (initCheckpoint actual.val replacement) = .done actual.val replacement ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (2 + additional) body first = some (type, Core.runStateful additional (ifCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (2 + additional) body replacement = some (type, Core.runStateful additional (ifCheckpoint actual.val replacement)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (5 + additional) body first = some (type, Core.runStateful additional (initCheckpoint actual.val first)) ∧
    (inputs true actual).runTypedLetReturnTree? (types type) owner (5 + additional) body replacement = some (type, Core.runStateful additional (initCheckpoint actual.val replacement)) :=
  ⟨rfl, rfl, rfl, LocalInputs.runTypedLetReturnTree?_resume (ifExhausted actual first) additional,
    LocalInputs.runTypedLetReturnTree?_resume (ifExhausted actual replacement) additional,
    LocalInputs.runTypedLetReturnTree?_resume (initExhausted actual first) additional,
    LocalInputs.runTypedLetReturnTree?_resume (initExhausted actual replacement) additional⟩

theorem opaque_cell_references_and_closures_replay_without_accessing_either_store
    (location : Core.Location) (word : Core.Word) (first replacement : Core.Store) :
    (inputs true (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnTree? (types (.cell .word)) owner 7 body replacement =
      some (.cell .word, .done (.cellRef .word location) replacement) ∧
    (inputs true (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnTree?
      (types (.function .bool .word)) owner 7 body replacement = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) replacement) :=
  ⟨(LocalInputs.runTypedLetReturnTree?_done_store_iff _ _ owner _ _ first replacement _ _).mp (completed true _ first),
    (LocalInputs.runTypedLetReturnTree?_done_store_iff _ _ owner _ _ first replacement _ _).mp (completed true _ first)⟩

theorem unknown_annotations_replay_selected_paths_but_fail_whole_checking_in_both_stores {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (first replacement : Core.Store) (fuel : Nat) :
    TypedLetReturnTreeEvaluatesWithCost owner (staticInputs type).names (environment choice actual.val) replacement body actual.val replacement (required choice) ∧
    (inputs choice actual).runTypedLetReturnTree? [] owner fuel body first = none ∧
    (inputs choice actual).runTypedLetReturnTree? [] owner fuel body replacement = none := by
  have rejected : (inputs choice actual).checkTypedLetReturnTree? [] owner body = none := by
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ yes _ =>
      cases yes with
      | single child => cases child
      | binding meaning _ _ _ => cases meaning with | named found => cases found
  exact ⟨(costed choice actual.val first).change_store replacement,
    LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr rejected, LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr rejected⟩

theorem pending_loads_after_the_same_source_body_can_observe_different_stored_values
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    (∀ (before after : Core.Store) (value : Core.Value), Core.Evaluates [.cellRef .word 0] before (.loadCell (.var 0)) value after → after = before) ∧
    Core.Steps 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], store⟩ ⟨.ret (.cellRef .word 0), [.loadCellApply], store⟩ ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word left]⟩ = .done (.word left) [.word left] ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word right]⟩ = .done (.word right) [.word right] ∧
    Core.runStateful 8 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word right]⟩ ≠ .done (.word left) [.word right] := by
  refine ⟨?_, (costed true (.cellRef .word 0) store).checked_toStepsWithContinuation (inputs := staticInputs (.cell .word))
    (elaborated (.cell .word)).complete rfl _, rfl, rfl, ?_⟩
  · intro before after value evaluation
    cases evaluation with
    | loadCell reference _ => cases reference; rfl
  · intro same
    exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj same).1).symm

theorem zero_fuel_load_faults_and_exhaustion_are_store_dependent_even_after_the_exact_body_path (word : Core.Word) :
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 0 ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ ∧
    Core.runStateful 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], []⟩ =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ ∧
    Core.runStateful 7 ⟨.eval core [.cellRef .word 0, .bool true], [.loadCellApply], [.word word]⟩ =
      .outOfFuel ⟨.ret (.cellRef .word 0), [.loadCellApply], [.word word]⟩ := ⟨rfl, rfl, rfl, rfl⟩

end Tests.FrontendTypedLetReturnTreeStore
