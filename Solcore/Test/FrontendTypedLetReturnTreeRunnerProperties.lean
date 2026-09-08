import Solcore.Frontend.TypedLetReturnTreeFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeResumptionProperties
import Solcore.Frontend.TypedLetReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties

/-! Original trees have independent costs and real resumable states.
Static provenance, actual typed values and whole acceptance remain separate. -/
set_option autoImplicit false
namespace Tests.FrontendTypedLetReturnTreeRunner
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeRunner", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-tree-runner.sol"⟩, 21, 5⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation (name : String := "Payload") : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def returned (value : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some value)⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) (typeName : String := "Payload") : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (annotation typeName)) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned (ref previous)
  | name :: rest, previous => binding name (ref previous) (branch guard (tree rest name) (returned (ref name)))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .letE (.var 0) (.ifE guardCore (core depth) (.var 0))
private def inputs (type : Core.Ty) : LocalTypeInputs := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def env (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private theorem guardCost (names : LocalNameTable) (values : Resolved.Environment) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names values store guard (.bool true) store 5 :=
  .equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)
private theorem counted (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner namesTable values store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have arithmetic : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [arithmetic, tree, binding, branch] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (guardCost _ _ store) (ih name _ _ (.identifier .head .head)))
private theorem elaborated (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (tree names previous) (core names.length) type := by
  induction names generalizing previous initial resolved with
  | nil =>
    simp only [tree, List.length_nil, core]
    exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
    have parts := List.nodup_cons.mp distinct
    simp only [tree, List.length_cons, core, binding]
    apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩) (annotation := annotation)
      (.named .head) (fresh name (by simp)) resolution lowered typed
    apply TypedLetReturnTreeElaborates.conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
      (.binary .word .word) (.binary .word .word)
    · apply ih name (initial.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .single (.expression (.identifier .head) (.var .head) (.var .head))
private theorem seedElab (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (inputs type) (tree names "seed") (core names.length) type := by
  apply elaborated names "seed" type (inputs type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem seedCost (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) :=
  counted names "seed" table (env value) value store (.identifier .head .head)

private theorem treeBound (names : List String) (previous : String) :
    typedLetReturnTreeFuelBound (tree names previous) = 10 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [tree, returned, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
    simp only [tree, binding, branch, typedLetReturnTreeFuelBound, returned, ref, localExpressionFuelBound,
      returnBodyFuelBound, guard, zero, List.length_cons]
    rw [ih name]
    omega

theorem arbitrary_original_depth_has_independent_provenance_cost_and_source_bound
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeElaborates (types type) owner (inputs type) (tree names "seed") (core names.length) type ∧
    TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store (10 * names.length + 1) ∧
    typedLetReturnTreeFuelBound (tree names "seed") = 10 * names.length + 1 :=
  ⟨seedElab names type distinct fresh, seedCost names value store, treeBound names "seed"⟩

theorem known_cost_and_aligned_ids_determine_every_fuel_without_runtime_typing
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names)
    (value : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .done value store ↔ 10 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .outOfFuel checkpoint) ↔ fuel < 10 * names.length + 1) ∧
    (Core.runStateful fuel (Core.State.initial (core names.length) [value] store) = .done value store ↔
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner table (env value) store (tree names "seed") value store cost ∧ cost ≤ fuel) :=
  ⟨(seedCost names value store).checked_runStateful_done_iff (seedElab names type distinct fresh).complete rfl,
    (seedCost names value store).checked_runStateful_outOfFuel_iff (seedElab names type distinct fresh).complete rfl,
    elaborateTypedLetReturnTree?_run_done_iff_cost (environment := env value) (seedElab names type distinct fresh).complete rfl⟩

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def pairInputs (type : Core.Ty) : LocalTypeInputs := ⟨[⟨"seed", id 1, type⟩, ⟨"c", id 0, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def actualInputs {type : Core.Ty} (choice : Bool) (actual : Actual type) : LocalInputs :=
  ⟨[⟨"seed", id 1, type, actual.val, actual.property⟩, ⟨"c", id 0, .bool, .bool choice, .bool⟩], by change [id 1, id 0].Nodup; decide⟩
private def pairEnv (choice : Bool) (value : Core.Value) : Resolved.Environment := [(id 1, value), (id 0, .bool choice)]
private def thenBody := binding "x" (ref "seed") (returned (ref "x"))
private def body := branch (ref "c") thenBody (returned (ref "seed"))
private def bodyCore : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)
private def required (choice : Bool) : Nat := if choice then 7 else 4
private theorem bodyElab (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (pairInputs type) body bodyCore type :=
  .conditional (.identifier (.tail (by change "seed" ≠ "c"; decide) .head))
    (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))
    (.binding (.named .head) (by change "x" ∉ ["seed", "c"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (choice : Bool) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (pairInputs .unit).names (pairEnv choice value) store body value store (required choice) := by
  have c : LocalExpressionEvaluatesWithCost (pairInputs .unit).names (pairEnv choice value) store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have seed : LocalExpressionEvaluatesWithCost (pairInputs .unit).names (pairEnv choice value) store (ref "seed") value store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse c (.single (.expression seed))
  · exact .ifTrue c (.binding seed (.single (.expression (.identifier .head .head))))
private theorem bodyBound : typedLetReturnTreeFuelBound body = 7 := by
  simp [body, branch, thenBody, binding, returned, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
private theorem runExact {type : Core.Ty} (choice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat) (result : Core.StatefulRunResult) :
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, result) ↔
      Core.runStateful fuel (Core.State.initial bodyCore [actual.val, .bool choice] store) = result := by
  constructor
  · intro observed
    obtain ⟨candidate, checked, ran⟩ := LocalInputs.runTypedLetReturnTree?_eq_some_iff.mp observed
    change elaborateTypedLetReturnTree? (types type) owner (pairInputs type) body = _ at checked
    rw [(bodyElab type).complete] at checked
    cases checked
    exact ran
  · intro ran
    exact LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨bodyCore, (bodyElab type).complete, ran⟩

theorem branch_local_let_is_new_acceptance_and_the_old_bound_is_insufficient (type : Core.Ty) :
    TypedLetReturnTreeElaborates (types type) owner (pairInputs type) body bodyCore type ∧
    typedLetReturnTreeFuelBound body = 7 ∧ typedLetReturnBodyFuelBound body = 4 ∧
    elaborateTypedLetReturnBody? (types type) owner (pairInputs type) body = none := by
  refine ⟨bodyElab type, bodyBound, ?_, ?_⟩
  · simp [body, branch, thenBody, binding, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  · have c : elaborateLocalExpression? (pairInputs type).names (pairInputs type).context (ref "c") = some (.var 1, .bool) :=
      elaborateLocalExpression?_complete (.identifier (.tail (by change "seed" ≠ "c"; decide) .head))
        (.var (.tail (by change id 1 ≠ id 0; decide) .head)) (.var (.tail (by change id 1 ≠ id 0; decide) .head))
    simp [body, branch, thenBody, binding, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?, c]

theorem actual_typed_branch_thresholds_are_exact_at_every_fuel {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    ((actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, .done actual.val store) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  refine ⟨(runExact choice actual store fuel _).trans ((bodyCost choice actual.val store).checked_runStateful_done_iff (inputs := pairInputs type) (bodyElab type).complete rfl), ?_⟩
  simp only [runExact]
  exact (bodyCost choice actual.val store).checked_runStateful_outOfFuel_iff (inputs := pairInputs type) (fuel := fuel) (bodyElab type).complete rfl

theorem wrapper_characterizations_retain_whole_typing_and_exclude_faults {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (store finalStore : Core.Store) (value : Core.Value)
    (fuel : Nat) (error : Core.MachineFault) (state : Core.State) :
    ((actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, .done value finalStore) ↔
      TypedLetReturnTreeHasType (types type) owner (actualInputs choice actual).toTypeInputs body type ∧
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner (pairInputs type).names (pairEnv choice actual.val) store body value finalStore cost ∧ cost ≤ fuel) ∧
    ((∃ checkpoint, (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store = some (type, .outOfFuel checkpoint)) ↔
      TypedLetReturnTreeHasType (types type) owner (actualInputs choice actual).toTypeInputs body type ∧
      ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner (pairInputs type).names (pairEnv choice actual.val) store body value store cost ∧ fuel < cost) ∧
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel body store ≠ some (type, .fault error state) :=
  ⟨LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost, LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost,
    (actualInputs choice actual).runTypedLetReturnTree?_never_faults (types type) owner body fuel store type error state⟩

theorem both_bound_interfaces_use_actual_typed_values_and_the_original_store {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (store : Core.Store) :
    required choice ≤ typedLetReturnTreeFuelBound body ∧ Core.ValueHasType actual.val type ∧
    (∃ value, Core.ValueHasType value type ∧ Core.runStateful 7 (Core.State.initial bodyCore [actual.val, .bool choice] store) = .done value store) ∧
    (∃ value, Core.ValueHasType value type ∧ (actualInputs choice actual).runTypedLetReturnTree? (types type) owner 7 body store = some (type, .done value store)) ∧
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner 7 body store = some (type, .done actual.val store) := by
  have typing : TypedLetReturnTreeHasType (types type) owner (actualInputs choice actual).toTypeInputs body type := (bodyElab type).hasType
  obtain ⟨value, cost, evaluated, valueTyped, _⟩ := LocalInputs.typedLetReturnTree_typed_cost_execution typing store
  have same := evaluated.deterministic (bodyCost choice actual.val store)
  exact ⟨(bodyCost choice actual.val store).cost_le_fuelBound, same.1 ▸ valueTyped,
    elaborateTypedLetReturnTree?_run_done_of_fuelBound (environment := pairEnv choice actual.val) (bodyElab type).complete rfl
      (.cons actual.property (.cons .bool .nil)) store 7 (by simp only [bodyBound, Nat.le_refl]),
    LocalInputs.runTypedLetReturnTree?_done_of_fuelBound typing store 7 (by simp only [bodyBound, Nat.le_refl]),
    (actual_typed_branch_thresholds_are_exact_at_every_fuel choice actual store 7).1.mpr (by cases choice <;> decide)⟩

private def ifCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) [value, .bool true]], store⟩
private def letCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 0) [value, .bool true]], store⟩
theorem genuine_conditional_initializer_and_tail_states_preserve_every_frame {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner 2 body store = some (type, .outOfFuel (ifCheckpoint actual.val store)) ∧
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner 4 body store =
      some (type, .outOfFuel ⟨.eval (.var 0) [actual.val, .bool true], (letCheckpoint actual.val store).continuation, store⟩) ∧
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner 5 body store = some (type, .outOfFuel (letCheckpoint actual.val store)) ∧
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner 6 body store =
      some (type, .outOfFuel ⟨.eval (.var 0) [actual.val, actual.val, .bool true], [], store⟩) ∧
    5 < 7 ∧ Core.Steps 2 (letCheckpoint actual.val store) (Core.State.final actual.val store) := by
  have real : Core.runStateful 5 (Core.State.initial bodyCore [actual.val, .bool true] store) = .outOfFuel (letCheckpoint actual.val store) := rfl
  exact ⟨(runExact true actual store 2 _).mpr rfl, (runExact true actual store 4 _).mpr rfl,
    (runExact true actual store 5 _).mpr real, (runExact true actual store 6 _).mpr rfl,
    (bodyCost true actual.val store).checked_residual_of_outOfFuel (inputs := pairInputs type) (bodyElab type).complete rfl real⟩

theorem full_resumption_and_multiple_chunks_differ_from_restarting_or_dropping_frames {type : Core.Ty}
    (actual : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 1 (ifCheckpoint actual.val store) = .outOfFuel ⟨.eval (.letE (.var 0) (.var 0)) [actual.val, .bool true], [], store⟩ ∧
    Core.runStateful 2 ⟨.eval (.letE (.var 0) (.var 0)) [actual.val, .bool true], [], store⟩ = .outOfFuel (letCheckpoint actual.val store) ∧
    Core.runStateful 3 (ifCheckpoint actual.val store) = .outOfFuel (letCheckpoint actual.val store) ∧
    Core.runStateful 2 (letCheckpoint actual.val store) = .done actual.val store ∧
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner (2 + additional) body store = some (type, Core.runStateful additional (ifCheckpoint actual.val store)) ∧
    (actualInputs true actual).runTypedLetReturnTree? (types type) owner (5 + additional) body store = some (type, Core.runStateful additional (letCheckpoint actual.val store)) ∧
    Core.runStateful 0 ⟨.ret actual.val, [], store⟩ = .done actual.val store ∧
    Core.runStateful 0 (letCheckpoint actual.val store) = .outOfFuel (letCheckpoint actual.val store) ∧
    Core.runStateful 2 (Core.State.initial bodyCore [actual.val, .bool true] store) ≠ .done actual.val store := by
  have checkpoints := genuine_conditional_initializer_and_tail_states_preserve_every_frame actual store
  exact ⟨rfl, rfl, rfl, rfl, LocalInputs.runTypedLetReturnTree?_resume checkpoints.1 additional,
    LocalInputs.runTypedLetReturnTree?_resume checkpoints.2.2.1 additional, rfl, rfl, by intro impossible; cases impossible⟩

theorem actual_cells_and_closures_pass_through_the_new_branch_without_access_or_calls
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    (actualInputs true (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnTree? (types (.cell .word)) owner 7 body store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    (actualInputs true (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnTree?
      (types (.function .bool .word)) owner 7 body store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(runExact true _ store 7 _).mpr rfl, (runExact true _ store 7 _).mpr rfl⟩

theorem positive_bounds_and_raw_paths_do_not_replace_whole_acceptance {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    TypedLetReturnTreeEvaluatesWithCost owner (pairInputs type).names (pairEnv choice actual.val) store body actual.val store (required choice) ∧
    typedLetReturnTreeFuelBound body = 7 ∧ (actualInputs choice actual).runTypedLetReturnTree? [] owner fuel body store = none ∧
    typedLetReturnTreeFuelBound ⟨span, []⟩ = 0 ∧
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel ⟨span, []⟩ store = none := by
  refine ⟨bodyCost choice actual.val store, bodyBound, LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr ?_, ?_,
    LocalInputs.runTypedLetReturnTree?_eq_none_iff.mpr ?_⟩
  · apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ yes _ =>
      cases yes with
      | single child => cases child
      | binding meaning _ _ _ => cases meaning with | named found => cases found
  · simp [typedLetReturnTreeFuelBound]
  · simp [LocalInputs.checkTypedLetReturnTree?, elaborateTypedLetReturnTree?]

theorem accepted_aligned_untyped_guards_can_fault_before_or_at_the_full_bound (word : Core.Word) (store : Core.Store) :
    elaborateTypedLetReturnTree? (types .word) owner (pairInputs .word) body = some (bodyCore, .word) ∧
    Resolved.LocalScope.ids ([(id 1, .word word), (id 0, .word word)] : Resolved.Environment) = (pairInputs .word).context.ids ∧
    typedLetReturnTreeFuelBound body = 7 ∧
    Core.runStateful 2 (Core.State.initial bodyCore [.word word, .word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) [.word word, .word word]], store⟩ ∧
    Core.runStateful 7 (Core.State.initial bodyCore [.word word, .word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) [.word word, .word word]], store⟩ :=
  ⟨(bodyElab .word).complete, rfl, bodyBound, rfl, rfl⟩

theorem old_successes_preserve_full_results_but_only_singletons_preserve_all_options {type : Core.Ty}
    (choice : Bool) (actual : Actual type) (fuel : Nat) (store : Core.Store) (value : Option Syntax.Expr) :
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel ⟨span, [⟨span, .returnStmt value⟩]⟩ store =
      (actualInputs choice actual).runReturnBody? fuel ⟨span, [⟨span, .returnStmt value⟩]⟩ store ∧
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel (returned (ref "seed")) store =
      some (type, Core.runStateful fuel (Core.State.initial (.var 0) [actual.val, .bool choice] store)) ∧
    (actualInputs choice actual).runTypedLetReturnTree? (types type) owner fuel thenBody store =
      some (type, Core.runStateful fuel (Core.State.initial (.letE (.var 0) (.var 0)) [actual.val, .bool choice] store)) := by
  have oldTree : TerminalReturnTreeElaborates (actualInputs choice actual).names (actualInputs choice actual).context
      (returned (ref "seed")) (.var 0) type := .single (.expression (.identifier .head) (.var .head) (.var .head))
  have oldBody : TypedLetReturnBodyElaborates (types type) owner (actualInputs choice actual).toTypeInputs thenBody (.letE (.var 0) (.var 0)) type :=
    .binding (.named .head) (by change "x" ∉ ["seed", "c"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  refine ⟨(actualInputs choice actual).runTypedLetReturnTree?_single (types type) owner fuel value span span store,
    LocalInputs.runTypedLetReturnTree?_some_of_terminalReturnTree (types type) owner ?_,
    LocalInputs.runTypedLetReturnTree?_some_of_typedLetReturnBody ?_⟩
  · simp [LocalInputs.runTerminalReturnTree?, LocalInputs.checkTerminalReturnTree?, oldTree.complete]
    rfl
  · simp [LocalInputs.runTypedLetReturnBody?, LocalInputs.checkTypedLetReturnBody?, oldBody.complete]
    rfl

end Tests.FrontendTypedLetReturnTreeRunner
