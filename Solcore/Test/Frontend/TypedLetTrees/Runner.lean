import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.RuntimeFunction

/-!
# Typed let tree runner tests

The runner on typed let return trees.
-/

section
-- leanmerge: from Solcore.Test.FrontendTypedLetReturnTreeRunnerProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypedLetReturnTreeRunner
/-! Actual parsed parameters and independent source scripts meet the new body
runner. All checkpoints come from real execution; expectations are not inferred
from runner output. Recursive entries use this body; old body adapters and old bounds remain unchanged. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetTreeRunner", by decide⟩], by decide⟩⟩, 17⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def stores : List Core.Store := [[.word (word 101), .cellRef .word 31],
  [.closure .bool .bool (.var 0) [], .bool false, .word Core.Word.maximum]]
private def actual (content : String) (arguments : List TypedRuntimeArgument) : IO (Syntax.FunctionDecl × LocalInputs × List TypedRuntimeArgument) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-let-tree-runner.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"function did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "diagnosed or incomplete source"
  match bound : bindRuntimeParameters? types owner source.value.signature.parameters.elements arguments with
  | none => throw (IO.userError "actual typed arguments did not bind")
  | some inputs =>
      have _ := (bindRuntimeParameters?_sound bound).erase_values.complete
      let names := source.value.signature.parameters.elements.filterMap fun parameter => match parameter.value with
        | .typed none name _ => some name.value | _ => none
      assertTrue (decide (inputs.environment.values = arguments.reverse.map (·.value) ∧
        inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        (declareRuntimeParameters? types owner source.value.signature.parameters.elements).map (fun i => (i.names, i.context.values)) =
          some (inputs.names, inputs.context.values))) "original names, IDs, actual values or static factorization changed"
      return (source, inputs, arguments)
private structure Expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def reference (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "script expected an existing name")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "script expected an actual value")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "script expected a reference")
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table environment store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (valueAt ▸ child.costed)⟩
      | _ => throw (IO.userError "word-not expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table environment store left
      let second ← reference table environment store right
      match leftAt : first.value, rightAt : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (leftAt ▸ first.costed) (rightAt ▸ second.costed)⟩
      | _, _ => throw (IO.userError "ordered subtraction expected Words")
  | _ => throw (IO.userError "expression outside fixture script")
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store source value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Block) (choices : List Bool) : IO (Certificate table environment store source) := do
  match sourceAt : source with
  | ⟨blockSpan, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let child ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, child.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by
        rw [sourceAt]; cases annotation <;> first | exact .binding child.costed tail.costed | exact .inferred child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected-branch script")
      let guard ← reference table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let child ← certify table environment store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
        | false =>
            let child ← certify table environment store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) child.costed⟩
      else throw (IO.userError "script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after bare return"
      return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued after return"
      let child ← expression table environment store operand
      return ⟨child.value, child.cost, by rw [sourceAt]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "script cannot describe original source")
termination_by sizeOf source
private def oldShapes (inputs : LocalInputs) (body : Syntax.Block) (fuel : Nat) (store : Core.Store) : IO Unit := do
  let run := inputs.runTypedLetReturnTree? types owner fuel body store
  match body.value with
  | [⟨returnSpan, .returnStmt returned⟩] =>
      have _ := inputs.runTypedLetReturnTree?_single types owner fuel returned body.span returnSpan store
      assertTrue (decide (run = inputs.runReturnBody? fuel body store)) "singleton full Option result changed"
  | _ => pure ()
  match accepted : inputs.runTerminalReturnTree? fuel body store with
  | none => pure ()
  | some result =>
      have _ := LocalInputs.runTypedLetReturnTree?_some_of_terminalReturnTree types owner accepted
      assertTrue (decide (run = some result)) "old terminal-tree success changed complete same-fuel result"
  match accepted : inputs.runTypedLetReturnBody? types owner fuel body store with
  | none => pure ()
  | some result =>
      have _ := LocalInputs.runTypedLetReturnTree?_some_of_typedLetReturnBody accepted
      assertTrue (decide (run = some result)) "old prefix success changed complete same-fuel result"
private def checked (source : Syntax.FunctionDecl) (inputs : LocalInputs) (arguments : List TypedRuntimeArgument) (choices : List Bool)
    (core : Core.Expr) (expected : TypedRuntimeArgument) (cost bound : Nat) (branchBindings : Bool := true) : IO Unit := do
  have aligned : inputs.environment.ids = inputs.toTypeInputs.context.ids := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have typed : Core.EnvironmentHasTypes inputs.environment.values inputs.toTypeInputs.context.values := by
    simpa only [LocalInputs.toTypeInputs_context] using inputs.environmentTyped
  for store in stores do
    let certificate ← certify inputs.toTypeInputs.names inputs.environment store source.value.body choices
    assertTrue (decide (certificate.value = expected.value ∧ certificate.cost = cost ∧ typedLetReturnTreeFuelBound source.value.body = bound))
      "independent source value/cost or maximum bound changed"
    match accepted : inputs.checkTypedLetReturnTree? types owner source.value.body with
    | none => throw (IO.userError "whole tree rejected")
    | some (actualCore, type) =>
        assertTrue (decide (actualCore = core ∧ type = expected.type ∧ Core.infer? inputs.context.values core = some type ∧
          interpretRuntimeFunctionHeader? types source.value.signature = some type)) "actual source Core/type/header changed"
        assertTrue (decide ((compileRuntimeFunction? types owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
          some (core, expected.type, inputs.names, inputs.context.values)) && (prepareRuntimeFunction? types owner source arguments).any (fun p =>
            decide (p.core = core ∧ p.returnType = expected.type ∧ p.inputs.names = inputs.names ∧ p.inputs.context.values = inputs.context.values ∧
              p.inputs.environment.values = arguments.reverse.map (·.value)))) "entry changed Core or original actual parameter rows"
        if branchBindings then assertTrue (inputs.checkTypedLetReturnBody? types owner source.value.body).isNone "old prefix adapter broadened"
        let typing := elaborateTypedLetReturnTree?_sound accepted
        have _ := certificate.costed.cost_le_fuelBound
        have _ := certificate.costed.checked_runStateful_done_iff (fuel := cost) accepted aligned
        have _ := certificate.costed.checked_runStateful_outOfFuel_iff (fuel := 0) accepted aligned
        have _ := elaborateTypedLetReturnTree?_run_done_iff_cost (initialStore := store) (finalStore := store)
          (value := expected.value) (fuel := cost) accepted aligned
        have _ := LocalInputs.typedLetReturnTree_typed_cost_execution (inputs := inputs) typing store
        have _ := elaborateTypedLetReturnTree?_run_done_of_fuelBound accepted aligned typed store
          (typedLetReturnTreeFuelBound source.value.body) (Nat.le_refl _)
        have _ := LocalInputs.runTypedLetReturnTree?_done_of_fuelBound (inputs := inputs) typing store
          (typedLetReturnTreeFuelBound source.value.body) (Nat.le_refl _)
        let initial := Core.State.initial core inputs.environment.values store
        let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel source.value.body store
        for fuel in List.range (bound + 3) do
          oldShapes inputs source.value.body fuel store
          have _ := LocalInputs.runTypedLetReturnTree?_never_faults inputs types owner source.value.body fuel store type
          assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial) ∧
            runRuntimeFunction? types owner source arguments fuel store = run fuel)) "runner or entry changed Core, original values or complete machine state"
          match outcome : run fuel with
          | some (actualType, .done value finalStore) =>
              have _ := LocalInputs.runTypedLetReturnTree?_done_iff_typed_cost.mp outcome
              assertTrue (decide (cost ≤ fuel ∧ actualType = type ∧ value = expected.value ∧ finalStore = store)) "completion threshold or own value/store changed"
          | some (actualType, .outOfFuel state) =>
              have _ := LocalInputs.runTypedLetReturnTree?_outOfFuel_iff_typed_cost.mp ⟨state, outcome⟩
              assertTrue (decide (fuel < cost ∧ actualType = type ∧ state.store = store)) "exhaustion threshold or own store changed"
          | _ => throw (IO.userError "whole typed runner faulted or disappeared")
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
              have _ : spent < certificate.cost ∧ Core.Steps (certificate.cost - spent) checkpoint (.final certificate.value store) := by
                obtain ⟨_, checkedAt, pathAt⟩ := LocalInputs.runTypedLetReturnTree?_eq_some_iff.mp exhausted
                exact certificate.costed.checked_residual_of_outOfFuel checkedAt aligned pathAt
              assertTrue (decide (Core.runStateful 0 checkpoint = .outOfFuel checkpoint)) "zero fuel changed a genuine checkpoint"
              for remaining in List.range (cost - spent + 3) do
                have _ := LocalInputs.runTypedLetReturnTree?_resume exhausted remaining
                let resumed := Core.runStateful remaining checkpoint
                assertTrue (decide (run (spent + remaining) = some (type, resumed))) "full genuine resumption changed"
                assertTrue (match resumed with
                  | .done value finalStore => decide (cost - spent ≤ remaining ∧ value = expected.value ∧ finalStore = store)
                  | .outOfFuel state => decide (remaining < cost - spent ∧ state.store = store)
                  | _ => false) "residual threshold or original store changed"
              for middle in [0, (cost - spent) / 2, cost - spent - 1] do
                let .outOfFuel second := Core.runStateful middle checkpoint | throw (IO.userError "second genuine checkpoint disappeared")
                for last in [0, cost - spent - middle - 1, cost - spent - middle, cost - spent - middle + 2] do
                  assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last second))) "three genuine chunks changed their complete result"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (type, .done expected.value store))) "restart was mistaken for checkpoint resumption"
          | _ => throw (IO.userError "expected actual exhaustion below independent cost")
private def alternating (remaining level : Nat) : String × Core.Expr :=
  match remaining with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1)
      let recText := s!"let z{level}: Word=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leafText := s!"let z{level}: Word=y;return z{level};"
      let recCore := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let leafCore := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recText ++ "}else{" ++ leafText ++ "}", .ifE (.var (level + 3)) recCore leafCore)
      else ("if(d){" ++ leafText ++ "}else{" ++ recText ++ "}", .ifE (.var (level + 2)) leafCore recCore)

def frontendParsedTypedLetReturnTreeRunnerTests : IO Unit := do
  for depth in [0, 1, 2, 5] do
    let (body, core) := alternating depth 0
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual ("function alternating(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}")
          [boolArg c, boolArg d, wordArg 9, wordArg 2]
        let choices := if depth = 0 then [] else if !c then [false] else if depth = 1 then [true]
          else if d then [true, true] else (List.range depth).map fun level => level % 2 == 0
        checked source inputs arguments choices core (if depth == 0 || (c && (depth == 1 || !d)) then wordArg 9 else wordArg 2)
          (if depth = 0 then 1 else if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1) (6 * depth + 1) (depth != 0)
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        let (source, inputs, arguments) ← actual "function asymmetric(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
          [boolArg c, boolArg d, wordArg x, wordArg y]
        checked source inputs arguments (if c then [true, d] else [false]) (.ifE (.var 3)
          (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
            (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)))
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩
          (if c then if d then 19 else 21 else 11) 21
  let left : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let right : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Fn", left, right), ("Cell", ⟨.cell .word, .cellRef .word 17, .cellRef⟩, ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    for c in [false, true] do
      let (source, inputs, arguments) ← actual (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++
        "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}") [boolArg c, x, y]
      checked source inputs arguments (if c then [true, true] else [false]) (.ifE (.var 2)
        (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) (if c then x else y) (if c then 13 else 7) 13
  for c in [false, true] do
    let (source, inputs, arguments) ← actual "function simple(c: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x;return z;}else{return y;}}" [boolArg c, wordArg 9, wordArg 2]
    let selected := Core.Expr.letE (.var 1) (.var 0)
    checked source inputs arguments [c] (.ifE (.var 2) selected (.var 0)) (if c then wordArg 9 else wordArg 2) (if c then 7 else 4) 7
    assertTrue (decide (terminalReturnTreeFuelBound source.value.body = 4 ∧ typedLetReturnBodyFuelBound source.value.body = 4)) "old source-only bounds changed"
    for store in stores do
      assertTrue ((inputs.runTerminalReturnTree? 7 source.value.body store).isNone && (inputs.runTypedLetReturnBody? types owner 7 source.value.body store).isNone)
        "old rejected branch-local profile was expanded"
      if c then
        let environment := inputs.environment.values
        let run := fun fuel => inputs.runTypedLetReturnTree? types owner fuel source.value.body store
        let frame := Core.Frame.letBody (.var 0) environment
        for (spent, state) in [(1, (⟨.eval (.var 2) environment, [.ifBranches selected (.var 0) environment], store⟩ : Core.State)),
            (3, ⟨.eval selected environment, [], store⟩), (4, ⟨.eval (.var 1) environment, [frame], store⟩),
            (5, ⟨.ret (.word (word 9)), [frame], store⟩), (6, ⟨.eval (.var 0) (.word (word 9) :: environment), [], store⟩)] do
          assertTrue (decide (run spent = some (.word, .outOfFuel state))) "actual if/initializer/obtained-value/tail checkpoint changed"
        let some (_, .outOfFuel checkpoint) := run 5 | throw (IO.userError "genuine retained initializer value disappeared")
        assertTrue (decide (Core.runStateful 0 { checkpoint with continuation := [] } = .done (.word (word 9)) store ∧
          Core.runStateful 0 checkpoint = .outOfFuel checkpoint ∧ Core.runStateful 2 checkpoint = .done (.word (word 9)) store ∧
          run 2 ≠ some (.word, .done (.word (word 9)) store))) "dropping pending frames or restarting became resumption"
  for (body, choices, core, value, cost) in [("{return x;}", [], Core.Expr.var 1, wordArg 9, 1),
      ("{return;}", [], .unit, (⟨.unit, .unit, .unit⟩ : TypedRuntimeArgument), 1),
      ("{if(c){if(c){return x;}else{return y;}}else{return y;}}", [true, true], .ifE (.var 2) (.ifE (.var 2) (.var 1) (.var 0)) (.var 0), wordArg 9, 7),
      ("{let z: Word=x;let w: Word=z - y;return w;}", [], .letE (.var 1) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)), wordArg 7, 11)] do
    let (source, inputs, arguments) ← actual ("function old(c: Bool,x: Word,y: Word)" ++ (if value.type = .unit then "" else " returns (Word)") ++ body)
      [boolArg true, wordArg 9, wordArg 2]
    checked source inputs arguments choices core value cost cost false
  let (inferred, original, args) ← actual "function rejected(c: Bool,x: Word,y: Word) returns (Word){let z=x;return z;}" [boolArg true, wordArg 9, wordArg 2]
  let ⟨blockSpan, ⟨letSpan, .letDecl name none (some initializer)⟩ :: _⟩ := inferred.value.body | throw (IO.userError "original none annotation changed")
  assertTrue (blockSpan.contains letSpan && letSpan.contains name.span && letSpan.contains initializer.span &&
    decide (name.value = "z" ∧ name.span.endByte ≤ initializer.span.startByte ∧ typedLetReturnBodyFuelBound inferred.value.body = 0 ∧
      (original.toTypeInputs.bindFresh owner name.value .word).context = (⟨owner, 3⟩, .word) :: original.context)) "inferred span/type/ID or old bound changed"
  checked inferred original args [] (.letE (.var 1) (.var 0)) (wordArg 9) 4 4
  for store in stores do
    let env := original.environment.values
    for (spent, state) in [(1, (⟨.eval (.var 1) env, [.letBody (.var 0) env], store⟩ : Core.State)),
        (2, ⟨.ret (.word (word 9)), [.letBody (.var 0) env], store⟩), (3, ⟨.eval (.var 0) (.word (word 9) :: env), [], store⟩)] do
      assertTrue (decide (original.runTypedLetReturnTree? types owner spent inferred.value.body store = some (.word, .outOfFuel state))) "inferred initializer/tail checkpoint changed"
  for (body, bound, script) in [("{if(c){let z: Unknown=x;return z;}else{return y;}}", 7, some [true]),
      ("{if(c){let x: Word=x;return x;}else{return y;}}", 7, some [true]),
      ("{if(c){let z: Word=x;return z;}else{if(c){return y;}else{return missing;}}}", 7, some [true]),
      ("{if(c){let z: Word=missing;return x;}else{return y;}}", 7, none), ("{if(c){return x;}else{return c;}}", 4, none),
      ("{let z: Word;return x;}", 0, none), ("{}", 0, none), ("{return x;return y;}", 0, none), ("{return missing;}", 1, none)] do
    let (source, inputs, _) ← actual ("function rejected(c: Bool,x: Word,y: Word) returns (Word)" ++ body) [boolArg true, wordArg 9, wordArg 2]
    assertTrue (decide (typedLetReturnTreeFuelBound source.value.body = bound) && (inputs.checkTypedLetReturnTree? types owner source.value.body).isNone)
      "numerical bound licensed whole rejected syntax"
    for store in stores do
      if let some choices := script then
        let certificate ← certify inputs.names inputs.environment store source.value.body choices
        have _ := certificate.costed.cost_le_fuelBound
        assertTrue (decide (certificate.cost = 7 ∧ certificate.value = .word (word 9))) "raw upper bound required whole acceptance"
      for fuel in [0, 1, bound, bound + 2, 50] do
        have _ := LocalInputs.runTypedLetReturnTree?_eq_none_iff (inputs := inputs) (types := types) (owner := owner)
          (body := source.value.body) (fuel := fuel) (store := store)
        oldShapes inputs source.value.body fuel store
        assertTrue (inputs.runTypedLetReturnTree? types owner fuel source.value.body store).isNone "fuel repaired whole rejection"

end Tests
end
