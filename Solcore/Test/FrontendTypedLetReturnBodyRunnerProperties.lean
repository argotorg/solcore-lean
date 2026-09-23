import Solcore.Frontend.TypedLetReturnBody

/-! Independent let chains distinguish actual typed inputs, numerical bounds,
whole acceptance and genuine suspended frames. No runtime value is fabricated. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetReturnBodyRunner

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetRunner", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-runner.sol"⟩, 151, 7⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some (ref previous))⟩
private def returned (name : String) : Syntax.Statement := ⟨span, .returnStmt (some (ref name))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [returned previous]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def body (twice : Bool) := chain (if twice then ["x", "y"] else ["x"]) "seed"
private def oneCore : Core.Expr := .letE (.var 0) (.var 0)
private def core (twice : Bool) : Core.Expr := if twice then .letE (.var 0) oneCore else oneCore
private def required (twice : Bool) : Nat := if twice then 7 else 4
private def staticInputs (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private def table : LocalNameTable := [("seed", id 0)]
private def environment (value : Core.Value) : Resolved.Environment := [(id 0, value)]
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (actual : Actual type) :=
  LocalInputs.empty.bindFresh owner "seed" type actual.val actual.property
private theorem elaborated (twice : Bool) (type : Core.Ty) :
    TypedLetReturnBodyElaborates (types type) owner (staticInputs type) (body twice) (core twice) type := by
  cases twice
  · exact .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head))))
  · exact .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
      (.binding (.named .head) (by change "y" ∉ ["x", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
        (.terminal (.single (.expression (.identifier .head) (.var .head) (.var .head)))))
private theorem chainCost (names : List String) (previous : String) (namesTable : LocalNameTable)
    (values : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost namesTable values store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner namesTable values store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous namesTable values with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := annotation)
          head (ih name _ _ (.identifier .head .head))
private theorem costed (twice : Bool) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (body twice) value store (required twice) := by
  cases twice
  · exact chainCost ["x"] "seed" table (environment value) value store (.identifier .head .head)
  · exact chainCost ["x", "y"] "seed" table (environment value) value store (.identifier .head .head)
private theorem chainBound (names : List String) (previous : String) :
    typedLetReturnBodyFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnBodyFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega
private theorem bounded (twice : Bool) : typedLetReturnBodyFuelBound (body twice) = required twice := by
  cases twice <;> exact chainBound _ _
private theorem runExact {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store)
    (fuel : Nat) (result : Core.StatefulRunResult) :
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, result) ↔
      Core.runStateful fuel (Core.State.initial (core twice) [actual.val] store) = result := by
  constructor
  · intro observed
    obtain ⟨candidate, checked, ran⟩ := LocalInputs.runTypedLetReturnBody?_eq_some_iff.mp observed
    change elaborateTypedLetReturnBody? (types type) owner (staticInputs type) (body twice) = _ at checked
    rw [(elaborated twice type).complete] at checked
    cases checked
    exact ran
  · intro ran
    exact LocalInputs.runTypedLetReturnBody?_eq_some_iff.mpr ⟨core twice, (elaborated twice type).complete, ran⟩

theorem arbitrary_raw_lists_have_exact_bounds_without_requiring_fresh_names_or_typed_values
    (names : List String) (value : Core.Value) (store : Core.Store) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment value) store (chain names "seed") value store (3 * names.length + 1) ∧
    typedLetReturnBodyFuelBound (chain names "seed") = 3 * names.length + 1 :=
  ⟨chainCost names "seed" table (environment value) value store (.identifier .head .head), chainBound names "seed"⟩

theorem static_provenance_needs_no_runtime_inhabitant_and_the_old_bound_misses_let_work
    (type : Core.Ty) (twice : Bool) :
    TypedLetReturnBodyElaborates (types type) owner (staticInputs type) (body twice) (core twice) type ∧
    typedLetReturnBodyFuelBound (body twice) = required twice ∧ terminalReturnTreeFuelBound (body twice) = 0 := by
  refine ⟨elaborated twice type, bounded twice, ?_⟩
  cases twice <;> simp [body, chain, statements, binding, terminalReturnTreeFuelBound]

theorem arbitrary_length_accepted_prefixes_use_the_independent_exact_count_at_every_fuel
    {type : Core.Ty} (names : List String) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (candidate : Core.Expr)
    (accepted : elaborateTypedLetReturnBody? (types type) owner (staticInputs type) (chain names "seed") = some (candidate, type)) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (chain names "seed") store =
      some (type, .done actual.val store) ↔ 3 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (chain names "seed") store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < 3 * names.length + 1) := by
  have count := chainCost names "seed" table (environment actual.val) actual.val store (.identifier .head .head)
  have checked : (inputs actual).checkTypedLetReturnBody? (types type) owner (chain names "seed") = some (candidate, type) := accepted
  have boundaries := And.intro (count.checked_runStateful_done_iff (fuel := fuel) accepted rfl)
    (count.checked_runStateful_outOfFuel_iff (fuel := fuel) accepted rfl)
  simp only [LocalInputs.runTypedLetReturnBody?, checked, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and]
  exact boundaries

theorem actual_typed_values_determine_all_fuel_thresholds_and_independent_cost_witnesses
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .done actual.val store) ↔ required twice ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required twice) ∧
    (Core.runStateful fuel (Core.State.initial (core twice) [actual.val] store) = .done actual.val store ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) actual.val store cost ∧ cost ≤ fuel) := by
  have accepted := (elaborated twice type).complete
  refine ⟨(runExact twice actual store fuel _).trans ((costed twice actual.val store).checked_runStateful_done_iff accepted rfl), ?_,
    elaborateTypedLetReturnBody?_run_done_iff_cost (environment := environment actual.val) accepted rfl⟩
  simp only [runExact]
  exact (costed twice actual.val store).checked_runStateful_outOfFuel_iff (fuel := fuel) accepted rfl

theorem both_typed_cost_characterizations_include_whole_typing_and_cannot_report_faults
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store finalStore : Core.Store)
    (value : Core.Value) (fuel : Nat) (error : Core.MachineFault) (state : Core.State) :
    ((inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .done value finalStore) ↔
      TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type ∧
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) value finalStore cost ∧ cost ≤ fuel) ∧
    ((∃ checkpoint, (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store = some (type, .outOfFuel checkpoint)) ↔
      TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type ∧
      ∃ value cost, TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body twice) value store cost ∧ fuel < cost) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel (body twice) store ≠ some (type, .fault error state) :=
  ⟨LocalInputs.runTypedLetReturnBody?_done_iff_typed_cost, LocalInputs.runTypedLetReturnBody?_outOfFuel_iff_typed_cost,
    (inputs actual).runTypedLetReturnBody?_never_faults (types type) owner (body twice) fuel store type error state⟩

theorem actual_typed_existence_and_both_bound_interfaces_keep_the_original_value_and_store
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) :
    required twice ≤ typedLetReturnBodyFuelBound (body twice) ∧ Core.ValueHasType actual.val type ∧
    Core.runStateful (required twice) (Core.State.initial (core twice) [actual.val] store) = .done actual.val store ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (required twice) (body twice) store = some (type, .done actual.val store) := by
  have typing : TypedLetReturnBodyHasType (types type) owner (inputs actual).toTypeInputs (body twice) type := (elaborated twice type).hasType
  obtain ⟨value, cost, evaluation, valueTyped, _⟩ := LocalInputs.typedLetReturnBody_typed_cost_execution typing store
  have same := evaluation.deterministic (costed twice actual.val store)
  obtain ⟨generic, _, genericRun⟩ := elaborateTypedLetReturnBody?_run_done_of_fuelBound (environment := environment actual.val)
    (elaborated twice type).complete rfl (Core.EnvironmentHasTypes.cons actual.property .nil) store (required twice) (by simp only [bounded, Nat.le_refl])
  obtain ⟨wrapped, _, wrappedRun⟩ := LocalInputs.runTypedLetReturnBody?_done_of_fuelBound typing store (required twice) (by simp only [bounded, Nat.le_refl])
  have completed := (actual_typed_values_determine_all_fuel_thresholds_and_independent_cost_witnesses twice actual store _).1.mpr (Nat.le_refl _)
  have machine := (runExact twice actual store _ _).mp completed
  change Core.runStateful (required twice) (Core.State.initial (core twice) [actual.val] store) = _ at genericRun
  rw [machine] at genericRun
  rw [completed] at wrappedRun
  cases genericRun
  cases wrappedRun
  exact ⟨(costed twice actual.val store).cost_le_fuelBound, same.1 ▸ valueTyped, machine, completed⟩

private def firstCheckpoint (twice : Bool) (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (if twice then oneCore else .var 0) [value]], store⟩
private def secondCheckpoint (value : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.ret value, [.letBody (.var 0) [value, value]], store⟩
theorem genuine_initializer_and_bound_checkpoints_keep_the_captured_and_extended_environments
    {type : Core.Ty} (twice : Bool) (actual : Actual type) (store : Core.Store) :
    (inputs actual).runTypedLetReturnBody? (types type) owner 1 (body twice) store =
      some (type, .outOfFuel ⟨.eval (.var 0) [actual.val], (firstCheckpoint twice actual.val store).continuation, store⟩) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 2 (body twice) store = some (type, .outOfFuel (firstCheckpoint twice actual.val store)) ∧
    Core.Steps (required twice - 2) (firstCheckpoint twice actual.val store) (Core.State.final actual.val store) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 3 (body twice) store =
      some (type, .outOfFuel ⟨.eval (if twice then oneCore else .var 0) [actual.val, actual.val], [], store⟩) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner 5 (body true) store = some (type, .outOfFuel (secondCheckpoint actual.val store)) ∧
    Core.Steps 2 (secondCheckpoint actual.val store) (Core.State.final actual.val store) := by
  have first : Core.runStateful 2 (Core.State.initial (core twice) [actual.val] store) = .outOfFuel (firstCheckpoint twice actual.val store) := by cases twice <;> rfl
  have second : Core.runStateful 5 (Core.State.initial (core true) [actual.val] store) = .outOfFuel (secondCheckpoint actual.val store) := rfl
  refine ⟨(runExact twice actual store 1 _).mpr (by cases twice <;> rfl), (runExact twice actual store 2 _).mpr first,
    ((costed twice actual.val store).checked_residual_of_outOfFuel (elaborated twice type).complete rfl first).2,
    (runExact twice actual store 3 _).mpr (by cases twice <;> rfl), (runExact true actual store 5 _).mpr second,
    ((costed true actual.val store).checked_residual_of_outOfFuel (elaborated true type).complete rfl second).2⟩

theorem two_and_three_chunks_resume_real_frames_while_dropping_them_or_restarting_changes_the_result
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 1 (firstCheckpoint true actual.val store) = .outOfFuel ⟨.eval oneCore [actual.val, actual.val], [], store⟩ ∧
    Core.runStateful 2 ⟨.eval oneCore [actual.val, actual.val], [], store⟩ = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 3 (firstCheckpoint true actual.val store) = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 2 (secondCheckpoint actual.val store) = .done actual.val store ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (2 + additional) (body true) store =
      some (type, Core.runStateful additional (firstCheckpoint true actual.val store)) ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner (5 + additional) (body true) store =
      some (type, Core.runStateful additional (secondCheckpoint actual.val store)) ∧
    Core.runStateful 0 ⟨.ret actual.val, [], store⟩ = .done actual.val store ∧
    Core.runStateful 0 (secondCheckpoint actual.val store) = .outOfFuel (secondCheckpoint actual.val store) ∧
    Core.runStateful 2 (Core.State.initial (core true) [actual.val] store) ≠ .done actual.val store := by
  have checkpoints := genuine_initializer_and_bound_checkpoints_keep_the_captured_and_extended_environments true actual store
  exact ⟨rfl, rfl, rfl, rfl, LocalInputs.runTypedLetReturnBody?_resume checkpoints.2.1 additional,
    LocalInputs.runTypedLetReturnBody?_resume checkpoints.2.2.2.2.1 additional, rfl, rfl, by intro impossible; cases impossible⟩

theorem existing_cells_and_captured_closures_are_returned_without_store_access_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    (inputs (⟨.cellRef .word location, .cellRef⟩ : Actual (.cell .word))).runTypedLetReturnBody? (types (.cell .word)) owner 7 (body true) store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs (⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩ : Actual (.function .bool .word))).runTypedLetReturnBody?
      (types (.function .bool .word)) owner 7 (body true) store = some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(runExact true _ store 7 _).mpr rfl, (runExact true _ store 7 _).mpr rfl⟩

theorem unknown_annotations_and_zero_bounds_do_not_turn_raw_paths_into_accepted_safe_runs
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (fuel : Nat) :
    TypedLetReturnBodyEvaluatesWithCost owner table (environment actual.val) store (body false) actual.val store 4 ∧
    typedLetReturnBodyFuelBound (body false) = 4 ∧
    (inputs actual).runTypedLetReturnBody? [] owner fuel (body false) store = none ∧
    typedLetReturnBodyFuelBound ⟨span, []⟩ = 0 ∧
    (inputs actual).runTypedLetReturnBody? (types type) owner fuel ⟨span, []⟩ store = none := by
  refine ⟨costed false actual.val store, bounded false, LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr ?_, ?_,
    LocalInputs.runTypedLetReturnBody?_eq_none_iff.mpr ?_⟩
  · simp [LocalInputs.checkTypedLetReturnBody?, body, chain, statements, binding, elaborateTypedLetReturnBody?, interpretTypeName?, annotation,
      TypeNameTable.lookup?]
  · simp [typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound]
  · simp [LocalInputs.checkTypedLetReturnBody?, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]

private def guarded : Syntax.Block := ⟨span, [binding "x" "seed",
  ⟨span, .ifThen (ref "x") ⟨span, [returned "x"]⟩ (some ⟨span, [returned "x"]⟩)⟩]⟩
private def guardedCore : Core.Expr := .letE (.var 0) (.ifE (.var 0) (.var 0) (.var 0))
private theorem guardedElab : TypedLetReturnBodyElaborates (types .bool) owner (staticInputs .bool) guarded guardedCore .bool :=
  .binding (.named .head) (by decide) (.identifier .head) (.var .head) (.var .head)
    (.terminal (.conditional (.identifier .head) (.var .head) (.var .head)
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))))
theorem accepted_aligned_but_untyped_environments_can_fault_even_at_the_full_bound (word : Core.Word) (store : Core.Store) :
    elaborateTypedLetReturnBody? (types .bool) owner (staticInputs .bool) guarded = some (guardedCore, .bool) ∧
    (environment (.word word)).ids = (staticInputs .bool).context.ids ∧ typedLetReturnBodyFuelBound guarded = 7 ∧
    Core.runStateful 5 (Core.State.initial guardedCore [.word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.var 0) (.var 0) [.word word, .word word]], store⟩ ∧
    Core.runStateful 7 (Core.State.initial guardedCore [.word word] store) =
      .fault (.expectedBool (.word word)) ⟨.ret (.word word), [.ifBranches (.var 0) (.var 0) [.word word, .word word]], store⟩ := by
  refine ⟨guardedElab.complete, rfl, ?_, rfl, rfl⟩
  simp [guarded, binding, returned, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem old_shapes_preserve_the_entire_optional_result_including_failures_and_checkpoints
    (actual : LocalInputs) (typeNames : TypeNameTable) (fuel : Nat) (store : Core.Store)
    (condition : Syntax.Expr) (yes no : Syntax.Block) (yesValue noValue : Option Syntax.Expr) :
    actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ store =
      actual.runReturnBody? fuel ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ store ∧
    actual.runTypedLetReturnBody? typeNames owner fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ store =
      actual.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩ store ∧
    actual.runTypedLetReturnBody? typeNames owner fuel
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ (some ⟨span, [⟨span, .returnStmt noValue⟩]⟩)⟩]⟩ store =
      actual.runConditionalReturnBody? fuel
        ⟨span, [⟨span, .ifThen condition ⟨span, [⟨span, .returnStmt yesValue⟩]⟩ (some ⟨span, [⟨span, .returnStmt noValue⟩]⟩)⟩]⟩ store :=
  ⟨actual.runTypedLetReturnBody?_single typeNames owner fuel yesValue span span store,
    actual.runTypedLetReturnBody?_conditional typeNames owner fuel condition yes no span span store,
    actual.runTypedLetReturnBody?_conditional_singletons typeNames owner fuel condition yesValue noValue span span span span span span store⟩

end Tests.FrontendTypedLetReturnBodyRunner
