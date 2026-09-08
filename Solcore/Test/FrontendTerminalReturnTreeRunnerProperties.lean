import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeResumptionProperties
import Solcore.Frontend.TerminalReturnTreeRunnerEmbeddingProperties
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Exact recursive fuel uses actual typed inputs and genuine suspended states.
The generic untyped contrast does not fabricate a proof-carrying input row. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnTreeRunner

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TreeRunner", by decide⟩], by decide⟩⟩, 0⟩
private theorem yc : "y" ≠ "c" := by decide
private theorem xc : "x" ≠ "c" := by decide
private theorem yx : "y" ≠ "x" := by decide
private theorem i20 : (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem i10 : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem i21 : (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩ := by decide
private def span : Syntax.SourceSpan := ⟨⟨.main, "tree-runner.sol"⟩, 81, 5⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def x := returned (some (ref "x"))
private def y := returned (some (ref "y"))
private def tree := branch (branch x y) y
private def inner : Core.Expr := .ifE (.var 2) (.var 1) (.var 0)
private def core : Core.Expr := .ifE (.var 2) inner (.var 0)
private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def inputs {type : Core.Ty} (choice : Bool) (left right : Actual type) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "x" type left.val left.property).bindFresh
    owner "y" type right.val right.property
private def required (choice : Bool) : Nat := if choice then 7 else 4
private def result {type : Core.Ty} (choice : Bool) (left right : Actual type) : Core.Value := if choice then left.val else right.val
private theorem elaborated {type : Core.Ty} (choice : Bool) (left right : Actual type) :
    TerminalReturnTreeElaborates (inputs choice left right).names (inputs choice left right).context tree core type := by
  have guardR : ResolvesLocalExpression (inputs choice left right).names (ref "c") (.var ⟨owner, 0⟩) :=
    .identifier (.tail yc (.tail xc .head))
  have guardL : Resolved.Lowers (inputs choice left right).context.ids (.var ⟨owner, 0⟩) (.var 2) :=
    .var (.tail i20 (.tail i10 .head))
  have guardT : Resolved.HasType (inputs choice left right).context (.var ⟨owner, 0⟩) .bool :=
    .var (.tail i20 (.tail i10 .head))
  have leftE : TerminalReturnTreeElaborates (inputs choice left right).names (inputs choice left right).context x (.var 1) type :=
    .single (.expression (.identifier (.tail yx .head)) (.var (.tail i21 .head)) (.var (.tail i21 .head)))
  have rightE : TerminalReturnTreeElaborates (inputs choice left right).names (inputs choice left right).context y (.var 0) type :=
    .single (.expression (.identifier .head) (.var .head) (.var .head))
  exact .conditional guardR guardL guardT (.conditional guardR guardL guardT leftE rightE) rightE
private theorem costed {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store tree (result choice left right) store (required choice) := by
  have c : LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail yc (.tail xc .head)) (.tail i20 (.tail i10 .head))
  have l : LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "x") left.val store 1 := .identifier (.tail yx .head) (.tail i21 .head)
  have r : LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "y") right.val store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse c (.single (.expression r))
  · exact .ifTrue c (.ifTrue c (.single (.expression l)))

theorem all_fuel_boundaries_retain_the_exact_selected_value_and_store
    {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) (fuel : Nat) :
    ((inputs choice left right).runTerminalReturnTree? fuel tree store = some (type, .done (result choice left right) store) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice left right).runTerminalReturnTree? fuel tree store = some (type, .outOfFuel checkpoint)) ↔ fuel < required choice) ∧
    (Core.runStateful fuel (Core.State.initial core [right.val, left.val, .bool choice] store) = .done (result choice left right) store ↔
      ∃ cost, TerminalReturnTreeEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
        store tree (result choice left right) store cost ∧ cost ≤ fuel) := by
  have accepted := (elaborated choice left right).complete
  refine ⟨?_, ?_, elaborateTerminalReturnTree?_run_done_iff_cost accepted (inputs choice left right).sameIds⟩
  · simpa only [LocalInputs.runTerminalReturnTree?, LocalInputs.checkTerminalReturnTree?, accepted, bind,
      Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed choice left right store).checked_runStateful_done_iff (fuel := fuel) accepted (inputs choice left right).sameIds
  · simpa only [LocalInputs.runTerminalReturnTree?, LocalInputs.checkTerminalReturnTree?, accepted, bind,
      Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed choice left right store).checked_runStateful_outOfFuel_iff (fuel := fuel) accepted (inputs choice left right).sameIds

theorem exact_optional_results_execute_the_original_ordered_values
    {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) (fuel : Nat) (execution : Core.StatefulRunResult) :
    (inputs choice left right).runTerminalReturnTree? fuel tree store = some (type, execution) ↔
      Core.runStateful fuel (Core.State.initial core [right.val, left.val, .bool choice] store) = execution := by
  constructor
  · intro observed
    obtain ⟨candidate, checked, ran⟩ := LocalInputs.runTerminalReturnTree?_eq_some_iff.mp observed
    have equal := (elaborated choice left right).complete
    change elaborateTerminalReturnTree? _ _ tree = _ at checked
    rw [equal] at checked
    cases checked
    exact ran
  · intro ran
    exact LocalInputs.runTerminalReturnTree?_eq_some_iff.mpr ⟨core, (elaborated choice left right).complete, ran⟩

theorem typed_cost_characterizations_include_whole_acceptance_and_exclude_faults
    {type : Core.Ty} (choice : Bool) (left right : Actual type) (store finalStore : Core.Store)
    (value : Core.Value) (fuel : Nat) (error : Core.MachineFault) (state : Core.State) :
    ((inputs choice left right).runTerminalReturnTree? fuel tree store = some (type, .done value finalStore) ↔
      TerminalReturnTreeHasType (inputs choice left right).names (inputs choice left right).context tree type ∧
      ∃ cost, TerminalReturnTreeEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
        store tree value finalStore cost ∧ cost ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice left right).runTerminalReturnTree? fuel tree store = some (type, .outOfFuel checkpoint)) ↔
      TerminalReturnTreeHasType (inputs choice left right).names (inputs choice left right).context tree type ∧
      ∃ actual cost, TerminalReturnTreeEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
        store tree actual store cost ∧ fuel < cost) ∧
    (inputs choice left right).runTerminalReturnTree? fuel tree store ≠ some (type, .fault error state) :=
  ⟨LocalInputs.runTerminalReturnTree?_done_iff_typed_cost, LocalInputs.runTerminalReturnTree?_outOfFuel_iff_typed_cost,
    (inputs choice left right).runTerminalReturnTree?_never_faults tree fuel store type error state⟩

theorem recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient :
    terminalReturnTreeFuelBound tree = 7 ∧ terminalReturnBodyFuelBound tree = 4 ∧
    terminalReturnTreeFuelBound (returned none) = 1 := by
  simp [terminalReturnTreeFuelBound, terminalReturnBodyFuelBound, conditionalReturnBodyFuelBound,
    returnBodyFuelBound, localExpressionFuelBound, tree, branch, x, y, returned, ref]

theorem the_short_path_finishes_below_the_bound_while_the_old_bound_exhausts_the_long_path
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) :
    (inputs false left right).runTerminalReturnTree? 4 tree store = some (type, .done right.val store) ∧
    4 < terminalReturnTreeFuelBound tree ∧
    ∃ checkpoint, (inputs true left right).runTerminalReturnTree? (terminalReturnBodyFuelBound tree) tree store =
      some (type, .outOfFuel checkpoint) :=
  ⟨(all_fuel_boundaries_retain_the_exact_selected_value_and_store false left right store 4).1.mpr (by decide),
    by rw [recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient.1]; decide,
    (all_fuel_boundaries_retain_the_exact_selected_value_and_store true left right store _).2.1.mpr
      (by rw [recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient.2.1]; decide)⟩

theorem actual_typed_cost_existence_and_both_sufficient_fuel_interfaces
    {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) :
    required choice ≤ terminalReturnTreeFuelBound tree ∧ Core.ValueHasType (result choice left right) type ∧
    Core.runStateful 7 (Core.State.initial core [right.val, left.val, .bool choice] store) = .done (result choice left right) store ∧
    (inputs choice left right).runTerminalReturnTree? 7 tree store = some (type, .done (result choice left right) store) := by
  have typing := (elaborated choice left right).hasType
  obtain ⟨actual, cost, evaluation, actualTyped, _⟩ := LocalInputs.terminalReturnTree_typed_cost_execution typing store
  have same := evaluation.deterministic (costed choice left right store)
  obtain ⟨generic, _, genericRun⟩ := elaborateTerminalReturnTree?_run_done_of_fuelBound
    (elaborated choice left right).complete (inputs choice left right).sameIds (inputs choice left right).environmentTyped store 7
      (by rw [recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient.1]; decide)
  obtain ⟨wrapped, _, wrappedRun⟩ := LocalInputs.runTerminalReturnTree?_done_of_fuelBound typing store 7
    (by rw [recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient.1]; decide)
  have completed := (all_fuel_boundaries_retain_the_exact_selected_value_and_store choice left right store 7).1.mpr
    (by cases choice <;> decide)
  have machine := (exact_optional_results_execute_the_original_ordered_values choice left right store 7 _).mp completed
  change Core.runStateful 7 (Core.State.initial core [right.val, left.val, .bool choice] store) = _ at genericRun
  rw [machine] at genericRun
  rw [completed] at wrappedRun
  cases genericRun
  cases wrappedRun
  exact ⟨(costed choice left right store).cost_le_fuelBound, same.1 ▸ actualTyped, machine, completed⟩

private def outerCheckpoint {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches inner (.var 0) [right.val, left.val, .bool choice]], store⟩
private def innerCheckpoint {type : Core.Ty} (left right : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool true), [.ifBranches (.var 1) (.var 0) [right.val, left.val, .bool true]], store⟩
theorem genuine_checkpoints_retain_their_environments_frames_and_exact_residuals
    {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) :
    (inputs choice left right).runTerminalReturnTree? 2 tree store = some (type, .outOfFuel (outerCheckpoint choice left right store)) ∧
    Core.Steps (required choice - 2) (outerCheckpoint choice left right store) (Core.State.final (result choice left right) store) ∧
    (inputs true left right).runTerminalReturnTree? 5 tree store = some (type, .outOfFuel (innerCheckpoint left right store)) ∧
    Core.Steps 2 (innerCheckpoint left right store) (Core.State.final left.val store) := by
  have outer : Core.runStateful 2 (Core.State.initial core [right.val, left.val, .bool choice] store) =
      .outOfFuel (outerCheckpoint choice left right store) := by cases choice <;> rfl
  have inner : Core.runStateful 5 (Core.State.initial core [right.val, left.val, .bool true] store) =
      .outOfFuel (innerCheckpoint left right store) := rfl
  exact ⟨(exact_optional_results_execute_the_original_ordered_values choice left right store 2 _).mpr outer,
    ((costed choice left right store).checked_residual_of_outOfFuel (elaborated choice left right).complete (inputs choice left right).sameIds outer).2,
    (exact_optional_results_execute_the_original_ordered_values true left right store 5 _).mpr inner,
    ((costed true left right store).checked_residual_of_outOfFuel (elaborated true left right).complete (inputs true left right).sameIds inner).2⟩

theorem multiple_chunks_resume_the_actual_suspended_states_without_resetting
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (outerCheckpoint true left right store) = .outOfFuel (innerCheckpoint left right store) ∧
    Core.runStateful 2 (innerCheckpoint left right store) = .done left.val store ∧
    (inputs true left right).runTerminalReturnTree? (2 + additional) tree store =
      some (type, Core.runStateful additional (outerCheckpoint true left right store)) ∧
    (inputs true left right).runTerminalReturnTree? (5 + additional) tree store =
      some (type, Core.runStateful additional (innerCheckpoint left right store)) := by
  have checkpoints := genuine_checkpoints_retain_their_environments_frames_and_exact_residuals true left right store
  exact ⟨rfl, rfl, LocalInputs.runTerminalReturnTree?_resume checkpoints.1 additional,
    LocalInputs.runTerminalReturnTree?_resume checkpoints.2.2.1 additional⟩

theorem dropping_a_pending_frame_observes_the_wrong_completed_control (store : Core.Store) :
    Core.runStateful 0 (outerCheckpoint true ⟨.word .zero, .word⟩ ⟨.word .zero, .word⟩ store) =
      .outOfFuel (outerCheckpoint true ⟨.word .zero, .word⟩ ⟨.word .zero, .word⟩ store) ∧
    Core.runStateful 0 ⟨.ret (.bool true), [], store⟩ = .done (.bool true) store := ⟨rfl, rfl⟩

theorem typed_existing_cells_and_captured_closures_are_returned_without_store_access
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    (inputs true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩).runTerminalReturnTree? 7 tree store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    (inputs true ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩
      ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩).runTerminalReturnTree? 7 tree store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(actual_typed_cost_existence_and_both_sufficient_fuel_interfaces true _ _ store).2.2.2,
    (actual_typed_cost_existence_and_both_sufficient_fuel_interfaces true _ _ store).2.2.2⟩

theorem aligned_but_untyped_guards_fault_even_at_zero_remaining_fuel (word : Core.Word) (store : Core.Store) :
    let good := inputs true (⟨.word word, .word⟩ : Actual .word) ⟨.word word, .word⟩
    let bad : Resolved.Environment := [(⟨owner, 2⟩, .word word), (⟨owner, 1⟩, .word word), (⟨owner, 0⟩, .word word)]
    let checkpoint : Core.State := ⟨.ret (.word word), [.ifBranches inner (.var 0) bad.values], store⟩
    elaborateTerminalReturnTree? good.names good.context tree = some (core, .word) ∧ bad.ids = good.context.ids ∧
    terminalReturnTreeFuelBound tree ≤ 7 ∧
    Core.runStateful 2 (Core.State.initial core bad.values store) = .fault (.expectedBool (.word word)) checkpoint ∧
    Core.runStateful 7 (Core.State.initial core bad.values store) = .fault (.expectedBool (.word word)) checkpoint := by
  exact ⟨(elaborated true _ _).complete, rfl,
    by rw [recursive_bounds_are_conservative_and_the_old_bound_is_not_sufficient.1]; decide, rfl, rfl⟩

private def unsupported : Syntax.Block := ⟨span, []⟩
theorem a_zero_bound_is_not_acceptance_and_a_skipped_bad_arm_still_rejects
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) (fuel : Nat) :
    terminalReturnTreeFuelBound unsupported = 0 ∧ terminalReturnTreeFuelBound (branch unsupported y) = 4 ∧
    TerminalReturnTreeEvaluatesWithCost (inputs false left right).names (inputs false left right).environment
      store (branch unsupported y) right.val store 4 ∧
    4 ≤ terminalReturnTreeFuelBound (branch unsupported y) ∧
    (inputs false left right).runTerminalReturnTree? fuel unsupported store = none ∧
    (inputs false left right).runTerminalReturnTree? fuel (branch unsupported y) store = none := by
  have rejected : (inputs false left right).checkTerminalReturnTree? (branch unsupported y) = none := by
    simp [LocalInputs.checkTerminalReturnTree?, elaborateTerminalReturnTree?, branch, unsupported]
  have c : LocalExpressionEvaluatesWithCost (inputs false left right).names (inputs false left right).environment
      store (ref "c") (.bool false) store 1 := .identifier (.tail yc (.tail xc .head)) (.tail i20 (.tail i10 .head))
  have r : LocalExpressionEvaluatesWithCost (inputs false left right).names (inputs false left right).environment
      store (ref "y") right.val store 1 := .identifier .head .head
  have raw : TerminalReturnTreeEvaluatesWithCost (inputs false left right).names (inputs false left right).environment
      store (branch unsupported y) right.val store 4 := .ifFalse c (.single (.expression r))
  refine ⟨?_, ?_, raw, raw.cost_le_fuelBound,
    LocalInputs.runTerminalReturnTree?_eq_none_iff.mpr ?_, LocalInputs.runTerminalReturnTree?_eq_none_iff.mpr rejected⟩
  · simp [terminalReturnTreeFuelBound, unsupported]
  · simp [terminalReturnTreeFuelBound, unsupported, branch, y, returned, ref, localExpressionFuelBound, returnBodyFuelBound]
  · simp [LocalInputs.checkTerminalReturnTree?, elaborateTerminalReturnTree?, unsupported]

theorem old_singleton_shapes_preserve_every_optional_result_at_every_fuel
    (supplied : LocalInputs) (condition : Syntax.Expr) (first side : Option Syntax.Expr) (fuel : Nat) (store : Core.Store) :
    supplied.runTerminalReturnTree? fuel (returned first) store = supplied.runReturnBody? fuel (returned first) store ∧
    supplied.runTerminalReturnTree? fuel (returned first) store = supplied.runTerminalReturnBody? fuel (returned first) store ∧
    supplied.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition (returned first) (some (returned side))⟩]⟩ store =
      supplied.runConditionalReturnBody? fuel ⟨span, [⟨span, .ifThen condition (returned first) (some (returned side))⟩]⟩ store ∧
    supplied.runTerminalReturnTree? fuel ⟨span, [⟨span, .ifThen condition (returned first) (some (returned side))⟩]⟩ store =
      supplied.runTerminalReturnBody? fuel ⟨span, [⟨span, .ifThen condition (returned first) (some (returned side))⟩]⟩ store :=
  ⟨supplied.runTerminalReturnTree?_single fuel first span span store,
    supplied.runTerminalReturnTree?_single_terminal fuel first span span store,
    supplied.runTerminalReturnTree?_conditional_singletons fuel condition first side span span span span span span store,
    supplied.runTerminalReturnTree?_conditional_singletons_terminal fuel condition first side span span span span span span store⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def entry : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "deep"⟩, none,
    ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, tree⟩⟩
private def declaredInputs (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type).bindFresh owner "y" type
theorem deep_body_execution_and_exact_function_entry_compilation_agree
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) :
    RuntimeFunctionHeader (types type) entry.value.signature type ∧
    RuntimeParametersDeclare (types type) owner entry.value.signature.parameters.elements (declaredInputs type) ∧
    (inputs true left right).runTerminalReturnTree? 7 tree store = some (type, .done left.val store) ∧
    compileRuntimeFunction? (types type) owner entry = some ⟨declaredInputs type, core, type⟩ := by
  have declared : RuntimeParametersDeclare (types type) owner entry.value.signature.parameters.elements (declaredInputs type) :=
    .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
  have compilation : RuntimeFunctionCompiles (types type) owner entry ⟨declaredInputs type, core, type⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, declared, elaborated true left right⟩
  exact ⟨compilation.header, declared,
    (actual_typed_cost_existence_and_both_sufficient_fuel_interfaces true left right store).2.2.2, compilation.complete⟩

end Tests.FrontendTerminalReturnTreeRunner
