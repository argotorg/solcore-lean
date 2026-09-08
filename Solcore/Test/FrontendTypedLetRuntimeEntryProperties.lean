import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties

/-! Independent arbitrary-length entry provenance and actual cost keep prefix
locals out of the parameter record and retain real pending let continuations. -/

set_option autoImplicit false

namespace Tests.FrontendTypedLetRuntimeEntry

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LetEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "let-entry.sol"⟩, 211, 11⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def binding (name previous : String) : Syntax.Statement :=
  ⟨span, .letDecl ⟨span, name⟩ (some (named "Payload")) (some (ref previous))⟩
private def statements : List String → String → List Syntax.Statement
  | [], previous => [⟨span, .returnStmt (some (ref previous))⟩]
  | name :: rest, previous => binding name previous :: statements rest name
private def chain (names : List String) (previous : String) : Syntax.Block := ⟨span, statements names previous⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | count + 1 => .letE (.var 0) (core count)
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "flag" "Flag", parameter "seed" "Payload"]
private def declaration (names : List String) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "chain"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, chain names "seed"⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs :=
  (LocalTypeInputs.empty.bindFresh owner "flag" .bool).bindFresh owner "seed" type
private def compiled (names : List String) (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core names.length, type⟩
private theorem chainElaborated (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnBodyElaborates (types type) owner inputs (chain names previous) (core names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil =>
      simp only [chain, statements, List.length_nil, core]
      exact .terminal (.single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typing))
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      simp only [chain, statements, binding, List.length_cons, core]
      apply TypedLetReturnBodyElaborates.binding (name := ⟨span, name⟩)
        (show TypeNameDenotes (types type) (named "Payload") type from .named .head)
        (fresh name (by simp)) resolution lowered typing
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
private theorem compilation (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (declaration names) (compiled names type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil),
    (chainElaborated names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)).returnTree⟩

theorem arbitrary_length_whole_entry_compilation_needs_no_runtime_values
    (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (definitions : Core.DataEnvironment) :
    RuntimeFunctionCompiles (types type) owner (declaration names) (compiled names type) ∧
    compileRuntimeFunction? (types type) owner (declaration names) = some (compiled names type) ∧
    (compiled names type).inputs.names.map Prod.fst = ["seed", "flag"] ∧
    (compiled names type).inputs.context.values = [type, .bool] ∧ Core.HasType [type, .bool] (core names.length) type definitions := by
  refine ⟨compilation names type distinct fresh, (compilation names type distinct fresh).complete, rfl, rfl, ?_⟩
  have typed (count : Nat) (tail : List Core.Ty) : Core.HasType (type :: tail) (core count) type definitions := by
    induction count generalizing tail with
    | zero => exact .var rfl
    | succ count ih => exact .letE (.var rfl) (ih _)
  exact typed names.length [.bool]

theorem nominal_entry_compilation_does_not_manufacture_an_actual_argument
    (names : List String) (nominal : Core.DataTypeId) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (declaration names) = some (compiled names (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation names _ distinct fresh).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (flag : Bool) (actual : Actual type) : List TypedRuntimeArgument :=
  [⟨.bool, .bool flag, .bool⟩, ⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (flag : Bool) (actual : Actual type) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "flag" .bool (.bool flag) .bool).bindFresh owner "seed" type actual.val actual.property
private def prepared {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) : PreparedRuntimeFunction :=
  ⟨inputs flag actual, core names.length, type⟩
private theorem preparation {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionPrepares (types type) owner (declaration names) (arguments flag actual) (prepared names flag actual) :=
  ⟨(compilation names type distinct fresh).header,
    .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil), (compilation names type distinct fresh).body⟩
private theorem chainCost (names : List String) (previous : String) (table : LocalNameTable)
    (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnBodyEvaluatesWithCost owner table environment store (chain names previous) value store (3 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .terminal (.single (.expression head))
  | cons name rest ih =>
      have arithmetic : 1 + (3 * rest.length + 1) + 2 = 3 * (name :: rest).length + 1 := by simp; omega
      simpa only [arithmetic, chain, statements, binding] using
        TypedLetReturnBodyEvaluatesWithCost.binding (name := ⟨span, name⟩) (annotation := named "Payload")
          head (ih name _ _ (.identifier .head .head))
private theorem costed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration names) (arguments flag actual) store type actual.val store (3 * names.length + 1) :=
  .intro (preparation names flag actual distinct fresh)
    (chainCost names "seed" (inputs flag actual).names (inputs flag actual).environment actual.val store (.identifier .head .head)).returnTree
private theorem bound (names : List String) (previous : String) :
    typedLetReturnBodyFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, ref, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnBodyFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega

theorem actual_preparation_retains_only_original_parameters_and_exactly_one_value_reverse
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (fuel : Nat) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    prepareRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) = some (prepared names flag actual) ∧
    (prepared names flag actual).toCompiled = compiled names type ∧
    (prepared names flag actual).inputs.environment.values = [actual.val, .bool flag] ∧
    runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store)) :=
  ⟨(preparation names flag actual distinct fresh).complete, rfl, rfl,
    (compilation names type distinct fresh).run_eq (arguments flag actual) rfl fuel store⟩

theorem independent_whole_entry_cost_proves_all_fuel_thresholds_and_actual_core_safety
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store) (fuel : Nat)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (error : Core.MachineFault) (state : Core.State) :
    Core.Steps (3 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) (Core.State.final actual.val store) ∧
    (runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store = some (type, .done actual.val store) ↔ 3 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (declaration names) (arguments flag actual) fuel store = some (type, .outOfFuel checkpoint)) ↔ fuel < 3 * names.length + 1) ∧
    Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store) ≠ .fault error state :=
  ⟨(costed names flag actual store distinct fresh).compiled_toSteps (compilation names type distinct fresh),
    (costed names flag actual store distinct fresh).run_done_iff, (costed names flag actual store distinct fresh).run_outOfFuel_iff,
    (compilation names type distinct fresh).compiled_never_faults (arguments flag actual) rfl fuel store error state⟩

private theorem recursiveBound (names : List String) (previous : String) :
    typedLetReturnTreeFuelBound (chain names previous) = 3 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [chain, statements, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | cons name rest ih =>
      simp only [chain, statements, binding, typedLetReturnTreeFuelBound, ref, localExpressionFuelBound, List.length_cons]
      have tail := ih name
      simp only [chain] at tail
      rw [tail]; omega
theorem all_three_entry_bounds_include_strict_prefix_work
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    3 * names.length + 1 ≤ typedLetReturnTreeFuelBound (declaration names).value.body ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration names)
      (arguments flag actual) (3 * names.length + 1) store = some (type, .done value store)) ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration names)
      (arguments flag actual) (3 * names.length + 1) store = some (type, .done value store) ∧
      Core.runStateful (3 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) = .done value store) := by
  have enough : typedLetReturnTreeFuelBound (declaration names).value.body ≤ 3 * names.length + 1 := Nat.le_of_eq (recursiveBound names "seed")
  exact ⟨(costed names flag actual store distinct fresh).cost_le_fuelBound,
    (preparation names flag actual distinct fresh).hasType.run_done_of_fuelBound store _ enough,
    (compilation names type distinct fresh).run_done_of_fuelBound (arguments flag actual) rfl store _ enough⟩

theorem the_old_tree_bound_does_not_pay_for_a_valid_initialized_prefix
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (store : Core.Store) :
    terminalReturnTreeFuelBound (declaration ["x"]).value.body = 0 ∧
    typedLetReturnBodyFuelBound (declaration ["x"]).value.body = 4 ∧
    (∃ checkpoint, runRuntimeFunction? (types type) owner (declaration ["x"]) (arguments flag actual) 0 store = some (type, .outOfFuel checkpoint)) ∧
    runRuntimeFunction? (types type) owner (declaration ["x"]) (arguments flag actual) 4 store = some (type, .done actual.val store) :=
  ⟨by simp [declaration, chain, statements, binding, terminalReturnTreeFuelBound], bound ["x"] "seed",
    (costed ["x"] flag actual store (by decide) (by decide)).run_outOfFuel_iff.mpr (by decide),
    (costed ["x"] flag actual store (by decide) (by decide)).run_done_iff.mpr (by decide)⟩

private def checkpoint {type : Core.Ty} (second : Bool) (flag : Bool) (actual : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret actual.val, [.letBody (if second then .var 0 else core 1)
    (if second then [actual.val, actual.val, .bool flag] else [actual.val, .bool flag])], store⟩
private theorem exhausted {type : Core.Ty} (second : Bool) (flag : Bool) (actual : Actual type) (store : Core.Store) :
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) (if second then 5 else 2) store =
      some (type, .outOfFuel (checkpoint second flag actual store)) := by
  rw [(compilation ["x", "y"] type (by decide) (by decide)).run_eq (arguments flag actual) rfl]
  cases second <;> rfl

theorem genuine_two_let_checkpoints_and_multiple_chunks_retain_the_actual_remainder
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) 2 store = some (type, .outOfFuel (checkpoint false flag actual store)) ∧
    Core.runStateful 3 (checkpoint false flag actual store) = .outOfFuel (checkpoint true flag actual store) ∧
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) 5 store = some (type, .outOfFuel (checkpoint true flag actual store)) ∧
    Core.Steps 2 (checkpoint true flag actual store) (Core.State.final actual.val store) ∧
    runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) (5 + additional) store =
      some (type, Core.runStateful additional (checkpoint true flag actual store)) :=
  ⟨exhausted false flag actual store, rfl, exhausted true flag actual store,
    ((costed ["x", "y"] flag actual store (by decide) (by decide)).residual_of_outOfFuel (exhausted true flag actual store)).2,
    runRuntimeFunction?_resume (exhausted true flag actual store) additional⟩

theorem owner_changes_keep_full_checkpoints_and_store_replay_keeps_its_own_store
    {type : Core.Ty} (flag : Bool) (actual : Actual type) (otherOwner : Resolved.DeclarationId)
    (first replacement : Core.Store) (fuel : Nat) :
    runRuntimeFunction? (types type) otherOwner (declaration ["x", "y"]) (arguments flag actual) 5 first = some (type, .outOfFuel (checkpoint true flag actual first)) ∧
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration ["x", "y"]) (arguments flag actual) replacement type actual.val replacement 7 ∧
    ((∃ state, runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) fuel first = some (type, .outOfFuel state)) ↔
      ∃ state, runRuntimeFunction? (types type) owner (declaration ["x", "y"]) (arguments flag actual) fuel replacement = some (type, .outOfFuel state)) :=
  ⟨(runRuntimeFunction?_owner_eq (types type) otherOwner owner _ _ 5 first).trans (exhausted true flag actual first),
    (costed ["x", "y"] flag actual first (by decide) (by decide)).change_store replacement,
    runRuntimeFunction?_outOfFuel_store_iff (types type) owner _ _ fuel first replacement type⟩

theorem semantic_type_extension_preserves_the_complete_original_parameter_record
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"])
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) :
    RuntimeFunctionCompiles next owner (declaration names) (compiled names type) ∧
    compileRuntimeFunction? next owner (declaration names) = some (compiled names type) :=
  ⟨(compilation names type distinct fresh).extend_types extension,
    compileRuntimeFunction?_some_of_extends extension (compilation names type distinct fresh).complete⟩

theorem same_typed_wrong_core_does_not_satisfy_whole_source_provenance (type : Core.Ty) :
    Core.HasType [type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (declaration ["x"]) { compiled ["x"] type with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation ["x"] type (by decide) (by decide)))
  cases wrong

theorem missing_or_wrong_ordered_arguments_are_not_prefix_local_inputs
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"])
    (supplied : List TypedRuntimeArgument) (mismatch : supplied.map (·.type) ≠ [.bool, type]) (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (types type) owner (declaration names) = some (compiled names type) ∧
    runRuntimeFunction? (types type) owner (declaration names) supplied fuel store = none := by
  refine ⟨(compilation names type distinct fresh).complete, ?_⟩
  rw [runRuntimeFunction?_factorization, (compilation names type distinct fresh).complete]
  simp only [bind, Option.bind_some, compiled, initial, Resolved.LocalScope.values, LocalTypeInputs.context,
    LocalTypeInputs.bindFresh, LocalTypeInputs.empty, List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, mismatch, ↓reduceIte]

theorem actual_cells_and_captured_closures_cross_prefixes_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word)) owner (declaration ["x", "y"])
      (arguments true ⟨.cellRef .word location, .cellRef⟩) 7 store = some (.cell .word, .done (.cellRef .word location) store) ∧
    runRuntimeFunction? (types (.function .bool .word)) owner (declaration ["x", "y"])
      (arguments false ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) 7 store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(costed ["x", "y"] true _ store (by decide) (by decide)).run_done_iff.mpr (by decide),
    (costed ["x", "y"] false _ store (by decide) (by decide)).run_done_iff.mpr (by decide)⟩

end Tests.FrontendTypedLetRuntimeEntry
