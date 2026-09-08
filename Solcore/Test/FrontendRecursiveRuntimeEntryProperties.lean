import Solcore.Frontend.TypedLetReturnTreeEvaluationEmbeddingProperties
import Solcore.Frontend.TypedLetReturnTreeEmbeddingProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.TerminalReturnBodyFuelBoundProperties
import Solcore.Frontend.TerminalReturnTreeFuelBoundProperties

/-! Value-free recursive compilation and actual-argument execution are distinct
contracts. Original parameter order, exact Core and genuine states are retained. -/

set_option autoImplicit false

namespace Tests.FrontendRecursiveRuntimeEntry

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private theorem yc : "y" ≠ "c" := by decide
private theorem xc : "x" ≠ "c" := by decide
private theorem yx : "y" ≠ "x" := by decide
private theorem i20 : id 2 ≠ id 0 := by decide
private theorem i10 : id 1 ≠ id 0 := by decide
private theorem i21 : id 2 ≠ id 1 := by decide
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive-entry.sol"⟩, 101, 8⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def body : Nat → Syntax.Block
  | 0 => returned "x"
  | depth + 1 => branch (body depth) (returned "y")
private def core : Nat → Core.Expr
  | 0 => .var 1
  | depth + 1 => .ifE (.var 2) (core depth) (.var 0)
private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def parameters := [parameter "c" "Flag", parameter "x" "Payload", parameter "y" "Payload"]
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def declaration (depth : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "recursive"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Payload"]⟩⟩, none⟩, body depth⟩⟩
private def staticInputs (type : Core.Ty) : LocalTypeInputs :=
  ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh owner "x" type).bindFresh owner "y" type
private def compiled (depth : Nat) (type : Core.Ty) : CompiledRuntimeFunction := ⟨staticInputs type, core depth, type⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (staticInputs type) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil))
private theorem elaborated (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates (staticInputs type).names (staticInputs type).context (body depth) (core depth) type := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail yx .head)) (.var (.tail i21 .head)) (.var (.tail i21 .head)))
  | succ depth ih =>
    exact .conditional (.identifier (.tail yc (.tail xc .head)))
      (.var (.tail i20 (.tail i10 .head))) (.var (.tail i20 (.tail i10 .head))) ih
      (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem compilation (depth : Nat) (type : Core.Ty) :
    RuntimeFunctionCompiles (types type) owner (declaration depth) (compiled depth type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, declared type, TypedLetReturnBodyElaborates.returnTree <| .terminal (elaborated depth type)⟩

theorem arbitrary_depth_and_types_compile_from_independent_whole_source_provenance
    (depth : Nat) (type : Core.Ty) (definitions : Core.DataEnvironment) :
    RuntimeFunctionCompiles (types type) owner (declaration depth) (compiled depth type) ∧
    compileRuntimeFunction? (types type) owner (declaration depth) = some (compiled depth type) ∧
    (compiled depth type).inputs.context.values = [type, type, .bool] ∧ Core.HasType [type, type, .bool] (core depth) type definitions := by
  refine ⟨compilation depth type, (compilation depth type).complete, rfl, ?_⟩
  induction depth with
  | zero => exact .var rfl
  | succ depth ih => exact .ifE (.var rfl) ih (.var rfl)

theorem nominal_compilation_does_not_manufacture_an_actual_argument (depth : Nat) (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (declaration depth) = some (compiled depth (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation depth _).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩
  cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem same_typed_wrong_core_and_arbitrary_records_do_not_supply_provenance
    (depth : Nat) (type : Core.Ty) (candidate : CompiledRuntimeFunction)
    (provenance : RuntimeFunctionCompiles (types type) owner (declaration depth) candidate) :
    candidate = compiled depth type ∧ Core.HasType [type, type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (declaration depth) { compiled depth type with core := .var 0 } := by
  refine ⟨provenance.result_unique (compilation depth type), .var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation depth type))
  cases depth <;> cases wrong

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (choice : Bool) (left right : Actual type) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨type, left.val, left.property⟩, ⟨type, right.val, right.property⟩]
private def inputs {type : Core.Ty} (choice : Bool) (left right : Actual type) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "x" type left.val left.property).bindFresh
    owner "y" type right.val right.property
private def prepared {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) : PreparedRuntimeFunction :=
  ⟨inputs choice left right, core depth, type⟩
private theorem preparation {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) :
    RuntimeFunctionPrepares (types type) owner (declaration depth) (arguments choice left right) (prepared depth choice left right) :=
  ⟨(compilation depth type).header, .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "x" ∉ ["c"]; decide) (.cons (.named .head) (by change "y" ∉ ["x", "c"]; decide) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal (elaborated depth type)⟩
private theorem conditionCost {type : Core.Ty} (choice : Bool) (left right : Actual type) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail yc (.tail xc .head)) (.tail i20 (.tail i10 .head))
private theorem trueBodyCost {type : Core.Ty} (depth : Nat) (left right : Actual type) (store : Core.Store) :
    TerminalReturnTreeEvaluatesWithCost (inputs true left right).names (inputs true left right).environment
      store (body depth) left.val store (3 * depth + 1) := by
  induction depth with
  | zero => exact .single (.expression (.identifier (.tail yx .head) (.tail i21 .head)))
  | succ depth ih =>
    have arithmetic : 1 + (3 * depth + 1) + 2 = 3 * (depth + 1) + 1 := by omega
    simpa only [arithmetic, body, branch] using TerminalReturnTreeEvaluatesWithCost.ifTrue (conditionCost true left right store) ih
private def required (depth : Nat) (choice : Bool) : Nat := if choice then 3 * (depth + 1) + 1 else 4
private def result {type : Core.Ty} (choice : Bool) (left right : Actual type) : Core.Value := if choice then left.val else right.val
private theorem costed {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration (depth + 1)) (arguments choice left right)
      store type (result choice left right) store (required depth choice) := by
  apply RuntimeFunctionEvaluatesWithCost.intro (preparation (depth + 1) choice left right)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  have y : LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "y") right.val store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse (conditionCost false left right store) (.single (.expression y))
  · exact trueBodyCost (depth + 1) left right store

theorem actual_preparation_and_factorization_keep_source_argument_order_exactly_once
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (fuel : Nat) (store : Core.Store) :
    prepareRuntimeFunction? (types type) owner (declaration depth) (arguments choice left right) = some (prepared depth choice left right) ∧
    (prepared depth choice left right).toCompiled = compiled depth type ∧
    (prepared depth choice left right).inputs.environment.values = [right.val, left.val, .bool choice] ∧
    runRuntimeFunction? (types type) owner (declaration depth) (arguments choice left right) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (core depth) ((arguments choice left right).reverse.map (·.value)) store)) :=
  ⟨(preparation depth choice left right).complete, rfl, rfl, (compilation depth type).run_eq _ rfl fuel store⟩

theorem independent_recursive_cost_gives_all_entry_and_compiled_thresholds_and_safety
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) (fuel : Nat)
    (error : Core.MachineFault) (state : Core.State) :
    Core.Steps (required depth choice) (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store)
      (Core.State.final (result choice left right) store) ∧ Core.ValueHasType (result choice left right) type ∧
    (runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel store =
      some (type, .done (result choice left right) store) ↔ required depth choice ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel store =
      some (type, .outOfFuel checkpoint)) ↔ fuel < required depth choice) ∧
    Core.runStateful fuel (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store) ≠ .fault error state :=
  ⟨(costed depth choice left right store).compiled_toSteps (compilation _ type), (costed depth choice left right store).preserves_type,
    (costed depth choice left right store).run_done_iff, (costed depth choice left right store).run_outOfFuel_iff,
    (compilation (depth + 1) type).compiled_never_faults (arguments choice left right) rfl fuel store error state⟩

private theorem treeBound (depth : Nat) : terminalReturnTreeFuelBound (body depth) = 3 * depth + 1 := by
  induction depth with
  | zero => simp [body, returned, ref, terminalReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | succ depth ih =>
    simp only [body, branch, terminalReturnTreeFuelBound, ih, returned, returnBodyFuelBound,
      ref, localExpressionFuelBound]
    omega
private theorem recursiveBound (depth : Nat) : typedLetReturnTreeFuelBound (body depth) = 3 * depth + 1 := by
  induction depth with
  | zero => simp [body, returned, ref, typedLetReturnTreeFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  | succ depth ih =>
    simp only [body, branch, typedLetReturnTreeFuelBound, ih, returned, returnBodyFuelBound, ref, localExpressionFuelBound]
    omega
theorem all_three_entry_bound_contracts_use_the_recursive_bound
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    required depth choice ≤ typedLetReturnTreeFuelBound (declaration (depth + 1)).value.body ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration (depth + 1))
      (arguments choice left right) (3 * (depth + 1) + 1) store = some (type, .done value store)) ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (declaration (depth + 1))
      (arguments choice left right) (3 * (depth + 1) + 1) store = some (type, .done value store) ∧
      Core.runStateful (3 * (depth + 1) + 1) (Core.State.initial (core (depth + 1)) [right.val, left.val, .bool choice] store) = .done value store) := by
  have enough : typedLetReturnTreeFuelBound (declaration (depth + 1)).value.body ≤ 3 * (depth + 1) + 1 :=
    Nat.le_of_eq (recursiveBound _)
  exact ⟨(costed depth choice left right store).cost_le_fuelBound,
    (preparation _ choice left right).hasType.run_done_of_fuelBound store _ enough,
    (compilation _ type).run_done_of_fuelBound (arguments choice left right) rfl store _ enough⟩

theorem old_nonrecursive_bound_is_insufficient_for_the_new_deep_entry
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) :
    terminalReturnTreeFuelBound (body 2) = 7 ∧ terminalReturnBodyFuelBound (body 2) = 4 ∧
    (∃ checkpoint, runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 4 store = some (type, .outOfFuel checkpoint)) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments false left right) 4 store = some (type, .done right.val store) :=
  ⟨treeBound 2, by simp [body, branch, returned, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound],
    (costed 1 true left right store).run_outOfFuel_iff.mpr (by decide),
    (costed 1 false left right store).run_done_iff.mpr (by decide)⟩

private def checkpoint {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (core depth) (.var 0) [right.val, left.val, .bool choice]], store⟩
private theorem exhausted {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) :
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) 2 store =
      some (type, .outOfFuel (checkpoint depth choice left right store)) := by
  rw [(compilation _ type).run_eq (arguments choice left right) rfl 2 store]
  cases choice <;> rfl
theorem recursive_entry_resumes_its_real_checkpoint_and_exact_compiled_residual
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) 2 store =
      some (type, .outOfFuel (checkpoint depth choice left right store)) ∧
    Core.Steps (required depth choice - 2) (checkpoint depth choice left right store) (Core.State.final (result choice left right) store) ∧
    runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) (2 + additional) store =
      some (type, Core.runStateful additional (checkpoint depth choice left right store)) :=
  ⟨exhausted depth choice left right store, ((costed depth choice left right store).residual_of_outOfFuel
      (exhausted depth choice left right store)).2, runRuntimeFunction?_resume (exhausted depth choice left right store) additional⟩

theorem owner_changes_keep_full_checkpoints_while_store_replay_keeps_its_own_store
    {type : Core.Ty} (depth : Nat) (choice : Bool) (left right : Actual type) (otherOwner : Resolved.DeclarationId)
    (first replacement : Core.Store) (fuel : Nat) :
    runRuntimeFunction? (types type) otherOwner (declaration (depth + 1)) (arguments choice left right) 2 first =
      some (type, .outOfFuel (checkpoint depth choice left right first)) ∧
    RuntimeFunctionEvaluatesWithCost (types type) owner (declaration (depth + 1)) (arguments choice left right)
      replacement type (result choice left right) replacement (required depth choice) ∧
    ((∃ state, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel first = some (type, .outOfFuel state)) ↔
      ∃ state, runRuntimeFunction? (types type) owner (declaration (depth + 1)) (arguments choice left right) fuel replacement = some (type, .outOfFuel state)) :=
  ⟨(runRuntimeFunction?_owner_eq (types type) otherOwner owner _ _ 2 first).trans (exhausted depth choice left right first),
    (costed depth choice left right first).change_store replacement, runRuntimeFunction?_outOfFuel_store_iff (types type) owner _ _ fuel first replacement type⟩

theorem multiple_chunks_retain_the_actual_compiled_remainder
    {type : Core.Ty} (left right : Actual type) (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (checkpoint 1 true left right store) = .outOfFuel (checkpoint 0 true left right store) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 5 store =
      some (type, .outOfFuel (checkpoint 0 true left right store)) ∧
    Core.Steps 2 (checkpoint 0 true left right store) (Core.State.final left.val store) ∧
    runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) (5 + additional) store =
      some (type, Core.runStateful additional (checkpoint 0 true left right store)) := by
  have machine : Core.runStateful 5 (Core.State.initial (compiled 2 type).core
      ((arguments true left right).reverse.map (·.value)) store) = .outOfFuel (checkpoint 0 true left right store) := rfl
  have actual : runRuntimeFunction? (types type) owner (declaration 2) (arguments true left right) 5 store =
      some (type, .outOfFuel (checkpoint 0 true left right store)) :=
    ((compilation 2 type).run_eq (arguments true left right) rfl 5 store).trans (congrArg (fun result => some (type, result)) machine)
  exact ⟨rfl, actual, ((costed 1 true left right store).compiled_residual_of_outOfFuel (compilation 2 type) machine).2,
    runRuntimeFunction?_resume actual additional⟩

theorem actual_typed_cells_and_captured_closures_return_without_allocation_or_invocation
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word)) owner (declaration 2)
      (arguments true ⟨.cellRef .word location, .cellRef⟩ ⟨.cellRef .word location, .cellRef⟩) 7 store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    runRuntimeFunction? (types (.function .bool .word)) owner (declaration 2)
      (arguments true ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩
        ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) 7 store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(costed 1 true _ _ store).run_done_iff.mpr (by decide), (costed 1 true _ _ store).run_done_iff.mpr (by decide)⟩

theorem missing_or_wrong_ordered_actual_types_do_not_follow_from_static_compilation
    (depth : Nat) (type : Core.Ty) (supplied : List TypedRuntimeArgument)
    (mismatch : supplied.map (·.type) ≠ [.bool, type, type]) (fuel : Nat) (store : Core.Store) :
    compileRuntimeFunction? (types type) owner (declaration depth) = some (compiled depth type) ∧
    runRuntimeFunction? (types type) owner (declaration depth) supplied fuel store = none := by
  refine ⟨(compilation depth type).complete, ?_⟩
  rw [runRuntimeFunction?_factorization, (compilation depth type).complete]
  simp only [bind, Option.bind_some, show (compiled depth type).inputs.context.values.reverse = [.bool, type, type] from rfl,
    if_neg mismatch]

private def publicEntry (depth : Nat) : Syntax.FunctionDecl :=
  ⟨span, ⟨{ (declaration depth).value.signature with modifiers := ⟨some span, none⟩ }, body depth⟩⟩
private def duplicateEntry (depth : Nat) : Syntax.FunctionDecl := ⟨span,
  ⟨{ (declaration depth).value.signature with parameters := ⟨span, [parameter "c" "Flag", parameter "x" "Payload", parameter "x" "Payload"]⟩ }, body depth⟩⟩
theorem whole_header_and_complete_parameter_policy_still_precede_deep_body_acceptance
    (depth : Nat) (type : Core.Ty) :
    TerminalReturnTreeElaborates (staticInputs type).names (staticInputs type).context (body depth) (core depth) type ∧
    compileRuntimeFunction? (types type) owner (publicEntry depth) = none ∧
    compileRuntimeFunction? (types type) owner (duplicateEntry depth) = none :=
  ⟨elaborated depth type, rfl, rfl⟩

end Tests.FrontendRecursiveRuntimeEntry
