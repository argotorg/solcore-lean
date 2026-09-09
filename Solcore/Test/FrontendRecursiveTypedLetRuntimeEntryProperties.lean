import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionOwnerProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionCompilationTypeExtensionProperties
import Solcore.Frontend.TypedLetReturnBodyFuelBoundProperties

/-! Independent recursive source provenance and cost reach the existing entry.
Only original parameters inhabit the records; sibling lets remain scope-local. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveTypedLetRuntimeEntry
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive-entry.sol"⟩, 222, 5⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def named (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type), (["Flag"], .bool)]
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def bind (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some (named "Payload")) (some value)⟩ :: tail.value⟩
private def branch (condition : Syntax.Expr) (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen condition yes (some no)⟩]⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private def guardCore : Core.Expr := .binary .wordEq (.word .zero) (.word .zero)
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => branch guard (bind name (ref previous) (tree rest name)) (bind name (ref previous) (returned name))
private def core : Nat → Core.Expr
  | 0 => .var 0
  | depth + 1 => .ifE guardCore (.letE (.var 0) (core depth)) (.letE (.var 0) (.var 0))
private def parameter (name type : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ (named type)⟩
private def parameters := [parameter "flag" "Flag", parameter "seed" "Payload"]
private def entry (body : Syntax.Block) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "tree"⟩, none, ⟨span, parameters⟩, ⟨none, none⟩, some ⟨span, ⟨span, [named "Payload"]⟩⟩, none⟩, body⟩⟩
private def initial (type : Core.Ty) : LocalTypeInputs := (LocalTypeInputs.empty.bindFresh owner "flag" .bool).bindFresh owner "seed" type
private def compiled (names : List String) (type : Core.Ty) : CompiledRuntimeFunction := ⟨initial type, core names.length, type⟩
private theorem treeElab (names : List String) (previous : String) (type : Core.Ty)
    (inputs : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ inputs.names.map Prod.fst)
    (resolution : ResolvesLocalExpression inputs.names (ref previous) resolved)
    (lowered : Resolved.Lowers inputs.ids resolved (.var 0)) (typing : Resolved.HasType inputs.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner inputs (tree names previous) (core names.length) type := by
  induction names generalizing previous inputs resolved with
  | nil => exact .single (.expression resolution (by simpa only [List.length_nil, core, LocalTypeInputs.context_ids] using lowered) typing)
  | cons name rest ih =>
    have parts := List.nodup_cons.mp distinct
    have eta : ⟨span, (tree rest name).value⟩ = tree rest name := by cases rest <;> rfl
    refine .conditional (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (.binary .word .word) (.binary .word .word) ?_ ?_
    · apply TypedLetReturnTreeElaborates.binding (name := ⟨span, name⟩)
        (show TypeNameDenotes (types type) (named "Payload") type from .named .head).structural (fresh name (by simp)) resolution lowered typing
      rw [eta]
      apply ih name (inputs.bindFresh owner name type) _ parts.2
      · intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩
      · exact .identifier .head
      · exact .var .head
      · exact .var .head
    · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typing
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem header (type : Core.Ty) (body : Syntax.Block) : RuntimeFunctionHeader (types type) (entry body).value.signature type :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem declared (type : Core.Ty) : RuntimeParametersDeclare (types type) owner parameters (initial type) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil)
private theorem compilation (names : List String) (type : Core.Ty) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (entry (tree names "seed")) (compiled names type) :=
  ⟨header type _, declared type, treeElab names "seed" type (initial type) _ distinct fresh (.identifier .head) (.var .head) (.var .head)⟩

theorem arbitrary_fresh_depth_compiles_both_scopes_without_runtime_inhabitants
    (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (entry (tree names "seed")) (compiled names type) ∧
    compileRuntimeFunction? (types type) owner (entry (tree names "seed")) = some (compiled names type) ∧
    (compiled names type).inputs.names.map Prod.fst = ["seed", "flag"] ∧ (compiled names type).inputs.context.values = [type, .bool] ∧
    (initial type |>.bindFresh owner "left" type).ids = (initial type |>.bindFresh owner "right" .bool).ids :=
  ⟨compilation names type distinct fresh, (compilation names type distinct fresh).complete, rfl, rfl, rfl⟩
theorem nominal_parameters_compile_but_supply_no_actual_argument (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (entry (tree ["x", "y"] "seed")) = some (compiled ["x", "y"] (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation _ _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private abbrev Actual (type : Core.Ty) := { value : Core.Value // Core.ValueHasType value type }
private def arguments {type : Core.Ty} (flag : Bool) (actual : Actual type) : List TypedRuntimeArgument := [⟨.bool, .bool flag, .bool⟩, ⟨type, actual.val, actual.property⟩]
private def inputs {type : Core.Ty} (flag : Bool) (actual : Actual type) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "flag" .bool (.bool flag) .bool).bindFresh owner "seed" type actual.val actual.property
private theorem boundArguments {type : Core.Ty} (flag : Bool) (actual : Actual type) :
    RuntimeParametersBind (types type) owner parameters (arguments flag actual) (inputs flag actual) :=
  .cons (.named (.tail (by decide) .head)) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named .head) (by change "seed" ∉ ["flag"]; decide) .nil)
private theorem preparation {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionPrepares (types type) owner (entry (tree names "seed")) (arguments flag actual) ⟨inputs flag actual, core names.length, type⟩ :=
  ⟨header type _, boundArguments flag actual, (compilation names type distinct fresh).body⟩
private theorem treeCost (names : List String) (previous : String) (table : LocalNameTable) (environment : Resolved.Environment)
    (value : Core.Value) (store : Core.Store) (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (tree names previous) value store (10 * names.length + 1) := by
  induction names generalizing previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have eta : ⟨span, (tree rest name).value⟩ = tree rest name := by cases rest <;> rfl
    have arithmetic : 5 + (1 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    rw [← arithmetic]
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning))
    apply TypedLetReturnTreeEvaluatesWithCost.binding head
    rw [eta]
    exact ih name _ _ (.identifier .head .head)
private theorem costed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry (tree names "seed")) (arguments flag actual) store type actual.val store (10 * names.length + 1) :=
  .intro (preparation names flag actual distinct fresh) (treeCost names "seed" _ _ actual.val store (.identifier .head .head))
private theorem bound (names : List String) (previous : String) : typedLetReturnTreeFuelBound (tree names previous) = 10 * names.length + 1 := by
  induction names generalizing previous with
  | nil => simp [tree, returned, typedLetReturnTreeFuelBound, returnBodyFuelBound, ref, localExpressionFuelBound]
  | cons name rest ih =>
    have eta : ⟨span, (tree rest name).value⟩ = tree rest name := by cases rest <;> rfl
    simp only [tree, branch, bind, returned, typedLetReturnTreeFuelBound, returnBodyFuelBound,
      guard, zero, ref, localExpressionFuelBound, eta, ih, List.length_cons]
    omega

theorem actual_parameter_records_factor_once_into_the_exact_machine
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (fuel : Nat) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    prepareRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) = some ⟨inputs flag actual, core names.length, type⟩ ∧
    (inputs flag actual).toTypeInputs = initial type ∧ (inputs flag actual).bindings.length = 2 ∧
    (inputs flag actual).environment.values = (arguments flag actual).reverse.map (·.value) ∧
    runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store =
      some (type, Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store)) :=
  ⟨(preparation names flag actual distinct fresh).complete, rfl, rfl, rfl,
    (compilation names type distinct fresh).run_eq (arguments flag actual) rfl fuel store⟩
theorem independent_cost_fixes_all_fuel_paths_and_both_safety_endpoints
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (fuel : Nat) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (error : Core.MachineFault) (state : Core.State) :
    Core.Steps (10 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) (Core.State.final actual.val store) ∧
    (runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store = some (type, .done actual.val store) ↔ 10 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store = some (type, .outOfFuel checkpoint)) ↔ fuel < 10 * names.length + 1) ∧
    runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store ≠ some (type, .fault error state) ∧
    Core.runStateful fuel (Core.State.initial (core names.length) [actual.val, .bool flag] store) ≠ .fault error state :=
  ⟨(costed names flag actual store distinct fresh).compiled_toSteps (compilation names type distinct fresh),
    (costed names flag actual store distinct fresh).run_done_iff, (costed names flag actual store distinct fresh).run_outOfFuel_iff,
    runRuntimeFunction?_never_faults _ _ _ _ _ _ _ _ _, (compilation names type distinct fresh).compiled_never_faults (arguments flag actual) rfl _ _ _ _⟩
theorem all_three_source_bounds_pay_for_recursive_branch_local_work
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type) (store : Core.Store)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    10 * names.length + 1 ≤ typedLetReturnTreeFuelBound (entry (tree names "seed")).value.body ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (entry (tree names "seed"))
      (arguments flag actual) (10 * names.length + 1) store = some (type, .done value store)) ∧
    (∃ value, Core.ValueHasType value type ∧ runRuntimeFunction? (types type) owner (entry (tree names "seed"))
      (arguments flag actual) (10 * names.length + 1) store = some (type, .done value store) ∧
      Core.runStateful (10 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store) = .done value store) :=
  ⟨(costed names flag actual store distinct fresh).cost_le_fuelBound,
    (preparation names flag actual distinct fresh).hasType.run_done_of_fuelBound _ _ (Nat.le_of_eq (bound names "seed")),
    (compilation names type distinct fresh).run_done_of_fuelBound _ rfl _ _ (Nat.le_of_eq (bound names "seed"))⟩

private def shortBody := branch (ref "flag") (bind "x" (ref "seed") (returned "x")) (returned "seed")
private def shortCore : Core.Expr := .ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)
private theorem shortElab (type : Core.Ty) : TypedLetReturnTreeElaborates (types type) owner (initial type) shortBody shortCore type :=
  .conditional (.identifier (.tail (by change "seed" ≠ "flag"; decide) .head))
    (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))
    (.var (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head))
    (.binding (.named .head) (by change "x" ∉ ["seed", "flag"]; decide) (.identifier .head) (.var .head) (.var .head) (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem shortCost {type : Core.Ty} (flag : Bool) (actual : Actual type) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry shortBody) (arguments flag actual) store type actual.val store (if flag then 7 else 4) := by
  apply RuntimeFunctionEvaluatesWithCost.intro (prepared := ⟨inputs flag actual, shortCore, type⟩) ⟨header _ _, boundArguments _ _, shortElab type⟩
  have condition : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "flag") (.bool flag) store 1 :=
    .identifier (.tail (by change "seed" ≠ "flag"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  have seed : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "seed") actual.val store 1 := .identifier .head .head
  cases flag
  · apply TypedLetReturnTreeEvaluatesWithCost.ifFalse (branchCost := 1) condition
    exact .single (.expression (.identifier .head .head))
  · apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (branchCost := 4) condition
    exact .binding seed (.single (.expression (.identifier .head .head)))
theorem old_four_step_bound_cannot_replace_the_new_seven_step_entry_bound
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) :
    typedLetReturnBodyFuelBound shortBody = 4 ∧ typedLetReturnTreeFuelBound shortBody = 7 ∧
    (∃ checkpoint, runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) 4 store = some (type, .outOfFuel checkpoint)) ∧
    runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) 7 store = some (type, .done actual.val store) ∧
    runRuntimeFunction? (types type) owner (entry shortBody) (arguments false actual) 4 store = some (type, .done actual.val store) :=
  ⟨by simp [shortBody, branch, bind, returned, typedLetReturnBodyFuelBound, terminalReturnTreeFuelBound, returnBodyFuelBound, ref, localExpressionFuelBound],
    by simp [shortBody, branch, bind, returned, typedLetReturnTreeFuelBound, returnBodyFuelBound, ref, localExpressionFuelBound], (shortCost true actual store).run_outOfFuel_iff.mpr (by decide),
    (shortCost true actual store).run_done_iff.mpr (by decide), (shortCost false actual store).run_done_iff.mpr (by decide)⟩
private def checkpoint {type : Core.Ty} (phase : Nat) (actual : Actual type) (store : Core.Store) : Core.State :=
  if phase = 0 then ⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) [actual.val, .bool true]], store⟩
  else if phase = 1 then ⟨.ret actual.val, [.letBody (.var 0) [actual.val, .bool true]], store⟩
  else ⟨.eval (.var 0) [actual.val, actual.val, .bool true], [], store⟩
private theorem exhausted {type : Core.Ty} (phase : Nat) (actual : Actual type) (store : Core.Store) (small : phase ≤ 2) :
    runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) (if phase = 0 then 2 else if phase = 1 then 5 else 6) store =
      some (type, .outOfFuel (checkpoint phase actual store)) := by
  rw [(show RuntimeFunctionCompiles (types type) owner (entry shortBody) ⟨initial type, shortCore, type⟩ from ⟨header _ _, declared _, shortElab _⟩).run_eq _ rfl]
  have casesPhase : phase = 0 ∨ phase = 1 ∨ phase = 2 := by omega
  rcases casesPhase with rfl | rfl | rfl <;> rfl
theorem real_if_initializer_and_tail_checkpoints_support_full_three_chunk_resumption
    {type : Core.Ty} (actual : Actual type) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) 2 store = some (type, .outOfFuel (checkpoint 0 actual store)) ∧
    Core.runStateful 3 (checkpoint 0 actual store) = .outOfFuel (checkpoint 1 actual store) ∧
    Core.runStateful 1 (checkpoint 1 actual store) = .outOfFuel (checkpoint 2 actual store) ∧
    Core.Steps 2 (checkpoint 1 actual store) (Core.State.final actual.val store) ∧
    Core.Steps 1 (checkpoint 2 actual store) (Core.State.final actual.val store) ∧
    runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) (5 + additional) store = some (type, Core.runStateful additional (checkpoint 1 actual store)) :=
  ⟨exhausted 0 actual store (by decide), rfl, rfl,
    ((shortCost true actual store).residual_of_outOfFuel (exhausted 1 actual store (by decide))).2,
    ((shortCost true actual store).compiled_residual_of_outOfFuel (spent := 6)
      (show RuntimeFunctionCompiles (types type) owner (entry shortBody) ⟨initial type, shortCore, type⟩ from ⟨header _ _, declared _, shortElab _⟩) (by rfl)).2,
    runRuntimeFunction?_resume (exhausted 1 actual store (by decide)) additional⟩

theorem owner_store_and_annotation_transport_preserve_the_original_parameters
    {type : Core.Ty} (actual : Actual type) (otherOwner : Resolved.DeclarationId) (first replacement : Core.Store)
    (next : TypeNameTable) (extension : TypeNameTable.Extends (types type) next) (fuel : Nat) :
    runRuntimeFunction? (types type) otherOwner (entry shortBody) (arguments true actual) 5 first = some (type, .outOfFuel (checkpoint 1 actual first)) ∧
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry shortBody) (arguments true actual) replacement type actual.val replacement 7 ∧
    (runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) fuel first = some (type, .done actual.val first) ↔
      runRuntimeFunction? (types type) owner (entry shortBody) (arguments true actual) fuel replacement = some (type, .done actual.val replacement)) ∧
    compileRuntimeFunction? next owner (entry (tree ["x", "y"] "seed")) = some (compiled ["x", "y"] type) :=
  ⟨(runRuntimeFunction?_owner_eq _ otherOwner owner _ _ 5 first).trans (exhausted 1 actual first (by decide)),
    (shortCost true actual first).change_store replacement, runRuntimeFunction?_done_store_iff _ _ _ _ _ _ _ _ _,
    compileRuntimeFunction?_some_of_extends extension (compilation _ _ (by decide) (by decide)).complete⟩
theorem actual_cells_and_captured_functions_cross_recursive_arms_without_effects
    (location : Core.Location) (word : Core.Word) (store : Core.Store) :
    runRuntimeFunction? (types (.cell .word)) owner (entry (tree ["x", "y"] "seed")) (arguments true ⟨.cellRef .word location, .cellRef⟩) 21 store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    runRuntimeFunction? (types (.function .bool .word)) owner (entry (tree ["x", "y"] "seed"))
      (arguments false ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) 21 store =
      some (.function .bool .word, .done (.closure .bool .word (.var 1) [.word word]) store) :=
  ⟨(costed _ true _ store (by decide) (by decide)).run_done_iff.mpr (by decide),
    (costed _ false _ store (by decide) (by decide)).run_done_iff.mpr (by decide)⟩
theorem same_typed_core_does_not_replace_independent_whole_source_provenance (type : Core.Ty) :
    Core.HasType [type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (entry (tree ["x"] "seed")) { compiled ["x"] type with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core (forged.result_unique (compilation ["x"] type (by decide) (by decide)))
  cases wrong

private def sub (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .subtract⟩ right⟩
private def mathBody := branch (ref "flag") (bind "x" (sub zero (ref "seed")) (returned "x"))
  (bind "x" ⟨span, .unary ⟨span, .bitNot⟩ (sub (ref "seed") zero)⟩ (returned "seed"))
private def mathCore : Core.Expr := .ifE (.var 1) (.letE (.binary .wordSub (.word .zero) (.var 0)) (.var 0))
  (.letE (.unary .wordNot (.binary .wordSub (.var 0) (.word .zero))) (.var 1))
private theorem mathCompilation : RuntimeFunctionCompiles (types .word) owner (entry mathBody) ⟨initial .word, mathCore, .word⟩ :=
  ⟨header _ _, declared _, .conditional (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
    (.binding (.named .head) (by decide) (.subtract (.wordLiteral zeroMeaning) (.identifier .head)) (.binary .word (.var .head)) (.binary .word (.var .head))
      (.single (.expression (.identifier .head) (.var .head) (.var .head))))
    (.binding (.named .head) (by decide) (.bitNot (.subtract (.identifier .head) (.wordLiteral zeroMeaning)))
      (.unary (.binary (.var .head) .word)) (.unary (.binary (.var .head) .word))
      (.single (.expression (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)))))⟩
private theorem mathCost (flag : Bool) (word : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩)
      store .word (.word (if flag then Core.Word.zero.sub word else word)) store (if flag then 11 else 13) := by
  let actual : Actual .word := ⟨.word word, .word⟩
  apply RuntimeFunctionEvaluatesWithCost.intro (prepared := ⟨inputs flag actual, mathCore, .word⟩) ⟨header _ _, boundArguments _ _, mathCompilation.body⟩
  have seed : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "seed") (.word word) store 1 := .identifier .head .head
  have choice : LocalExpressionEvaluatesWithCost (inputs flag actual).names (inputs flag actual).environment store (ref "flag") (.bool flag) store 1 :=
    .identifier (.tail (by change "seed" ≠ "flag"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
  cases flag
  · apply TypedLetReturnTreeEvaluatesWithCost.ifFalse (branchCost := 10) choice
    apply TypedLetReturnTreeEvaluatesWithCost.binding (tailCost := 1) (.bitNot (.subtract seed (.wordLiteral zeroMeaning)))
    exact .single (.expression (.identifier (.tail (by decide) .head) (.tail (by change (⟨owner, 2⟩ : Resolved.LocalId) ≠ ⟨owner, 1⟩; decide) .head)))
  · apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (branchCost := 8) choice
    exact .binding (.subtract (.wordLiteral zeroMeaning) seed) (.single (.expression (.identifier .head .head)))
theorem noncommutative_initializers_keep_their_order_and_unused_work
    (flag : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    compileRuntimeFunction? (types .word) owner (entry mathBody) = some ⟨initial .word, mathCore, .word⟩ ∧
    (runRuntimeFunction? (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩) fuel store =
      some (.word, .done (.word (if flag then Core.Word.zero.sub word else word)) store) ↔ (if flag then 11 else 13) ≤ fuel) :=
  ⟨mathCompilation.complete, (mathCost flag word store).run_done_iff⟩
private def invalidBody := branch (ref "flag") (returned "seed")
  ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (named "Unknown")) (some (ref "seed"))⟩, ⟨span, .returnStmt (some (ref "x"))⟩]⟩
theorem a_selected_raw_value_does_not_hide_the_invalid_other_annotation (word : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (inputs true ⟨.word word, .word⟩).names
      (inputs true ⟨.word word, .word⟩).environment store invalidBody (.word word) store 4 ∧
    compileRuntimeFunction? (types .word) owner (entry invalidBody) = none := by
  refine ⟨?_, ?_⟩
  · apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (conditionCost := 1) (branchCost := 1)
    · exact .identifier (.tail (by change "seed" ≠ "flag"; decide) .head) (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
    · exact .single (.expression (.identifier .head .head))
  apply compileRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨⟨initialInputs, actualCore, type⟩, accepted⟩
  cases accepted.body with
  | single child => cases child
  | conditional _ _ _ _ invalid =>
    cases invalid with
    | single child => cases child
    | binding meaning _ _ _ _ _ =>
      have impossible := meaning.complete
      simp only [named, interpretStructuralType?_named_eq_typeName] at impossible
      change none = some _ at impossible
      cases impossible

end Tests.FrontendRecursiveTypedLetRuntimeEntry
