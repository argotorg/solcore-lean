import Solcore.Frontend.Fragments.Internal.RuntimeFunctions
import Solcore.Frontend.Fragments.Internal.TypedLet
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
# Recursive typed let entry tests

Recursive runtime entries of typed lets.
-/

section
-- leanmerge: from Solcore.Test.FrontendRecursiveTypedLetRuntimeEntryProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRecursiveTypedLetRuntimeEntries
/-! Complete declarations retain independently specified Core and original
parameters. Selected source certificates fix values and costs before executing
the entry; genuine checkpoints retain branch-local values and captured frames. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RecursiveLetEntries", by decide⟩], by decide⟩⟩, 17⟩
private def otherOwner : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def wordArg (n : Nat) : TypedRuntimeArgument := ⟨.word, .word (word n), .word⟩
private def boolArg (b : Bool) : TypedRuntimeArgument := ⟨.bool, .bool b, .bool⟩
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩), (["Pkg", "Token"], .namedData ⟨92⟩)]
private def extended := types ++ [(["Word"], Core.Ty.bool), (["Fresh"], .namedData ⟨93⟩)]
private theorem grows : TypeNameTable.Extends types extended := TypeNameTable.Extends.append_right _ _
private def stores : List Core.Store := [[.word (word 91), .cellRef .word 40], [.closure .bool .bool (.var 0) [], .bool true, .word Core.Word.maximum]]
private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-recursive-let-entries.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next => return if next.atEnd && next.diagnostics.isEmpty then some source else none
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "parser invariant")
private structure Entry where
  source : Syntax.FunctionDecl
  compiled : CompiledRuntimeFunction
  provenance : RuntimeFunctionCompiles types owner source compiled
private theorem excludeWrong {source : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (provenance : RuntimeFunctionCompiles types owner source compiled) {wrong : Core.Expr} (different : wrong ≠ compiled.core) :
    ¬ RuntimeFunctionCompiles types owner source { compiled with core := wrong } := by
  intro other
  exact different (congrArg CompiledRuntimeFunction.core (other.result_unique provenance))
private def compile (content : String) (core : Core.Expr) (type : Core.Ty) (parameters : List Core.Ty) (bound : Nat) : IO Entry := do
  let some source ← parsed? content | throw (IO.userError "positive declaration did not completely parse")
  match accepted : compileRuntimeFunction? types owner source with
  | none => throw (IO.userError "recursive typed entry rejected")
  | some compiled =>
      let names ← source.value.signature.parameters.elements.mapM fun parameter => do
        let .typed none name annotation := parameter.value | throw (IO.userError "parameter shape changed")
        assertTrue (source.span.contains parameter.span && parameter.span.contains name.span && parameter.span.contains annotation.span) "parameter source positions changed"
        pure name.value
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ compiled.inputs.context.values = parameters.reverse ∧
        compiled.inputs.names = (names.zipIdx.map (fun (name, index) => (name, (⟨owner, index⟩ : Resolved.LocalId)))).reverse ∧
        compiled.inputs.bindings.length = parameters.length ∧ Core.infer? parameters.reverse core = some type ∧ typedLetReturnTreeFuelBound source.value.body = bound) &&
        (elaborateTypedLetReturnBody? types owner compiled.inputs source.value.body).isNone) "exact Core/type/bound or original parameter-only rows changed"
      have proof := compileRuntimeFunction?_sound accepted
      have _ := proof.core_hasType
      have _ := compileRuntimeFunction?_some_of_extends grows accepted
      assertTrue (decide ((compileRuntimeFunction? extended owner source).map (fun c => (c.core, c.returnType, c.inputs.names, c.inputs.context.values)) =
        some (core, type, compiled.inputs.names, parameters.reverse))) "annotation extension changed compiled provenance"
      let wrong := Core.Expr.ifE (.bool true) core core
      if different : wrong ≠ compiled.core then
        have _ := excludeWrong proof different
        assertTrue (decide (Core.infer? parameters.reverse wrong = some type)) "wrong Core did not retain the same type"
      else throw (IO.userError "wrong-Core contrast became identical")
      return ⟨source, compiled, proof⟩

private structure Expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table environment store source value store cost
private def expression (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) :
    IO (Expression table environment store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "independent source name missing")
      | some id =>
          match found : environment.lookup? id with
          | none => throw (IO.userError "independent actual value missing")
          | some value => return ⟨value, 1, by rw [sourceAt]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← expression table environment store operand
      match valueAt : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (valueAt ▸ child.costed)⟩
      | _ => throw (IO.userError "word-not fixture had nonword value")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let l ← expression table environment store left
      let r ← expression table environment store right
      match leftAt : l.value, rightAt : r.value with
      | .word x, .word y => return ⟨.word (x.sub y), l.cost + r.cost + 3, by rw [sourceAt]; exact .subtract (leftAt ▸ l.costed) (rightAt ▸ r.costed)⟩
      | _, _ => throw (IO.userError "subtraction fixture had nonword values")
  | _ => throw (IO.userError "expression outside independent source script")
termination_by sizeOf source
private structure Certificate (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost
private def certify (table : LocalNameTable) (environment : Resolved.Environment) (store : Core.Store) (body : Syntax.Block)
    (choices : List Bool) : IO (Certificate table environment store body) := do
  match sourceAt : body with
  | ⟨blockSpan, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let value ← expression table environment store initializer
      let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← certify ((name.value, id) :: table) ((id, value.value) :: environment) store ⟨blockSpan, rest⟩ choices
      return ⟨tail.value, value.cost + tail.cost + 2, by
        rw [sourceAt]; cases annotation with
        | none => exact .inferred value.costed tail.costed
        | some _ => exact .binding value.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "missing selected branch")
      let guard ← expression table environment store condition
      if agrees : guard.value = .bool choice then
        match choiceAt : choice with
        | true =>
            let tail ← certify table environment store left rest
            return ⟨tail.value, guard.cost + tail.cost + 2, by rw [sourceAt]; exact .ifTrue (by simpa only [agrees, choiceAt] using guard.costed) tail.costed⟩
        | false =>
            let tail ← certify table environment store right rest
            return ⟨tail.value, guard.cost + tail.cost + 2, by rw [sourceAt]; exact .ifFalse (by simpa only [agrees, choiceAt] using guard.costed) tail.costed⟩
      else throw (IO.userError "independent branch disagreed with actual value")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "branch script continued after bare return"
      return ⟨.unit, 1, by rw [sourceAt]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "branch script continued after return"
      let value ← expression table environment store operand
      return ⟨value.value, value.cost, by rw [sourceAt]; exact .single (.expression value.costed)⟩
  | _ => throw (IO.userError "body outside independent source script")
termination_by sizeOf body
private def observation (result : Option (Core.Ty × Core.StatefulRunResult)) (expected : TypedRuntimeArgument) (store : Core.Store) (cost fuel : Nat) : Bool :=
  match result with
  | some (type, .done value finalStore) => decide (type = expected.type ∧ value = expected.value ∧ finalStore = store ∧ cost ≤ fuel)
  | some (type, .outOfFuel state) => decide (type = expected.type ∧ state.store = store ∧ fuel < cost)
  | _ => false
private def checkCase (entry : Entry) (arguments : List TypedRuntimeArgument) (choices : List Bool) (expected : TypedRuntimeArgument) (cost : Nat) : IO Unit := do
  if matching : arguments.map (·.type) = entry.compiled.inputs.context.values.reverse then
    match preparedAt : prepareRuntimeFunction? types owner entry.source arguments with
    | none => throw (IO.userError "matching original arguments rejected")
    | some prepared =>
      let preparation := prepareRuntimeFunction?_sound preparedAt
      have _ := prepareRuntimeFunction?_factorization types owner entry.source arguments
      assertTrue (decide (prepared.core = entry.compiled.core ∧ prepared.returnType = expected.type ∧
        prepared.inputs.names = entry.compiled.inputs.names ∧ prepared.inputs.context.values = entry.compiled.inputs.context.values ∧
        prepared.inputs.bindings.length = arguments.length ∧ prepared.inputs.environment.values = arguments.reverse.map (·.value))) "branch locals leaked into parameters or argument order changed"
      for store in stores do
        let source ← certify prepared.inputs.names prepared.inputs.environment store entry.source.value.body choices
        assertTrue (decide (source.value = expected.value ∧ source.cost = cost)) "independent source value or cost differs"
        have costed := RuntimeFunctionEvaluatesWithCost.intro preparation source.costed
        have _ := costed.compiled_toSteps entry.provenance
        have _ := costed.cost_le_fuelBound
        let bound := typedLetReturnTreeFuelBound entry.source.value.body
        have _ := preparation.hasType.run_done_of_fuelBound store bound (Nat.le_refl _)
        have _ := entry.provenance.run_done_of_fuelBound arguments matching store bound (Nat.le_refl _)
        let initial := Core.State.initial entry.compiled.core (arguments.reverse.map (·.value)) store
        let run := fun fuel => runRuntimeFunction? types owner entry.source arguments fuel store
        for fuel in List.range (bound + 3) do
          have _ := entry.provenance.run_eq arguments matching fuel store
          have _ := runRuntimeFunction?_owner_eq types owner otherOwner entry.source arguments fuel store
          assertTrue (decide (run fuel = some (expected.type, Core.runStateful fuel initial) ∧
            run fuel = prepared.inputs.runTypedLetReturnTree? types owner fuel entry.source.value.body store ∧
            run fuel = runRuntimeFunction? extended owner entry.source arguments fuel store ∧
            run fuel = runRuntimeFunction? types otherOwner entry.source arguments fuel store) && observation (run fuel) expected store cost fuel)
            "entry changed exact Core, independent threshold, owner, dictionary or actual checkpoint"
          for replacement in stores do
            have _ := runRuntimeFunction?_done_store_iff types owner entry.source arguments fuel store replacement expected.type expected.value
            have _ := runRuntimeFunction?_outOfFuel_store_iff types owner entry.source arguments fuel store replacement expected.type
            assertTrue (observation (runRuntimeFunction? types owner entry.source arguments fuel replacement) expected replacement cost fuel) "own-store observation changed"
        for spent in List.range cost do
          match exhausted : run spent with
          | some (type, .outOfFuel checkpoint) =>
            if sameType : type = prepared.returnType then
              have actualOut : run spent = some (prepared.returnType, .outOfFuel checkpoint) := by simpa only [sameType] using exhausted
              have _ := costed.residual_of_outOfFuel actualOut
              if actualCore : Core.runStateful spent initial = .outOfFuel checkpoint then
                have _ := costed.compiled_residual_of_outOfFuel entry.provenance actualCore
                pure ()
              else throw (IO.userError "entry checkpoint differs from actual compiled path")
              for remaining in List.range (cost - spent + 3) do
                have _ := runRuntimeFunction?_resume exhausted remaining
                assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)) &&
                  observation (some (type, Core.runStateful remaining checkpoint)) expected store (cost - spent) remaining) "actual residual replay changed"
              let middle := (cost - spent) / 2
              let .outOfFuel next := Core.runStateful middle checkpoint | throw (IO.userError "middle checkpoint missing")
              for last in [0, cost - spent - middle - 1, cost - spent - middle, cost - spent - middle + 2] do
                assertTrue (decide (run (spent + middle + last) = some (type, Core.runStateful last next))) "three chunks lost captured branch-local values"
              if 0 < spent then assertTrue (decide (run (cost - spent) ≠ some (expected.type, .done expected.value store))) "restart was mistaken for resumption"
            else throw (IO.userError "entry changed declared result type")
          | _ => throw (IO.userError "missing genuine below-cost checkpoint")
  else throw (IO.userError "positive fixture has wrong argument types")
private def rejectArguments (entry : Entry) (arguments : List TypedRuntimeArgument) : IO Unit := do
  assertTrue (decide (arguments.map (·.type) ≠ entry.compiled.inputs.context.values.reverse)) "negative argument list unexpectedly matched"
  for store in stores do
    for fuel in [0, typedLetReturnTreeFuelBound entry.source.value.body, 60] do
      have _ := runRuntimeFunction?_factorization types owner entry.source arguments fuel store
      assertTrue ((prepareRuntimeFunction? types owner entry.source arguments).isNone && (runRuntimeFunction? types owner entry.source arguments fuel store).isNone) "wrong arity/type produced a state"
private def alternating (depth level : Nat) (annotation : String) : String × Core.Expr :=
  match depth with
  | 0 => ("return " ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";", .var (if level = 0 then 1 else 0))
  | count + 1 =>
      let (tail, core) := alternating count (level + 1) annotation
      let recursive := s!"let z{level}: {annotation}=" ++ (if level = 0 then "x" else s!"z{level - 1}") ++ ";" ++ tail
      let leaf := s!"let z{level}: {annotation}=y;return z{level};"
      let next := Core.Expr.letE (.var (if level = 0 then 1 else 0)) core
      let short := Core.Expr.letE (.var level) (.var 0)
      if level % 2 = 0 then ("if(c){" ++ recursive ++ "}else{" ++ leaf ++ "}", .ifE (.var (level + 3)) next short)
      else ("if(d){" ++ leaf ++ "}else{" ++ recursive ++ "}", .ifE (.var (level + 2)) short next)

def frontendParsedRecursiveTypedLetRuntimeEntryTests : IO Unit := do
  for depth in [1, 2, 5, 12] do
    let (body, core) := alternating depth 0 "Word"
    let entry ← compile ("function recursive(c: Bool,d: Bool,x: Word,y: Word) returns (Word){" ++ body ++ "}") core .word [.bool, .bool, .word, .word] (6 * depth + 1)
    for c in [false, true] do
      for d in [false, true] do
        let choices := if !c then [false] else if depth = 1 then [true] else if d then [true, true] else (List.range depth).map fun n => n % 2 == 0
        checkCase entry [boolArg c, boolArg d, wordArg 9, wordArg 2] choices (if c && (depth == 1 || !d) then wordArg 9 else wordArg 2)
          (if !c || depth == 1 then 7 else if d then 13 else 6 * depth + 1)
    for args in [[], [boolArg true], [wordArg 9, wordArg 2, boolArg true, boolArg false], [boolArg true, boolArg false, wordArg 9, wordArg 2, wordArg 7]] do rejectArguments entry args
  let ordered ← compile "function ordered(c: Bool,d: Bool,x: Word,y: Word) returns (Word){if(c){let z: Word=x - y;if(d){let w: Word=z;return ~w;}else{let w: Word=y - z;return w;}}else{let z: Word=y - x;return y;}}"
    (.ifE (.var 3) (.letE (.binary .wordSub (.var 1) (.var 0)) (.ifE (.var 3) (.letE (.var 0) (.unary .wordNot (.var 0)))
      (.letE (.binary .wordSub (.var 1) (.var 0)) (.var 0)))) (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 1))) .word [.bool, .bool, .word, .word] 21
  for (x, y) in [(9, 2), (2, 9), (0, Core.Word.maximum.val), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        checkCase ordered [boolArg c, boolArg d, wordArg x, wordArg y] (if c then [true, d] else [false])
          ⟨.word, .word (if c then if d then ((word x).sub (word y)).bitNot else (word y).sub ((word x).sub (word y)) else word y), .word⟩ (if c then if d then 19 else 21 else 11)
  let closure : TypedRuntimeArgument := ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, x, y) in [("Cell", (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument), ⟨.cell .word, .cellRef .word 29, .cellRef⟩),
      ("Fn", closure, ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩), ("Unit", ⟨.unit, .unit, .unit⟩, ⟨.unit, .unit, .unit⟩)] do
    let entry ← compile (s!"function opaque(c: Bool,x: {name},y: {name}) returns ({name})" ++ "{if(c){let z: " ++ name ++ "=x;if(c){let w: " ++ name ++ "=y;return z;}else{return z;}}else{let z: " ++ name ++ "=y;return z;}}")
      (.ifE (.var 2) (.letE (.var 1) (.ifE (.var 3) (.letE (.var 1) (.var 1)) (.var 0))) (.letE (.var 0) (.var 0))) x.type [.bool, x.type, y.type] 13
    for c in [false, true] do checkCase entry [boolArg c, x, y] (if c then [true, true] else [false]) (if c then x else y) (if c then 13 else 7)
  let simple ← compile "function simple(c: Bool,x: Word) returns (Word){if(c){let z: Word=x;return z;}else{return x;}}"
    (.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)) .word [.bool, .word] 7
  assertTrue (decide (typedLetReturnBodyFuelBound simple.source.value.body = 4)) "old bound changed or no longer contrasts with seven steps"
  for c in [false, true] do checkCase simple [boolArg c, wordArg 9] [c] (wordArg 9) (if c then 7 else 4)
  for store in stores do
    let env := [Core.Value.word (word 9), .bool true]
    for (spent, state) in [(2, (⟨.ret (.bool true), [.ifBranches (.letE (.var 0) (.var 0)) (.var 0) env], store⟩ : Core.State)),
        (4, ⟨.eval (.var 0) env, [.letBody (.var 0) env], store⟩), (5, ⟨.ret (.word (word 9)), [.letBody (.var 0) env], store⟩),
        (6, ⟨.eval (.var 0) (.word (word 9) :: env), [], store⟩)] do
      assertTrue (decide (runRuntimeFunction? types owner simple.source [boolArg true, wordArg 9] spent store = some (.word, .outOfFuel state))) "independent if/initializer/tail checkpoint changed"
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value, typed⟩
    cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for (name, type) in [("Opaque", Core.Ty.namedData ⟨91⟩), ("Pkg.Token", .namedData ⟨92⟩)] do
    for depth in [1, 3, 8] do
      let (body, core) := alternating depth 0 name
      let entry ← compile (s!"function nominal(c: Bool,d: Bool,x: {name},y: {name}) returns ({name})" ++ "{" ++ body ++ "}") core type [.bool, .bool, type, type] (6 * depth + 1)
      for value in [wordArg 9, boolArg true, closure, (⟨.cell .word, .cellRef .word 17, .cellRef⟩ : TypedRuntimeArgument)] do rejectArguments entry [boolArg true, boolArg false, value, value]
  let closedBody := "{if(0==0){let z: Word=7;return z;}else{return 7;}}"
  for header in ["function generic<T>() returns (Word)", "function many() returns (Word,Bool)", "function empty() returns ()",
      "function unknown() returns (Unknown)", "function duplicate(x: Word,x: Bool) returns (Word)",
      "function staged(comptime x: Word) returns (Word)", "function unknownParameter(x: Unknown) returns (Word)",
      "function wrong() returns (Bool)", "function absent()"] do
    let some source ← parsed? (header ++ closedBody) | throw (IO.userError "negative header failed to parse")
    assertTrue (decide (LocalInputs.empty.checkTypedLetReturnTree? types owner source.value.body =
      some (.ifE (.binary .wordEq (.word .zero) (.word .zero)) (.letE (.word (word 7)) (.var 0)) (.word (word 7)), .word)) &&
      (compileRuntimeFunction? types owner source).isNone) "header rejection lost its independently valid recursive body"
    for args in [[], [wordArg 9], [wordArg 9, boolArg true]] do
      for store in stores do
        for fuel in [0, 11, 60] do
          assertTrue ((prepareRuntimeFunction? types owner source args).isNone &&
            (runRuntimeFunction? types owner source args fuel store).isNone) "invalid header, parameter or return contract acquired execution"
  let some invalid ← parsed? "function hidden(c: Bool,x: Word) returns (Word){if(c){let z: Word=x;return z;}else{let z: Unknown=x;return z;}}"
    | throw (IO.userError "raw-versus-whole contrast failed to parse")
  let some actual := bindRuntimeParameters? types owner invalid.value.signature.parameters.elements [boolArg true, wordArg 9]
    | throw (IO.userError "raw-versus-whole contrast had invalid parameters")
  for store in stores do
    let raw ← certify actual.names actual.environment store invalid.value.body [true]
    assertTrue (decide (raw.value = .word (word 9) ∧ raw.cost = 7) && (compileRuntimeFunction? types owner invalid).isNone &&
      (runRuntimeFunction? types owner invalid [boolArg true, wordArg 9] 7 store).isNone) "selected raw success hid an invalid unselected annotation"
  let inferred ← compile "function invalid(c: Bool,x: Word) returns (Word){if(c){let z=x;return z;}else{return x;}}"
    (.ifE (.var 1) (.letE (.var 0) (.var 0)) (.var 0)) .word [.bool, .word] 7
  for c in [false, true] do checkCase inferred [boolArg c, wordArg 9] [c] (wordArg 9) (if c then 7 else 4)
  for body in ["{if(c){let z: Word;return x;}else{return x;}}",
      "{if(c){let z: Unknown=x;return x;}else{return x;}}", "{if(c){let z: Bool=x;return x;}else{return x;}}", "{if(c){let x: Word=x;return x;}else{return x;}}",
      "{if(c){let z: Word=z;return x;}else{return x;}}", "{if(c){let z: Word=x;return z;}else{return z;}}",
      "{if(c){let z: Word=x;return z;}else{if(c){return x;}else{return missing;}}}", "{if(c){let z: Word=x;return z;}else{return c;}}",
      "{if(x){let z: Word=x;return z;}else{return x;}}", "{if(c){let z: Word=x;return z;}}", "{if(c){return x;}else{return x;}return x;}", "{}"] do
    let some source ← parsed? ("function invalid(c: Bool,x: Word) returns (Word)" ++ body) | throw (IO.userError "negative body failed to parse")
    assertTrue (decide (interpretRuntimeFunctionHeader? types source.value.signature = some .word) &&
      (bindRuntimeParameters? types owner source.value.signature.parameters.elements [boolArg true, wordArg 9]).isSome &&
      (compileRuntimeFunction? types owner source).isNone) "whole invalid source was accepted or had a bad header/parameters"
    for store in stores do
      for fuel in [0, typedLetReturnTreeFuelBound source.value.body, 60] do
        assertTrue ((runRuntimeFunction? types owner source [boolArg true, wordArg 9] fuel store).isNone) "invalid unselected child acquired execution"
  for content in ["function missing(x){if(x){return;}else{return;}}", "function incomplete(){if(0==0){let z: Word=;return z;}else{return 7;}}",
      "function incomplete(){if(0==0){return 7;}else{return 7;}", "function trailing(){return;} trailing"] do
    assertTrue (← parsed? content).isNone "incomplete source acquired entry meaning"

end Tests
end
