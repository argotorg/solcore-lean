import Solcore.Frontend.RuntimeFunctionEvaluatorProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties

/-! Original declarations and actual arguments, independently justified before
the direct triple is reflected back into the established machine contracts. -/
set_option autoImplicit false
namespace Tests.FrontendRuntimeFunctionEvaluator
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DirectEntry", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "direct-entry.sol"⟩, 225, 9⟩
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
private def entry (body : Syntax.Block) (result : String := "Payload") (exposed : Bool := false) : Syntax.FunctionDecl := ⟨span,
  ⟨⟨span, ⟨span, "tree"⟩, none, ⟨span, parameters⟩, ⟨if exposed then some span else none, none⟩, some ⟨span, ⟨span, [named result]⟩⟩, none⟩, body⟩⟩
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
        (show TypeNameDenotes (types type) (named "Payload") type from .named .head) (fresh name (by simp)) resolution lowered typing
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

private theorem computed {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    evaluateRuntimeFunctionWithCost? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some (type, actual.val, 10 * names.length + 1) :=
  (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (costed names flag actual [] distinct fresh)).2

theorem arbitrary_fresh_depth_retains_independent_provenance_and_original_arguments
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) :
    RuntimeFunctionCompiles (types type) owner (entry (tree names "seed")) (compiled names type) ∧
    prepareRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some ⟨inputs flag actual, core names.length, type⟩ ∧
    (inputs flag actual).bindings.length = 2 ∧
    (inputs flag actual).environment.values = [actual.val, .bool flag] ∧
    evaluateRuntimeFunctionWithCost? (types type) owner (entry (tree names "seed")) (arguments flag actual) =
      some (type, actual.val, 10 * names.length + 1) :=
  ⟨compilation names type distinct fresh, (preparation names flag actual distinct fresh).complete,
    rfl, rfl, computed names flag actual distinct fresh⟩

theorem direct_results_recover_compiled_paths_and_every_fuel_threshold
    {type : Core.Ty} (names : List String) (flag : Bool) (actual : Actual type)
    (distinct : names.Nodup) (fresh : ∀ name ∈ names, name ∉ ["seed", "flag"]) (store : Core.Store) (fuel : Nat) :
    Core.Steps (10 * names.length + 1) (Core.State.initial (core names.length) [actual.val, .bool flag] store)
      (Core.State.final actual.val store) ∧
    (runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual) fuel store =
      some (type, .done actual.val store) ↔ 10 * names.length + 1 ≤ fuel) ∧
    ((∃ checkpoint, runRuntimeFunction? (types type) owner (entry (tree names "seed")) (arguments flag actual)
      fuel store = some (type, .outOfFuel checkpoint)) ↔ fuel < 10 * names.length + 1) ∧
    10 * names.length + 1 ≤ typedLetReturnTreeFuelBound (tree names "seed") := by
  have recovered := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store)).mpr
    ⟨rfl, computed names flag actual distinct fresh⟩
  exact ⟨recovered.compiled_toSteps (compilation names type distinct fresh),
    recovered.run_done_iff, recovered.run_outOfFuel_iff, recovered.cost_le_fuelBound⟩

theorem store_free_triples_do_not_license_a_changed_final_store
    {type : Core.Ty} (actual : Actual type) (initialStore finalStore : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner (entry (tree ["x", "y"] "seed"))
      (arguments false actual) initialStore type actual.val finalStore 21 ↔ finalStore = initialStore := by
  rw [runtimeFunctionEvaluatesWithCost_iff_evaluate, computed ["x", "y"] false actual (by decide) (by decide)]
  simp

theorem nominal_compilation_cannot_supply_an_actual_parameter (nominal : Core.DataTypeId) :
    compileRuntimeFunction? (types (.namedData nominal)) owner (entry (tree ["x"] "seed")) =
      some (compiled ["x"] (.namedData nominal)) ∧
    ¬ ∃ argument : TypedRuntimeArgument, argument.type = .namedData nominal := by
  refine ⟨(compilation _ _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨⟨type, value, typed⟩, same⟩; cases same
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_opaque_cells_and_captured_functions_need_no_effects (location : Core.Location) (word : Core.Word) :
    evaluateRuntimeFunctionWithCost? (types (.cell .word)) owner (entry (tree ["x", "y"] "seed"))
      (arguments true ⟨.cellRef .word location, .cellRef⟩) = some (.cell .word, .cellRef .word location, 21) ∧
    evaluateRuntimeFunctionWithCost? (types (.function .bool .word)) owner (entry (tree ["x", "y"] "seed"))
      (arguments false ⟨.closure .bool .word (.var 1) [.word word], .closure (.cons .word .nil) (.var rfl)⟩) =
      some (.function .bool .word, .closure .bool .word (.var 1) [.word word], 21) :=
  ⟨computed _ _ _ (by decide) (by decide), computed _ _ _ (by decide) (by decide)⟩

theorem same_typed_core_is_not_independent_compilation (type : Core.Ty) :
    Core.HasType [type, .bool] (.var 0) type ∧
    ¬ RuntimeFunctionCompiles (types type) owner (entry (tree ["x"] "seed"))
      { compiled ["x"] type with core := .var 0 } := by
  refine ⟨.var rfl, ?_⟩
  intro forged
  have wrong := congrArg CompiledRuntimeFunction.core
    (forged.result_unique (compilation ["x"] type (by decide) (by decide)))
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

theorem direct_triples_pay_for_ordered_and_unused_work (flag : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩) =
      some (.word, .word (if flag then Core.Word.zero.sub word else word), if flag then 11 else 13) ∧
    (runRuntimeFunction? (types .word) owner (entry mathBody) (arguments flag ⟨.word word, .word⟩) fuel store =
      some (.word, .done (.word (if flag then Core.Word.zero.sub word else word)) store) ↔ (if flag then 11 else 13) ≤ fuel) := by
  have result := (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (mathCost flag word store)).2
  exact ⟨result, (runtimeFunctionEvaluatesWithCost_iff_evaluate.mpr ⟨rfl, result⟩).run_done_iff⟩
private def checkpoint (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word word), [.binaryApply .wordSub (.word .zero), .letBody (.var 0) [.word word, .bool true]], store⟩

theorem actual_pending_initializer_supports_arbitrary_resumption (word : Core.Word) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) 8 store =
      some (.word, .outOfFuel (checkpoint word store)) ∧
    Core.Steps 3 (checkpoint word store) (Core.State.final (.word (Core.Word.zero.sub word)) store) ∧
    Core.runStateful 1 (checkpoint word store) =
      .outOfFuel ⟨.ret (.word (Core.Word.zero.sub word)), [.letBody (.var 0) [.word word, .bool true]], store⟩ ∧
    Core.runStateful 2 ⟨.ret (.word (Core.Word.zero.sub word)), [.letBody (.var 0) [.word word, .bool true]], store⟩ =
      .done (.word (Core.Word.zero.sub word)) store ∧
    Core.runStateful 3 (checkpoint word store) = .done (.word (Core.Word.zero.sub word)) store ∧
    Core.runStateful 0 { checkpoint word store with continuation := [] } = .done (.word word) store ∧
    runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) (8 + additional) store =
      some (.word, Core.runStateful additional (checkpoint word store)) := by
  have suspended : runRuntimeFunction? (types .word) owner (entry mathBody) (arguments true ⟨.word word, .word⟩) 8 store =
      some (.word, .outOfFuel (checkpoint word store)) := by rw [mathCompilation.run_eq _ rfl]; rfl
  have recovered := (runtimeFunctionEvaluatesWithCost_iff_evaluate (initialStore := store)).mpr
    ⟨rfl, (runtimeFunctionEvaluatesWithCost_iff_evaluate.mp (mathCost true word store)).2⟩
  exact ⟨suspended, (recovered.residual_of_outOfFuel suspended).2, rfl, rfl, rfl, rfl, runRuntimeFunction?_resume suspended additional⟩

private theorem rejectArguments (args : List TypedRuntimeArgument) (wrong : args.map (·.type) ≠ [.bool, .word]) :
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed")) args = none := by
  apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨prepared, preparation⟩
  have same := preparation.compiles.result_unique (compilation ["x"] .word (by decide) (by decide))
  exact wrong (runtimeFunctionPrepares_toCompiled_iff.mp ⟨prepared, preparation, same⟩).2

theorem raw_success_does_not_bypass_headers_return_contracts_or_unused_arguments (word : Core.Word) :
    evaluateTypedLetReturnTreeWithCost? owner (inputs true ⟨.word word, .word⟩).names
      (inputs true ⟨.word word, .word⟩).environment (tree ["x"] "seed") = some (.word word, 11) ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed") "Payload" true)
      (arguments true ⟨.word word, .word⟩) = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed") "Flag")
      (arguments true ⟨.word word, .word⟩) = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed"))
      [⟨.word, .word .zero, .word⟩, ⟨.word, .word word, .word⟩] = none ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry (tree ["x"] "seed")) [] = none := by
  refine ⟨evaluateTypedLetReturnTreeWithCost?_complete (treeCost ["x"] "seed" _ _ (.word word) [] (.identifier .head .head)),
    evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr rfl, ?_, rejectArguments _ (by simp), rejectArguments _ (by simp)⟩
  apply evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr
  apply prepareRuntimeFunction?_eq_none_iff.mpr
  rintro ⟨prepared, preparation⟩
  have same := preparation.parameters.result_unique (boundArguments true ⟨.word word, .word⟩)
  have body := preparation.body
  rw [same] at body
  have declaredBool : RuntimeFunctionHeader (types .word) (entry (tree ["x"] "seed") "Flag").value.signature .bool :=
    ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
  have expected := (compilation ["x"] .word (by decide) (by decide)).body
  have impossible := (expected.result_unique body).2.trans (declaredBool.type_unique preparation.header).symm
  cases impossible

private def unknownArm := branch (ref "flag") (returned "seed")
  ⟨span, [⟨span, .letDecl ⟨span, "x"⟩ (some (named "Unknown")) (some (ref "seed"))⟩, ⟨span, .returnStmt (some (ref "x"))⟩]⟩
theorem direct_body_short_circuiting_does_not_remove_the_unselected_entry_contract (word : Core.Word) :
    evaluateTypedLetReturnTreeWithCost? owner (inputs true ⟨.word word, .word⟩).names
      (inputs true ⟨.word word, .word⟩).environment unknownArm = some (.word word, 4) ∧
    evaluateRuntimeFunctionWithCost? (types .word) owner (entry unknownArm) (arguments true ⟨.word word, .word⟩) = none := by
  refine ⟨?_, evaluateRuntimeFunctionWithCost?_eq_none_iff.mpr (prepareRuntimeFunction?_eq_none_iff.mpr ?_)⟩
  · apply evaluateTypedLetReturnTreeWithCost?_complete (initialStore := ([] : Core.Store))
    apply TypedLetReturnTreeEvaluatesWithCost.ifTrue (conditionCost := 1) (branchCost := 1)
    · exact .identifier (.tail (by change "seed" ≠ "flag"; decide) .head)
        (.tail (by change (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩; decide) .head)
    · exact .single (.expression (.identifier .head .head))
  · rintro ⟨⟨targetInputs, targetCore, targetType⟩, preparation⟩
    cases preparation.body with
    | single child => cases child
    | conditional _ _ _ _ invalid =>
      cases invalid with
      | single child => cases child
      | binding meaning _ _ _ _ _ =>
        have impossible := meaning.complete
        change none = some _ at impossible
        cases impossible

end Tests.FrontendRuntimeFunctionEvaluator
