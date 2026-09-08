import Solcore.Frontend.RuntimeFunctionStoreProperties

/-! Independent source derivations replay on arbitrary stores. Whole contracts,
actual values, per-store results, and effectful Core remain separate boundaries. -/

set_option autoImplicit false

namespace Tests.FrontendStoreIndependence

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"StoreIndependence", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "store-independence.sol"⟩, 9, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def names : LocalNameTable := [("x", ⟨owner, 0⟩)]
private def environment (value : Core.Value) : Resolved.Environment := [(⟨owner, 0⟩, value)]
private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩

theorem arbitrary_values_replay_without_typing_or_allocation
    (value : Core.Value) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment value) replacement (ref "x") value replacement 1 ∧
    LocalExpressionEvaluates names (environment value) replacement (ref "x") value replacement ∧
    (LocalExpressionEvaluatesWithCost names (environment value) first (ref "x") value first 1 ↔
      first = first ∧ LocalExpressionEvaluatesWithCost names (environment value)
        replacement (ref "x") value replacement 1) ∧
    (LocalExpressionEvaluates names (environment value) first (ref "x") value first ↔
      first = first ∧ LocalExpressionEvaluates names (environment value)
        replacement (ref "x") value replacement) := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment value) first (ref "x") value first 1 :=
    .identifier .head .head
  exact ⟨evaluated.change_store replacement, evaluated.erase.change_store replacement,
    localExpressionEvaluatesWithCost_store_iff, localExpressionEvaluates_store_iff⟩

private def skipped : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .logicalAnd⟩ (ref "missing")⟩

theorem skipped_invalid_branch_replays_but_still_fails_whole_resolution
    (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment (.bool false))
      replacement skipped (.bool false) replacement 4 ∧
    ReturnBodyEvaluates names (environment (.bool false)) replacement (body skipped) (.bool false) replacement ∧
    ReturnBodyEvaluatesWithCost names (environment (.bool false))
      replacement (body skipped) (.bool false) replacement 4 ∧
    resolveLocalExpression? names skipped = none := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment (.bool false))
      first skipped (.bool false) first 4 := .andFalse (.identifier .head .head)
  have rawBody : ReturnBodyEvaluates names (environment (.bool false)) first (body skipped) (.bool false) first :=
    .expression evaluated.erase
  have costBody : ReturnBodyEvaluatesWithCost names (environment (.bool false))
      first (body skipped) (.bool false) first 4 := .expression evaluated
  refine ⟨evaluated.change_store replacement, rawBody.change_store replacement,
    costBody.change_store replacement, ?_⟩
  simp [skipped, ref, resolveLocalExpression?, names, LocalNameTable.lookup?]

theorem bare_return_replays_with_one_transition (first replacement : Core.Store) :
    ReturnBodyEvaluates names (environment .unit) replacement ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit replacement ∧
    ReturnBodyEvaluatesWithCost names (environment .unit) replacement
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit replacement 1 := by
  have raw : ReturnBodyEvaluates names (environment .unit) first
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit first := .bare
  have costed : ReturnBodyEvaluatesWithCost names (environment .unit) first
      ⟨span, [⟨span, .returnStmt none⟩]⟩ .unit first 1 := .bare
  exact ⟨raw.change_store replacement, costed.change_store replacement⟩

private def branchNames : LocalNameTable := [("c", ⟨owner, 0⟩), ("x", ⟨owner, 1⟩)]
private def branchEnvironment (choice : Bool) (value : Core.Word) : Resolved.Environment :=
  [(⟨owner, 0⟩, .bool choice), (⟨owner, 1⟩, .word value)]
private def product : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .multiply⟩ (ref "x")⟩
private def branch : Syntax.Expr := ⟨span, .conditional (ref "c") span product span (ref "x")⟩
private theorem branchCost (choice : Bool) (value : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) store branch
      (.word (if choice then value.mul value else value)) store (if choice then 8 else 4) := by
  have leaf : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value)
      store (ref "x") (.word value) store 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have condition : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value)
      store (ref "c") (.bool choice) store 1 := .identifier .head .head
  cases choice
  · exact .ifFalse condition leaf
  · have multiplied : LocalExpressionEvaluatesWithCost branchNames (branchEnvironment true value)
        store product (.word (value.mul value)) store 5 :=
      .multiply (leftValue := value) (rightValue := value) (leftCost := 1) (rightCost := 1) leaf leaf
    exact .ifTrue condition multiplied

theorem conditional_arithmetic_keeps_its_selected_cost_across_stores
    (choice : Bool) (value : Core.Word) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) first branch
      (.word (if choice then value.mul value else value)) first (if choice then 8 else 4) ∧
    LocalExpressionEvaluatesWithCost branchNames (branchEnvironment choice value) replacement branch
      (.word (if choice then value.mul value else value)) replacement (if choice then 8 else 4) :=
  ⟨branchCost choice value first, (branchCost choice value first).change_store replacement⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "T"⟩, []⟩⟩⟩ none⟩
private def parameter : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, "x"⟩ annotation⟩
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "identity"⟩, none, ⟨span, [parameter]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation]⟩⟩, none⟩, body (ref "x")⟩⟩
private def types (type : Core.Ty) : TypeNameTable := [(["T"], type)]
private def argument (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    TypedRuntimeArgument := ⟨type, value, typed⟩
private def compiled (type : Core.Ty) : CompiledRuntimeFunction :=
  ⟨LocalTypeInputs.empty.bindFresh owner "x" type, .var 0, type⟩
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private def prepared (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    PreparedRuntimeFunction := ⟨LocalInputs.empty.bindFresh owner "x" type value typed, .var 0, type⟩
private theorem identityCost (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) : RuntimeFunctionEvaluatesWithCost (types type) owner declaration
      [argument type value typed] store type value store 1 := by
  have preparation : RuntimeFunctionPrepares (types type) owner declaration
      [argument type value typed] (prepared type value typed) :=
    ⟨(compilation type).header,
      .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type).body⟩
  exact .intro preparation (.terminal <| .single <| .expression (.identifier .head .head))

theorem independently_prepared_identity_keeps_value_type_and_exact_cost
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (first replacement : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration
      [argument type value typed] replacement type value replacement 1 ∧
    (RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      first type value first 1 ↔ first = first ∧ RuntimeFunctionEvaluatesWithCost (types type) owner declaration
        [argument type value typed] replacement type value replacement 1) :=
  ⟨(identityCost type value typed first).change_store replacement, runtimeFunctionEvaluatesWithCost_store_iff⟩

theorem same_fuel_preserves_terminal_and_exhaustion_observations_not_stores
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (fuel : Nat) (first replacement : Core.Store) :
    (runRuntimeFunction? (types type) owner declaration [argument type value typed] fuel first =
      some (type, .done value first) ↔ runRuntimeFunction? (types type) owner declaration
        [argument type value typed] fuel replacement = some (type, .done value replacement)) ∧
    ((∃ state, runRuntimeFunction? (types type) owner declaration [argument type value typed]
        fuel first = some (type, .outOfFuel state)) ↔
      (∃ state, runRuntimeFunction? (types type) owner declaration [argument type value typed]
        fuel replacement = some (type, .outOfFuel state))) ∧
    (Core.runStateful fuel (Core.State.initial (.var 0) [value] first) = .done value first ↔
      Core.runStateful fuel (Core.State.initial (.var 0) [value] replacement) = .done value replacement) ∧
    ((∃ state, Core.runStateful fuel (Core.State.initial (.var 0) [value] first) = .outOfFuel state) ↔
      (∃ state, Core.runStateful fuel (Core.State.initial (.var 0) [value] replacement) = .outOfFuel state)) :=
  ⟨runRuntimeFunction?_done_store_iff _ _ _ _ _ _ _ _ _,
    runRuntimeFunction?_outOfFuel_store_iff _ _ _ _ _ _ _ _,
    (compilation type).compiled_done_store_iff [argument type value typed] rfl fuel first replacement value,
    (compilation type).compiled_outOfFuel_store_iff [argument type value typed] rfl fuel first replacement⟩

theorem distinct_stores_prevent_literal_result_equality
    (value : Core.Value) (first replacement : Core.Store) (different : first ≠ replacement) :
    Core.runStateful 0 (Core.State.initial (.var 0) [value] first) ≠
      Core.runStateful 0 (Core.State.initial (.var 0) [value] replacement) ∧
    Core.runStateful 1 (Core.State.initial (.var 0) [value] first) ≠
      Core.runStateful 1 (Core.State.initial (.var 0) [value] replacement) := by
  constructor
  · intro same
    exact different (congrArg Core.State.store (Core.StatefulRunResult.outOfFuel.inj same))
  · intro same
    exact different (Core.StatefulRunResult.done.inj same).2

theorem reading_core_can_preserve_each_store_but_return_different_values
    (left right : Core.Word) (different : left ≠ right) :
    Core.runStateful 3 (Core.State.initial (.loadCell (.var 0)) [.cellRef .word 0] [.word left]) =
      .done (.word left) [.word left] ∧
    Core.runStateful 3 (Core.State.initial (.loadCell (.var 0)) [.cellRef .word 0] [.word right]) =
      .done (.word right) [.word right] ∧ Core.Value.word left ≠ .word right :=
  ⟨rfl, rfl, fun same => different (Core.Value.word.inj same)⟩

end Tests.FrontendStoreIndependence
