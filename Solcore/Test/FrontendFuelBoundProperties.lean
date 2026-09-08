import Solcore.Frontend.RuntimeFunctionFuelBoundProperties

/-! Independent cost derivations distinguish sufficient structural budgets from
exact path costs, and never treat an unsupported zero-bound expression as checked. -/

set_option autoImplicit false

namespace Tests.FrontendFuelBound

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FuelBound", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "fuel-bound.sol"⟩, 13, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def unary (operator : Syntax.UnaryOp) (child : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .unary ⟨span, operator⟩ child⟩
private def binary (operator : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, operator⟩ right⟩
private def names : LocalNameTable := [("c", ⟨owner, 0⟩), ("x", ⟨owner, 1⟩), ("y", ⟨owner, 2⟩)]
private def environment (choice : Bool) (left right : Core.Word) : Resolved.Environment :=
  [(⟨owner, 0⟩, .bool choice), (⟨owner, 1⟩, .word left), (⟨owner, 2⟩, .word right)]
private theorem choiceCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "c") (.bool choice) store 1 := .identifier .head .head
private theorem leftCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "x") (.word left) store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem rightCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "y") (.word right) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))

theorem leaf_spelling_spans_and_grouping_add_no_core_budget
    (literal : Syntax.CoreLiteral) (outer inner : Syntax.SourceSpan) (source : Syntax.Expr) :
    localExpressionFuelBound ⟨outer, .literal literal⟩ = 1 ∧
    localExpressionFuelBound ⟨outer, .group ⟨inner, .group source⟩⟩ = localExpressionFuelBound source ∧
    localExpressionFuelBound (ref "missing") = 1 := by
  simp [localExpressionFuelBound, ref]

theorem independently_denoted_literals_and_both_unaries_fit
    (literal : Syntax.CoreLiteral) (word : Core.Word) (meaning : WordLiteralDenotes literal word)
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      ⟨span, .group ⟨span, .literal literal⟩⟩ (.word word) store 1 ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .logicalNot (ref "c")) (.bool (!choice)) store 3 ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .bitNot (ref "x")) (.word left.bitNot) store 3 ∧
    1 ≤ localExpressionFuelBound ⟨span, .group ⟨span, .literal literal⟩⟩ ∧
    3 ≤ localExpressionFuelBound (unary .logicalNot (ref "c")) ∧
    3 ≤ localExpressionFuelBound (unary .bitNot (ref "x")) := by
  have literalCost : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      ⟨span, .group ⟨span, .literal literal⟩⟩ (.word word) store 1 := .group (.wordLiteral meaning)
  have negated : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .logicalNot (ref "c")) (.bool (!choice)) store 3 := .logicalNot (choiceCost choice left right store)
  have complemented : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .bitNot (ref "x")) (.word left.bitNot) store 3 := .bitNot (leftCost choice left right store)
  exact ⟨literalCost, negated, complemented, literalCost.cost_le_fuelBound,
    negated.cost_le_fuelBound, complemented.cost_le_fuelBound⟩

private inductive StrictOp where
  | add | subtract | multiply | bitAnd | bitOr | bitXor | greater
private def operator : StrictOp → Syntax.BinaryOp
  | .add => .add | .subtract => .subtract | .multiply => .multiply
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor | .greater => .greater
private def result (kind : StrictOp) (left right : Core.Word) : Core.Value :=
  match kind with
  | .add => .word (left.add right) | .subtract => .word (left.sub right)
  | .multiply => .word (left.mul right) | .bitAnd => .word (left.bitAnd right)
  | .bitOr => .word (left.bitOr right) | .bitXor => .word (left.bitXor right)
  | .greater => .bool (decide (left > right))

theorem every_strict_word_operator_has_independent_cost_and_bound_five
    (kind : StrictOp) (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (binary (operator kind) (ref "x") (ref "y")) (result kind left right) store 5 ∧
    5 ≤ localExpressionFuelBound (binary (operator kind) (ref "x") (ref "y")) ∧
    localExpressionFuelBound (binary (operator kind) (ref "x") (ref "y")) = 5 := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (binary (operator kind) (ref "x") (ref "y")) (result kind left right) store 5 := by
    cases kind
    · exact .add (leftCost choice left right store) (rightCost choice left right store)
    · exact .subtract (leftCost choice left right store) (rightCost choice left right store)
    · exact .multiply (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitAnd (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitOr (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitXor (leftCost choice left right store) (rightCost choice left right store)
    · exact .greater (leftCost choice left right store) (rightCost choice left right store)
  refine ⟨evaluated, evaluated.cost_le_fuelBound, ?_⟩
  cases kind <;> simp [binary, operator, ref, localExpressionFuelBound]

private def shortCircuit (operator : Syntax.BinaryOp) := binary operator (ref "c") (unary .logicalNot (ref "c"))
private theorem andCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalAnd) (.bool false) store (if choice then 6 else 4) := by
  cases choice
  · exact .andFalse (choiceCost false left right store)
  · exact .andTrue (choiceCost true left right store) (.logicalNot (choiceCost true left right store))
private theorem orCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalOr) (.bool true) store (if choice then 4 else 6) := by
  cases choice
  · exact .orFalse (choiceCost false left right store) (.logicalNot (choiceCost false left right store))
  · exact .orTrue (choiceCost true left right store)

theorem boolean_paths_have_value_dependent_costs_but_shared_sufficient_bounds
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalAnd) (.bool false) store (if choice then 6 else 4) ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalOr) (.bool true) store (if choice then 4 else 6) ∧
    (if choice then 6 else 4) ≤ localExpressionFuelBound (shortCircuit .logicalAnd) ∧
    (if choice then 4 else 6) ≤ localExpressionFuelBound (shortCircuit .logicalOr) ∧
    localExpressionFuelBound (shortCircuit .logicalAnd) = 6 ∧
    localExpressionFuelBound (shortCircuit .logicalOr) = 6 := by
  refine ⟨andCost choice left right store, orCost choice left right store,
    (andCost choice left right store).cost_le_fuelBound,
    (orCost choice left right store).cost_le_fuelBound, ?_, ?_⟩ <;>
    simp [shortCircuit, binary, unary, ref, localExpressionFuelBound]

private def conditional : Syntax.Expr :=
  ⟨span, .conditional (ref "c") span (binary .multiply (ref "x") (ref "y")) span (ref "x")⟩
private theorem conditionalCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store conditional
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) := by
  cases choice
  · exact .ifFalse (choiceCost false left right store) (leftCost false left right store)
  · exact .ifTrue (choiceCost true left right store)
      (every_strict_word_operator_has_independent_cost_and_bound_five .multiply true left right store).1

theorem conditional_bound_is_conservative_not_the_selected_path_minimum
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store conditional
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) ∧
    (if choice then 8 else 4) ≤ localExpressionFuelBound conditional ∧
    localExpressionFuelBound conditional = 8 ∧ 4 < localExpressionFuelBound conditional := by
  refine ⟨conditionalCost choice left right store,
    (conditionalCost choice left right store).cost_le_fuelBound, ?_, ?_⟩ <;>
    simp [conditional, binary, ref, localExpressionFuelBound]

private def unsupported : Syntax.Expr := ⟨span, .call (ref "missing") ⟨span, []⟩⟩

theorem inserted_boolean_constant_requires_positive_budget_when_skipping_unsupported_source
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment false left right) store
      (binary .logicalAnd (ref "c") unsupported) (.bool false) store 4 ∧
    localExpressionFuelBound unsupported = 0 ∧
    localExpressionFuelBound (binary .logicalAnd (ref "c") unsupported) = 4 ∧
    4 ≤ localExpressionFuelBound (binary .logicalAnd (ref "c") unsupported) ∧
    resolveLocalExpression? names (binary .logicalAnd (ref "c") unsupported) = none := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment false left right) store
      (binary .logicalAnd (ref "c") unsupported) (.bool false) store 4 :=
    .andFalse (choiceCost false left right store)
  refine ⟨evaluated, ?_, ?_, evaluated.cost_le_fuelBound, ?_⟩
  · simp [unsupported, localExpressionFuelBound]
  · simp [binary, ref, unsupported, localExpressionFuelBound]
  · simp [binary, ref, unsupported, resolveLocalExpression?, names, LocalNameTable.lookup?]

private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩

theorem singleton_return_inherits_the_bound_without_a_wrapper_cost
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost names (environment choice left right) store (body conditional)
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) ∧
    (if choice then 8 else 4) ≤ returnBodyFuelBound (body conditional) ∧
    returnBodyFuelBound ⟨span, [⟨span, .returnStmt none⟩]⟩ = 1 ∧
    returnBodyFuelBound ⟨span, []⟩ = 0 := by
  have evaluated : ReturnBodyEvaluatesWithCost names (environment choice left right) store (body conditional)
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) :=
    .expression (conditionalCost choice left right store)
  exact ⟨evaluated, evaluated.cost_le_fuelBound, rfl, rfl⟩

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
private def inputs (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem preparation (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    RuntimeFunctionPrepares (types type) owner declaration [argument type value typed]
      ⟨inputs type value typed, .var 0, type⟩ :=
  ⟨(compilation type).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    (compilation type).body⟩

theorem checked_local_and_return_endpoints_finish_with_the_same_structural_budget
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (enough : 1 ≤ fuel) :
    (∃ result, Core.ValueHasType result type ∧
      (inputs type value typed).run? fuel (ref "x") store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧
      (inputs type value typed).runReturnBody? fuel (body (ref "x")) store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧
      Core.runStateful fuel (Core.State.initial (.var 0) [value] store) = .done result store) := by
  have localTyped : LocalExpressionHasType (inputs type value typed).names
      (inputs type value typed).context (ref "x") type := .identifier .head .head
  have localChecked : elaborateLocalExpression? (inputs type value typed).names
      (inputs type value typed).context (ref "x") = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have localEnough : localExpressionFuelBound (ref "x") ≤ fuel := by
    simpa [ref, localExpressionFuelBound] using enough
  have bodyEnough : returnBodyFuelBound (body (ref "x")) ≤ fuel := localEnough
  have localRun := elaborateLocalExpression?_run_done_of_fuelBound localChecked
    (inputs type value typed).sameIds (inputs type value typed).environmentTyped store fuel localEnough
  have bodyElaboration : ReturnBodyElaborates (inputs type value typed).names
      (inputs type value typed).context (body (ref "x")) (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have bodyRun := elaborateReturnBody?_run_done_of_fuelBound bodyElaboration.complete
    (inputs type value typed).sameIds (inputs type value typed).environmentTyped store fuel bodyEnough
  obtain ⟨localResult, _, localDone⟩ := localRun
  obtain ⟨bodyResult, bodyResultTyped, bodyDone⟩ := bodyRun
  have sameResult : localResult = bodyResult := by
    have same := localDone.symm.trans bodyDone
    exact (Core.StatefulRunResult.done.inj same).1
  refine ⟨LocalInputs.run?_done_of_fuelBound localTyped store fuel localEnough,
    LocalInputs.runReturnBody?_done_of_fuelBound (.expression localTyped) store fuel bodyEnough,
    localResult, ?_, localDone⟩
  exact sameResult ▸ bodyResultTyped

theorem independently_compiled_identity_uses_only_its_actual_typed_argument
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (enough : 1 ≤ fuel) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 ∧ 1 ≤ terminalReturnTreeFuelBound declaration.value.body ∧
    (∃ result, Core.ValueHasType result type ∧ runRuntimeFunction? (types type) owner declaration
      [argument type value typed] fuel store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧ runRuntimeFunction? (types type) owner declaration
      [argument type value typed] fuel store = some (type, .done result store) ∧
      Core.runStateful fuel (Core.State.initial (.var 0) [value] store) = .done result store) := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 := .intro (preparation type value typed) (.single <| .expression (.identifier .head .head))
  have bounded : terminalReturnTreeFuelBound declaration.value.body ≤ fuel := by
    simpa [declaration, body, terminalReturnTreeFuelBound, returnBodyFuelBound, ref, localExpressionFuelBound] using enough
  exact ⟨evaluated, evaluated.cost_le_fuelBound,
    (preparation type value typed).hasType.run_done_of_fuelBound store fuel bounded,
    (compilation type).run_done_of_fuelBound [argument type value typed] rfl store fuel bounded⟩

end Tests.FrontendFuelBound
