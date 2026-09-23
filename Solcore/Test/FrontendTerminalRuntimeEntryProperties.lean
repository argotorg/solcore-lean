import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TerminalReturnTree
import Solcore.Frontend.TerminalReturnBody

/-! Independent terminal-entry contracts use actual arguments, unequal selected
costs and real suspended environments. Static compilation invents no values. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalRuntimeEntry

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-entry.sol"⟩, 7, 31⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalEntry", by decide⟩], by decide⟩⟩, 0⟩
private def id (index : Nat) : Resolved.LocalId := ⟨owner, index⟩
private def annotation (name : String) : Syntax.TypeExpr :=
  ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name type : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation type)⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def yes := returned ⟨span, .unary ⟨span, .bitNot⟩ (ref "t")⟩
private def branch (no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def body := branch (returned (ref "f"))
private def declaration (source : Syntax.Block) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "choose"⟩, none,
    ⟨span, [parameter "c" "Bool", parameter "t" "Word", parameter "f" "Word"]⟩, ⟨none, none⟩,
    some ⟨span, ⟨span, [annotation "Word"]⟩⟩, none⟩, source⟩⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def staticInputs := ((LocalTypeInputs.empty.bindFresh owner "c" .bool).bindFresh
  owner "t" .word).bindFresh owner "f" .word
private def inputs (choice : Bool) (left right : Core.Word) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh
    owner "t" .word (.word left) .word).bindFresh owner "f" .word (.word right) .word
private def arguments (choice : Bool) (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private def core : Core.Expr := .ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)
private def compiled : CompiledRuntimeFunction := ⟨staticInputs, core, .word⟩
private def prepared (choice : Bool) (left right : Core.Word) : PreparedRuntimeFunction :=
  ⟨inputs choice left right, core, .word⟩
private def required (choice : Bool) : Nat := if choice then 6 else 4
private def result (choice : Bool) (left right : Core.Word) : Core.Value :=
  .word (if choice then left.bitNot else right)
private theorem header : RuntimeFunctionHeader types (declaration body).value.signature .word :=
  ⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩
private theorem bodyElab : TerminalReturnBodyElaborates staticInputs.names staticInputs.context body core .word :=
  .conditional (.intro (.identifier (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.var (.tail (by decide) (.tail (by decide) .head)))
    (.expression (.bitNot (.identifier (.tail (by decide) .head)))
      (.unary (.var (.tail (by decide) .head))) (.unary (.var (.tail (by decide) .head))))
    (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem compiles : RuntimeFunctionCompiles types owner (declaration body) compiled :=
  ⟨header, .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
      (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal bodyElab.returnTree⟩
private theorem prepares (choice : Bool) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration body) (arguments choice left right) (prepared choice left right) :=
  ⟨header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
    (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
      (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)), TypedLetReturnBodyElaborates.returnTree <| .terminal bodyElab.returnTree⟩
private theorem conditionCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (ref "c") (.bool choice) store 1 :=
  .identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head))
    (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head))
private theorem yesCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store yes (.word left.bitNot) store 3 :=
  .expression (.bitNot (.identifier (.tail (show "f" ≠ "t" by decide) .head)
    (.tail (show id 2 ≠ id 1 by decide) .head)))
private theorem noCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost (inputs choice left right).names (inputs choice left right).environment
      store (returned (ref "f")) (.word right) store 1 := .expression (.identifier .head .head)
private theorem costed (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      store .word (result choice left right) store (required choice) := by
  apply RuntimeFunctionEvaluatesWithCost.intro (prepares choice left right)
  apply TypedLetReturnBodyEvaluatesWithCost.returnTree
  apply TypedLetReturnBodyEvaluatesWithCost.terminal
  apply TerminalReturnBodyEvaluatesWithCost.returnTree
  apply TerminalReturnBodyEvaluatesWithCost.conditional
  cases choice
  · exact .ifFalse (conditionCost false left right store) (noCost false left right store)
  · exact .ifTrue (conditionCost true left right store) (yesCost true left right store)

theorem annotation_only_compilation_and_actual_preparation_retain_exact_core
    (choice : Bool) (left right : Core.Word) :
    RuntimeFunctionCompiles types owner (declaration body) compiled ∧
    compileRuntimeFunction? types owner (declaration body) = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration body) (arguments choice left right) (prepared choice left right) ∧
    prepareRuntimeFunction? types owner (declaration body) (arguments choice left right) = some (prepared choice left right) ∧
    (prepared choice left right).toCompiled = compiled ∧
    (inputs choice left right).environment = [(id 2, .word right), (id 1, .word left), (id 0, .bool choice)] :=
  ⟨compiles, compiles.complete, prepares choice left right, (prepares choice left right).complete, rfl, rfl⟩

theorem compilation_factorization_keeps_the_actual_argument_values_at_every_fuel
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (store : Core.Store) :
    (prepareRuntimeFunction? types owner (declaration body) (arguments choice left right)).map
      PreparedRuntimeFunction.toCompiled = some compiled ∧
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store)) := by
  constructor
  · simpa only [compiles.complete, bind, Option.bind_some, show
      (arguments choice left right).map (·.type) = compiled.inputs.context.values.reverse from rfl, ↓reduceIte]
      using prepareRuntimeFunction?_factorization types owner (declaration body) (arguments choice left right)
  · exact compiles.run_eq (arguments choice left right) rfl fuel store

theorem independent_selected_costs_have_the_same_exact_compiled_paths
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      store .word (result choice left right) store (required choice) ∧
    Core.Steps (required choice) (Core.State.initial core [.word right, .word left, .bool choice] store)
      (Core.State.final (result choice left right) store) :=
  ⟨costed choice left right store, (costed choice left right store).compiled_toSteps compiles⟩

theorem all_entry_and_compiled_fuel_thresholds_keep_six_versus_four_steps
    (choice : Bool) (left right : Core.Word) (fuel : Nat) (store : Core.Store) :
    (runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, .done (result choice left right) store) ↔ required choice ≤ fuel) ∧
    ((∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel store =
      some (.word, .outOfFuel suspended)) ↔ fuel < required choice) ∧
    (Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) =
      .done (result choice left right) store ↔ required choice ≤ fuel) ∧
    ((∃ suspended, Core.runStateful fuel (Core.State.initial core [.word right, .word left, .bool choice] store) =
      .outOfFuel suspended) ↔ fuel < required choice) :=
  ⟨(costed choice left right store).run_done_iff, (costed choice left right store).run_outOfFuel_iff,
    (costed choice left right store).compiled_run_done_iff compiles,
    (costed choice left right store).compiled_run_outOfFuel_iff compiles⟩

private theorem bound : terminalReturnBodyFuelBound body = 6 := by
  simp [body, branch, returned, yes, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound]

theorem terminal_bound_is_six_while_the_unchanged_singleton_bound_is_zero
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    terminalReturnBodyFuelBound body = 6 ∧ returnBodyFuelBound body = 0 ∧ required choice ≤ 6 ∧
    (∃ value, Core.ValueHasType value .word ∧
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 6 store = some (.word, .done value store)) ∧
    (∃ value, Core.ValueHasType value .word ∧
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 6 store = some (.word, .done value store) ∧
      Core.runStateful 6 (Core.State.initial core [.word right, .word left, .bool choice] store) = .done value store) := by
  have treeBound : typedLetReturnTreeFuelBound body = 6 := by
    simp [body, branch, returned, yes, ref, typedLetReturnTreeFuelBound,
      returnBodyFuelBound, localExpressionFuelBound]
  have enough : typedLetReturnTreeFuelBound (declaration body).value.body ≤ 6 := by
    change typedLetReturnTreeFuelBound body ≤ 6
    rw [treeBound]; exact Nat.le_refl 6
  refine ⟨bound, rfl, ?_, (prepares choice left right).hasType.run_done_of_fuelBound store 6 enough,
    compiles.run_done_of_fuelBound (arguments choice left right) rfl store 6 enough⟩
  simpa only [show (declaration body).value.body = body from rfl, treeBound]
    using (costed choice left right store).cost_le_fuelBound

theorem a_same_typed_hand_built_core_does_not_supply_compilation_provenance :
    Core.HasType staticInputs.context.values (.word .zero) .word ∧
    ¬ RuntimeFunctionCompiles types owner (declaration body) { compiled with core := .word .zero } := by
  refine ⟨.word, ?_⟩
  intro forged
  have same := congrArg CompiledRuntimeFunction.core (compiles.result_unique forged)
  cases same

private def checkpoint (choice : Bool) (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.unary .wordNot (.var 1)) (.var 0)
    [.word right, .word left, .bool choice]], store⟩
private theorem exhausted (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) := by
  rw [runRuntimeFunction?, (prepares choice left right).complete]; cases choice <;> rfl

theorem owner_relabeling_keeps_the_complete_actual_checkpoint
    (choice : Bool) (left right : Core.Word) (otherOwner : Resolved.DeclarationId) (store : Core.Store) :
    runRuntimeFunction? types otherOwner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) :=
  (runRuntimeFunction?_owner_eq types otherOwner owner (declaration body) (arguments choice left right) 2 store).trans
    (exhausted choice left right store)

theorem resumption_runs_the_real_checkpoint_and_retains_its_exact_remaining_path
    (choice : Bool) (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 store =
      some (.word, .outOfFuel (checkpoint choice left right store)) ∧
    2 < required choice ∧ Core.Steps (required choice - 2) (checkpoint choice left right store)
      (Core.State.final (result choice left right) store) ∧
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) (2 + additional) store =
      some (.word, Core.runStateful additional (checkpoint choice left right store)) := by
  have residual := (costed choice left right store).residual_of_outOfFuel (exhausted choice left right store)
  exact ⟨exhausted choice left right store, residual.1, residual.2,
    runRuntimeFunction?_resume (exhausted choice left right store) additional⟩

theorem store_replay_preserves_values_and_costs_but_keeps_each_own_store
    (choice : Bool) (left right : Core.Word) (first replacement : Core.Store) (fuel : Nat) :
    RuntimeFunctionEvaluatesWithCost types owner (declaration body) (arguments choice left right)
      replacement .word (result choice left right) replacement (required choice) ∧
    (runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel first =
      some (.word, .done (result choice left right) first) ↔
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel replacement =
        some (.word, .done (result choice left right) replacement)) ∧
    ((∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel first =
      some (.word, .outOfFuel suspended)) ↔
      ∃ suspended, runRuntimeFunction? types owner (declaration body) (arguments choice left right) fuel replacement =
        some (.word, .outOfFuel suspended)) :=
  ⟨(costed choice left right first).change_store replacement,
    runRuntimeFunction?_done_store_iff types owner (declaration body) (arguments choice left right) fuel
      first replacement .word (result choice left right),
    runRuntimeFunction?_outOfFuel_store_iff types owner (declaration body) (arguments choice left right) fuel first replacement .word⟩

theorem differing_nonempty_stores_give_distinct_actual_checkpoints
    (choice : Bool) (left right : Core.Word) (tail : Core.Store) :
    runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 (.unit :: tail) ≠
      runRuntimeFunction? types owner (declaration body) (arguments choice left right) 2 (.bool true :: tail) := by
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private def selectBody : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "c") (returned (ref "t")) (some (returned (ref "f")))⟩]⟩
private def valueTypes (argument : TypedRuntimeArgument) : TypeNameTable :=
  [(["Bool"], .bool), (["Word"], argument.type)]
private def supplied (choice : Bool) (argument : TypedRuntimeArgument) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, argument, argument]
private def valueInputs (choice : Bool) (argument : TypedRuntimeArgument) : LocalInputs :=
  ((LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh
    owner "t" argument.type argument.value argument.valueTyped).bindFresh
      owner "f" argument.type argument.value argument.valueTyped

theorem arbitrary_typed_values_are_returned_without_invocation_or_allocation
    (choice : Bool) (argument : TypedRuntimeArgument) (store : Core.Store) (fuel : Nat) :
    RuntimeFunctionEvaluatesWithCost (valueTypes argument) owner (declaration selectBody) (supplied choice argument)
      store argument.type argument.value store 4 ∧
    (runRuntimeFunction? (valueTypes argument) owner (declaration selectBody) (supplied choice argument) fuel store =
      some (argument.type, .done argument.value store) ↔ 4 ≤ fuel) := by
  let candidate : PreparedRuntimeFunction := ⟨valueInputs choice argument, .ifE (.var 2) (.var 1) (.var 0), argument.type⟩
  have preparation : RuntimeFunctionPrepares (valueTypes argument) owner (declaration selectBody)
      (supplied choice argument) candidate :=
    ⟨⟨rfl, rfl, rfl, rfl, .single (.named (.tail (by decide) .head))⟩,
      .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
        (.cons (.named (.tail (by decide) .head)) (by change "t" ∉ ["c"]; simp)
          (.cons (.named (.tail (by decide) .head)) (by change "f" ∉ ["t", "c"]; simp) .nil)),
      TypedLetReturnBodyElaborates.returnTree <| .terminal <| .conditional (.identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head)))
        (.var (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head)))
        (.var (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head)))
        (.single (.expression (.identifier (.tail (show "f" ≠ "t" by decide) .head))
          (.var (.tail (show id 2 ≠ id 1 by decide) .head)) (.var (.tail (show id 2 ≠ id 1 by decide) .head))))
        (.single (.expression (.identifier .head) (.var .head) (.var .head)))⟩
  have condition : LocalExpressionEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (ref "c") (.bool choice) store 1 :=
    .identifier (.tail (show "f" ≠ "c" by decide) (.tail (show "t" ≠ "c" by decide) .head))
      (.tail (show id 2 ≠ id 0 by decide) (.tail (show id 1 ≠ id 0 by decide) .head))
  have yesValue : ReturnBodyEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (returned (ref "t")) argument.value store 1 :=
    .expression (.identifier (.tail (show "f" ≠ "t" by decide) .head) (.tail (show id 2 ≠ id 1 by decide) .head))
  have noValue : ReturnBodyEvaluatesWithCost candidate.inputs.names candidate.inputs.environment
      store (returned (ref "f")) argument.value store 1 := .expression (.identifier .head .head)
  have evaluated : RuntimeFunctionEvaluatesWithCost (valueTypes argument) owner (declaration selectBody)
      (supplied choice argument) store argument.type argument.value store 4 := by
    apply RuntimeFunctionEvaluatesWithCost.intro preparation
    apply TypedLetReturnBodyEvaluatesWithCost.returnTree
    apply TypedLetReturnBodyEvaluatesWithCost.terminal
    apply TerminalReturnBodyEvaluatesWithCost.returnTree
    apply TerminalReturnBodyEvaluatesWithCost.conditional
    cases choice
    · exact .ifFalse condition noValue
    · exact .ifTrue condition yesValue
  exact ⟨evaluated, evaluated.run_done_iff⟩

private def missing := branch (returned (ref "missing"))

theorem raw_selected_success_does_not_accept_an_unresolved_unselected_arm
    (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluatesWithCost (inputs true left right).names (inputs true left right).environment
      store missing (.word left.bitNot) store 6 ∧
    prepareRuntimeFunction? types owner (declaration missing) (arguments true left right) = none ∧
    runRuntimeFunction? types owner (declaration missing) (arguments true left right) fuel store = none := by
  have bodyRejected : (inputs true left right).checkTypedLetReturnTree? types owner missing = none := by
    simp [LocalInputs.checkTypedLetReturnTree?, elaborateTypedLetReturnTree?, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context,
      missing, branch, yes, returned, ref, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have noPreparation : ¬ ∃ candidate, RuntimeFunctionPrepares types owner (declaration missing)
      (arguments true left right) candidate := by
    rintro ⟨candidate, accepted⟩
    have same := (prepares true left right).parameters.result_unique accepted.parameters
    have checked := accepted.body.complete
    rw [← same] at checked
    change (inputs true left right).checkTypedLetReturnTree? types owner missing = some _ at checked
    rw [bodyRejected] at checked
    cases checked
  have rejected := prepareRuntimeFunction?_eq_none_iff.mpr noPreparation
  exact ⟨.conditional (.ifTrue (conditionCost true left right store) (yesCost true left right store)), rejected,
    by simp only [runRuntimeFunction?, rejected, bind, Option.bind_none]⟩

end Tests.FrontendTerminalRuntimeEntry
