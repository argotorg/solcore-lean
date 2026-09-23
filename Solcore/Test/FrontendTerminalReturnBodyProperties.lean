import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.RuntimeFunction

/-! The nonrecursive union preserves each original profile's full observations.
Independent fixtures retain actual inputs and do not turn conditional arms into
recursive terminal bodies or accept function entries with ill-scoped bodies. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalReturnBody

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "terminal-union.sol"⟩, 29, 8⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"TerminalUnion", by decide⟩], by decide⟩⟩, 0⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def complement : Syntax.Expr := ⟨span, .unary ⟨span, .bitNot⟩ (ref "w")⟩
private def conditional := branch (returned (some complement)) (returned (some (ref "w")))
private def core : Core.Expr := .ifE (.var 1) (.unary .wordNot (.var 0)) (.var 0)
private def inputs (choice : Bool) (word : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "w" .word (.word word) .word
private theorem names_ne : "w" ≠ "c" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def required (choice : Bool) : Nat := if choice then 6 else 4
private def result (choice : Bool) (word : Core.Word) : Core.Value := .word (if choice then word.bitNot else word)
private theorem conditionCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
private theorem valueCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "w") (.word word) store 1 := .identifier .head .head
private theorem conditionalTyped (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyHasType (inputs choice word).names (inputs choice word).context conditional .word :=
  .intro (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    (.expression (.bitNot (.identifier .head .head))) (.expression (.identifier .head .head))
private theorem conditionalElaborated (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
    (.expression (.identifier .head) (.var .head) (.var .head))
private theorem conditionalCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) := by
  cases choice
  · exact .ifFalse (conditionCost false word store) (.expression (valueCost false word store))
  · exact .ifTrue (conditionCost true word store) (.expression (.bitNot (valueCost true word store)))
private theorem elaborated (choice : Bool) (word : Core.Word) :
    TerminalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word :=
  .conditional (conditionalElaborated choice word)
private theorem checked (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkTerminalReturnBody? conditional = some (core, .word) := (elaborated choice word).complete
private theorem costed (choice : Bool) (word : Core.Word) (store : Core.Store) :
    TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) := .conditional (conditionalCost choice word store)

theorem bare_return_embeddings_and_original_runner_agree_at_every_fuel
    (supplied : LocalInputs) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyHasType supplied.names supplied.context (returned none) .unit ∧
    TerminalReturnBodyElaborates supplied.names supplied.context (returned none) .unit .unit ∧
    TerminalReturnBodyEvaluates supplied.names supplied.environment store (returned none) .unit store ∧
    TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment store (returned none) .unit store 1 ∧
    supplied.runTerminalReturnBody? fuel (returned none) store = supplied.runReturnBody? fuel (returned none) store ∧
    terminalReturnBodyFuelBound (returned none) = 1 :=
  ⟨.single .bare, .single .bare, .single .bare, .single .bare,
    supplied.runTerminalReturnBody?_single fuel none span span store, rfl⟩

theorem singleton_expression_raw_and_cost_projection_do_not_admit_a_conditional_derivation
    (table : LocalNameTable) (environment : Resolved.Environment) (source : Syntax.Expr)
    (initialStore finalStore : Core.Store) (value : Core.Value) (cost : Nat) :
    (TerminalReturnBodyEvaluates table environment initialStore (returned (some source)) value finalStore ↔
      ReturnBodyEvaluates table environment initialStore (returned (some source)) value finalStore) ∧
    (TerminalReturnBodyEvaluatesWithCost table environment initialStore (returned (some source)) value finalStore cost ↔
      ReturnBodyEvaluatesWithCost table environment initialStore (returned (some source)) value finalStore cost) := by
  constructor
  · constructor
    · intro evaluation; cases evaluation with | single child => exact child | conditional child => cases child
    · exact TerminalReturnBodyEvaluates.single
  · constructor
    · intro evaluation; cases evaluation with | single child => exact child | conditional child => cases child
    · exact TerminalReturnBodyEvaluatesWithCost.single

theorem arbitrary_actual_typed_expression_values_keep_one_step_and_all_outer_frames
    (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    let supplied := LocalInputs.empty.bindFresh owner "w" type value valueTyped
    supplied.runTerminalReturnBody? fuel (returned (some (ref "w"))) store =
      supplied.runReturnBody? fuel (returned (some (ref "w"))) store ∧
    Core.Steps 1 ⟨.eval (.var 0) [value], continuation, store⟩ ⟨.ret value, continuation, store⟩ ∧
    (supplied.runTerminalReturnBody? fuel (returned (some (ref "w"))) store =
      some (type, .done value store) ↔ 1 ≤ fuel) := by
  intro supplied
  have elaboration : TerminalReturnBodyElaborates supplied.names supplied.context
      (returned (some (ref "w"))) (.var 0) type := .single (.expression (.identifier .head) (.var .head) (.var .head))
  have check : supplied.checkTerminalReturnBody? (returned (some (ref "w"))) = some (.var 0, type) := elaboration.complete
  have evaluation : TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment store
      (returned (some (ref "w"))) value store 1 := .single (.expression (.identifier .head .head))
  refine ⟨supplied.runTerminalReturnBody?_single fuel (some (ref "w")) span span store,
    evaluation.checked_toStepsWithContinuation check supplied.sameIds continuation, ?_⟩
  simpa only [LocalInputs.runTerminalReturnBody?, check, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using evaluation.checked_runStateful_done_iff
      (fuel := fuel) check supplied.sameIds

theorem conditional_embedding_keeps_the_original_core_type_value_store_and_cost
    (choice : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyHasType (inputs choice word).names (inputs choice word).context conditional .word ∧
    TerminalReturnBodyElaborates (inputs choice word).names (inputs choice word).context conditional core .word ∧
    TerminalReturnBodyEvaluates (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store ∧
    TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store conditional (result choice word) store (required choice) ∧
    Core.Steps (required choice) (Core.State.initial core [.word word, .bool choice] store)
      (Core.State.final (result choice word) store) ∧
    (inputs choice word).runTerminalReturnBody? fuel conditional store =
      (inputs choice word).runConditionalReturnBody? fuel conditional store :=
  ⟨.conditional (conditionalTyped choice word), elaborated choice word,
    .conditional (conditionalCost choice word store).erase, costed choice word store,
    (costed choice word store).checked_toSteps (checked choice word) (inputs choice word).sameIds,
    (inputs choice word).runTerminalReturnBody?_conditional fuel (ref "c")
      (returned (some complement)) (returned (some (ref "w"))) span span store⟩

theorem conditional_projection_retains_selected_arm_costs_without_recursive_union_arms
    (choice : Bool) (word : Core.Word) (initialStore finalStore : Core.Store) (value : Core.Value) (cost : Nat) :
    (TerminalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      initialStore conditional value finalStore cost ↔
      ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
        initialStore conditional value finalStore cost) := by
  constructor
  · intro evaluation; cases evaluation with | single child => cases child | conditional child => exact child
  · exact TerminalReturnBodyEvaluatesWithCost.conditional

theorem common_all_fuel_boundaries_and_continuation_paths_add_no_wrapper_steps
    (choice : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) (continuation : List Core.Frame) :
    ((inputs choice word).runTerminalReturnBody? fuel conditional store =
      some (.word, .done (result choice word) store) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice word).runTerminalReturnBody? fuel conditional store =
      some (.word, .outOfFuel checkpoint)) ↔ fuel < required choice) ∧
    Core.Steps (required choice) ⟨.eval core [.word word, .bool choice], continuation, store⟩
      ⟨.ret (result choice word), continuation, store⟩ := by
  refine ⟨?_, ?_, (costed choice word store).checked_toStepsWithContinuation
    (checked choice word) (inputs choice word).sameIds continuation⟩
  · simpa only [LocalInputs.runTerminalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_done_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds
  · simpa only [LocalInputs.runTerminalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_outOfFuel_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds

private def deciding (choice : Bool) (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.unary .wordNot (.var 0)) (.var 0) [.word word, .bool choice]], store⟩

theorem common_runner_resumes_the_same_genuine_conditional_checkpoint
    (choice : Bool) (word : Core.Word) (store : Core.Store) (additional : Nat) :
    (inputs choice word).runTerminalReturnBody? 2 conditional store = some (.word, .outOfFuel (deciding choice word store)) ∧
    Core.Steps (required choice - 2) (deciding choice word store) (Core.State.final (result choice word) store) ∧
    (inputs choice word).runTerminalReturnBody? (2 + additional) conditional store =
      some (.word, Core.runStateful additional (deciding choice word store)) := by
  have exhausted : (inputs choice word).runTerminalReturnBody? 2 conditional store =
      some (.word, .outOfFuel (deciding choice word store)) := by
    rw [LocalInputs.runTerminalReturnBody?, checked]; cases choice <;> rfl
  have actual : Core.runStateful 2 (Core.State.initial core [.word word, .bool choice] store) =
      .outOfFuel (deciding choice word store) := by cases choice <;> rfl
  exact ⟨exhausted, ((costed choice word store).checked_residual_of_outOfFuel
    (checked choice word) (inputs choice word).sameIds actual).2,
    LocalInputs.runTerminalReturnBody?_resume exhausted additional⟩

theorem bounds_dispatch_to_existing_profiles_but_old_entry_bound_remains_singleton_only :
    terminalReturnBodyFuelBound (returned none) = returnBodyFuelBound (returned none) ∧
    terminalReturnBodyFuelBound conditional = conditionalReturnBodyFuelBound conditional ∧
    terminalReturnBodyFuelBound conditional = 6 ∧ returnBodyFuelBound conditional = 0 :=
  ⟨rfl, rfl, by simp [conditional, branch, returned, complement, ref, terminalReturnBodyFuelBound,
    conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound], rfl⟩

theorem common_bound_completes_with_the_actual_selected_typed_value
    (choice : Bool) (word : Core.Word) (store : Core.Store) :
    required choice ≤ terminalReturnBodyFuelBound conditional ∧
    Core.ValueHasType (result choice word) .word ∧
    (inputs choice word).runTerminalReturnBody? 6 conditional store = some (.word, .done (result choice word) store) := by
  have bound := bounds_dispatch_to_existing_profiles_but_old_entry_bound_remains_singleton_only.2.2.1
  have enough := (costed choice word store).cost_le_fuelBound
  have actual := (common_all_fuel_boundaries_and_continuation_paths_add_no_wrapper_steps choice word store 6 []).1.mpr
    (by simpa only [bound] using enough)
  obtain ⟨value, valueTyped, completed⟩ := LocalInputs.runTerminalReturnBody?_done_of_fuelBound
    (.conditional (conditionalTyped choice word)) store 6 (by simp only [bound, Nat.le_refl])
  rw [actual] at completed
  cases completed
  exact ⟨enough, valueTyped, actual⟩

private def missingArm := branch (returned (some (ref "w"))) (returned (some (ref "missing")))
private def nested := branch conditional (returned none)

theorem raw_skipped_arm_success_does_not_certify_common_whole_checking
    (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluatesWithCost (inputs true word).names (inputs true word).environment
      store missingArm (.word word) store 4 ∧
    (inputs true word).checkTerminalReturnBody? missingArm = none ∧
    (inputs true word).runTerminalReturnBody? fuel missingArm store = none := by
  have rejected : (inputs true word).checkTerminalReturnBody? missingArm = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      missingArm, branch, returned, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.conditional (.ifTrue (conditionCost true word store) (.expression (valueCost true word store))),
    rejected, by simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]⟩

theorem nested_statement_conditionals_are_not_recursively_accepted
    (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    TerminalReturnBodyEvaluates (inputs false word).names (inputs false word).environment store nested .unit store ∧
    (inputs false word).checkTerminalReturnBody? nested = none ∧
    (inputs false word).runTerminalReturnBody? fuel nested store = none := by
  have rejected : (inputs false word).checkTerminalReturnBody? nested = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      nested, branch, conditional, returned, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.conditional (.ifFalse (conditionCost false word store).erase .bare), rejected,
    by simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]⟩

private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "unchanged"⟩, none, ⟨span, []⟩, ⟨none, none⟩, none, none⟩, conditional⟩⟩

theorem original_singleton_rejects_and_ill_scoped_function_entry_still_rejects
    (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkReturnBody? conditional = none ∧
    compileRuntimeFunction? [] owner declaration = none := by
  refine ⟨rfl, ?_⟩
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = .empty := accepted.parameters.result_unique .nil
  have checked := accepted.body.complete
  rw [sameInputs] at checked
  simp [elaborateTypedLetReturnTree?, declaration, conditional,
    branch, ref, elaborateLocalExpression?, resolveLocalExpression?, LocalTypeInputs.empty,
    LocalTypeInputs.names, LocalTypeInputs.context, LocalNameTable.lookup?] at checked

end Tests.FrontendTerminalReturnBody
