import Solcore.Frontend.TerminalReturnBody
import Solcore.Frontend.RuntimeFunction

/-! Identity transport preserves whole suspended states, whereas store replay
preserves observations carrying their own stores. Merging IDs is explicitly
excluded and can change both the selected Bool and its exact cost. -/

set_option autoImplicit false

namespace Tests.FrontendTerminalBodyInvariance

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "body-invariance.sol"⟩, 5, 23⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"BodyInvariance", by decide⟩], by decide⟩⟩, 0⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def single := returned (ref "v")
private def body : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") single
  (some (returned ⟨span, .unary ⟨span, .logicalNot⟩ (ref "v")⟩))⟩]⟩
private def inputs (choice flag : Bool) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "v" .bool (.bool flag) .bool
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.unary .boolNot (.var 0))
private theorem names_ne : "v" ≠ "c" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def required (choice : Bool) := if choice then 4 else 6
private def result (choice flag : Bool) : Core.Value := .bool (if choice then flag else !flag)
private theorem singleElab (choice flag : Bool) :
    ReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context single (.var 0) .bool :=
  .expression (.identifier .head) (.var .head) (.var .head)
private theorem elaborated (choice flag : Bool) :
    ConditionalReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context body core .bool :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (singleElab choice flag) (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
private theorem terminalElab (choice flag : Bool) :
    TerminalReturnBodyElaborates (inputs choice flag).names (inputs choice flag).context body core .bool :=
  .conditional (elaborated choice flag)
private theorem checked (choice flag : Bool) :
    (inputs choice flag).checkTerminalReturnBody? body = some (core, .bool) := (terminalElab choice flag).complete
private theorem conditionCost (choice flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
private theorem valueCost (choice flag : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store (ref "v") (.bool flag) store 1 := .identifier .head .head
private theorem costed (choice flag : Bool) (store : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      store body (result choice flag) store (required choice) := by
  cases choice
  · exact .ifFalse (conditionCost false flag store) (.expression (.logicalNot (valueCost false flag store)))
  · exact .ifTrue (conditionCost true flag store) (.expression (valueCost true flag store))

theorem injective_elaboration_transport_retains_exact_core_for_all_three_profiles
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    ReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) single (.var 0) .bool ∧
    ConditionalReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body core .bool ∧
    TerminalReturnBodyElaborates (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body core .bool :=
  ⟨(singleElab choice flag).mapIds mapping injective, (elaborated choice flag).mapIds mapping injective,
    (terminalElab choice flag).mapIds mapping injective⟩

theorem injective_checkers_and_entire_same_fuel_results_agree
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (store : Core.Store) :
    ((inputs choice flag).mapIds mapping injective).checkConditionalReturnBody? body = some (core, .bool) ∧
    ((inputs choice flag).mapIds mapping injective).checkTerminalReturnBody? body = some (core, .bool) ∧
    ((inputs choice flag).mapIds mapping injective).runConditionalReturnBody? fuel body store =
      (inputs choice flag).runConditionalReturnBody? fuel body store ∧
    ((inputs choice flag).mapIds mapping injective).runTerminalReturnBody? fuel body store =
      (inputs choice flag).runTerminalReturnBody? fuel body store :=
  ⟨((inputs choice flag).checkConditionalReturnBody?_mapIds mapping injective body).trans (elaborated choice flag).complete,
    ((inputs choice flag).checkTerminalReturnBody?_mapIds mapping injective body).trans (checked choice flag),
    (inputs choice flag).runConditionalReturnBody?_mapIds mapping injective fuel body store,
    (inputs choice flag).runTerminalReturnBody?_mapIds mapping injective fuel body store⟩

theorem optional_component_checkers_retain_exact_successful_core
    (choice flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) :
    elaborateReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) single = some (.var 0, .bool) ∧
    elaborateConditionalReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body = some (core, .bool) ∧
    elaborateTerminalReturnBody? (LocalNameTable.mapIds mapping (inputs choice flag).names)
      (Resolved.LocalScope.mapIds mapping (inputs choice flag).context) body = some (core, .bool) :=
  ⟨(elaborateReturnBody?_mapIds mapping injective _ _ _).trans (singleElab choice flag).complete,
    (elaborateConditionalReturnBody?_mapIds mapping injective _ _ _).trans (elaborated choice flag).complete,
    (elaborateTerminalReturnBody?_mapIds mapping injective _ _ _).trans (terminalElab choice flag).complete⟩

private def shifted (id : Resolved.LocalId) : Resolved.LocalId := ⟨id.owner, id.binderIndex + 7⟩
private theorem shiftedInjective : Function.Injective shifted := by
  intro ⟨leftOwner, leftIndex⟩ ⟨rightOwner, rightIndex⟩ same
  simp only [shifted, Resolved.LocalId.mk.injEq] at same
  obtain ⟨rfl, indexes⟩ := same
  cases Nat.add_right_cancel indexes
  rfl
private def checkpoint (choice flag : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 0) (.unary .boolNot (.var 0)) [.bool flag, .bool choice]], store⟩
private theorem exhausted (choice flag : Bool) (store : Core.Store) :
    (inputs choice flag).runTerminalReturnBody? 2 body store = some (.bool, .outOfFuel (checkpoint choice flag store)) := by
  rw [LocalInputs.runTerminalReturnBody?, checked]; cases choice <;> rfl

theorem nontrivial_identity_shift_preserves_the_actual_whole_checkpoint
    (choice flag : Bool) (store : Core.Store) :
    shifted ⟨owner, 0⟩ ≠ ⟨owner, 0⟩ ∧
    ((inputs choice flag).mapIds shifted shiftedInjective).runTerminalReturnBody? 2 body store =
      some (.bool, .outOfFuel (checkpoint choice flag store)) :=
  ⟨by decide, ((inputs choice flag).runTerminalReturnBody?_mapIds shifted shiftedInjective 2 body store).trans
    (exhausted choice flag store)⟩

theorem singleton_actual_typed_values_replay_through_the_old_store_api_and_terminal_wrapper
    (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type)
    (first replacement : Core.Store) :
    let supplied := LocalInputs.empty.bindFresh owner "v" type value valueTyped
    ReturnBodyEvaluates supplied.names supplied.environment replacement single value replacement ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment replacement single value replacement 1 ∧
    TerminalReturnBodyEvaluates supplied.names supplied.environment replacement single value replacement ∧
    TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment replacement single value replacement 1 := by
  intro supplied
  have original : ReturnBodyEvaluatesWithCost supplied.names supplied.environment first single value first 1 :=
    .expression (.identifier .head .head)
  have common : TerminalReturnBodyEvaluatesWithCost supplied.names supplied.environment first single value first 1 := .single original
  exact ⟨original.erase.change_store replacement, original.change_store replacement,
    common.erase.change_store replacement, common.change_store replacement⟩

theorem conditional_raw_and_exact_cost_replay_keep_the_selected_bool_and_cost
    (choice flag : Bool) (first replacement : Core.Store) :
    ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement (required choice) ∧
    TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement ∧
    TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      replacement body (result choice flag) replacement (required choice) := by
  have original := costed choice flag first
  have common : TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      first body (result choice flag) first (required choice) := .conditional original
  exact ⟨original.erase.change_store replacement, original.change_store replacement,
    common.erase.change_store replacement, common.change_store replacement⟩

theorem replay_equivalences_preserve_initial_final_store_equality
    (choice flag : Bool) (initialStore finalStore replacement : Core.Store) :
    (ReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore single (.bool flag) finalStore ↔
      finalStore = initialStore ∧ ReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement single (.bool flag) replacement) ∧
    (ReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment initialStore single (.bool flag) finalStore 1 ↔
      finalStore = initialStore ∧ ReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement single (.bool flag) replacement 1) ∧
    (ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore body (result choice flag) finalStore ↔
      finalStore = initialStore ∧ ConditionalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement) ∧
    (ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      initialStore body (result choice flag) finalStore (required choice) ↔
      finalStore = initialStore ∧ ConditionalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement (required choice)) ∧
    (TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment initialStore body (result choice flag) finalStore ↔
      finalStore = initialStore ∧ TerminalReturnBodyEvaluates (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement) ∧
    (TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
      initialStore body (result choice flag) finalStore (required choice) ↔
      finalStore = initialStore ∧ TerminalReturnBodyEvaluatesWithCost (inputs choice flag).names (inputs choice flag).environment
        replacement body (result choice flag) replacement (required choice)) :=
  ⟨returnBodyEvaluates_store_iff, returnBodyEvaluatesWithCost_store_iff,
    conditionalReturnBodyEvaluates_store_iff, conditionalReturnBodyEvaluatesWithCost_store_iff,
    terminalReturnBodyEvaluates_store_iff, terminalReturnBodyEvaluatesWithCost_store_iff⟩

theorem completion_and_exhaustion_presence_agree_without_equating_stored_states
    (choice flag : Bool) (fuel : Nat) (first replacement : Core.Store) :
    ((inputs choice flag).runConditionalReturnBody? fuel body first = some (.bool, .done (result choice flag) first) ↔
      (inputs choice flag).runConditionalReturnBody? fuel body replacement = some (.bool, .done (result choice flag) replacement)) ∧
    ((∃ checkpoint, (inputs choice flag).runConditionalReturnBody? fuel body first = some (.bool, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice flag).runConditionalReturnBody? fuel body replacement = some (.bool, .outOfFuel checkpoint)) ∧
    ((inputs choice flag).runTerminalReturnBody? fuel body first = some (.bool, .done (result choice flag) first) ↔
      (inputs choice flag).runTerminalReturnBody? fuel body replacement = some (.bool, .done (result choice flag) replacement)) ∧
    ((∃ checkpoint, (inputs choice flag).runTerminalReturnBody? fuel body first = some (.bool, .outOfFuel checkpoint)) ↔
      ∃ checkpoint, (inputs choice flag).runTerminalReturnBody? fuel body replacement = some (.bool, .outOfFuel checkpoint)) :=
  ⟨(inputs choice flag).runConditionalReturnBody?_done_store_iff fuel body first replacement .bool (result choice flag),
    (inputs choice flag).runConditionalReturnBody?_outOfFuel_store_iff fuel body first replacement .bool,
    (inputs choice flag).runTerminalReturnBody?_done_store_iff fuel body first replacement .bool (result choice flag),
    (inputs choice flag).runTerminalReturnBody?_outOfFuel_store_iff fuel body first replacement .bool⟩

theorem differing_nonempty_stores_change_full_checkpoints_even_when_fuel_agrees
    (choice flag : Bool) (tail : Core.Store) :
    (inputs choice flag).runTerminalReturnBody? 2 body (.unit :: tail) =
      some (.bool, .outOfFuel (checkpoint choice flag (.unit :: tail))) ∧
    (inputs choice flag).runTerminalReturnBody? 2 body (.bool true :: tail) =
      some (.bool, .outOfFuel (checkpoint choice flag (.bool true :: tail))) ∧
    (inputs choice flag).runTerminalReturnBody? 2 body (.unit :: tail) ≠
      (inputs choice flag).runTerminalReturnBody? 2 body (.bool true :: tail) := by
  refine ⟨exhausted choice flag _, exhausted choice flag _, ?_⟩
  rw [exhausted, exhausted]
  intro same
  have stored := congrArg (fun state : Core.State => state.store)
    (Core.StatefulRunResult.outOfFuel.inj (Prod.mk.inj (Option.some.inj same)).2)
  cases stored

private def missingArm : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "c") single (some (returned (ref "missing")))⟩]⟩

theorem invalid_unselected_arm_remains_absent_under_identity_and_store_changes
    (flag : Bool) (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (fuel : Nat) (first replacement : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs true flag).names (inputs true flag).environment
      first missingArm (.bool flag) first 4 ∧
    (inputs true flag).checkTerminalReturnBody? missingArm = none ∧
    ((inputs true flag).mapIds mapping injective).checkConditionalReturnBody? missingArm = none ∧
    ((inputs true flag).mapIds mapping injective).runTerminalReturnBody? fuel missingArm replacement = none := by
  have rejected : (inputs true flag).checkTerminalReturnBody? missingArm = none := by
    simp [LocalInputs.checkTerminalReturnBody?, elaborateTerminalReturnBody?, elaborateConditionalReturnBody?,
      missingArm, single, returned, ref, elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?,
      inputs, LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have absent : (inputs true flag).runTerminalReturnBody? fuel missingArm replacement = none := by
    simp only [LocalInputs.runTerminalReturnBody?, rejected, bind, Option.bind_none]
  exact ⟨.ifTrue (conditionCost true flag first) (.expression (valueCost true flag first)), rejected,
    ((inputs true flag).checkConditionalReturnBody?_mapIds mapping injective missingArm).trans rejected,
    ((inputs true flag).runTerminalReturnBody?_mapIds mapping injective fuel missingArm replacement).trans absent⟩

private def collapse (_ : Resolved.LocalId) : Resolved.LocalId := ⟨owner, 0⟩

theorem merging_two_bool_ids_changes_first_lookup_selected_value_and_cost
    (store : Core.Store) :
    ¬ Function.Injective collapse ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs false true).names (inputs false true).environment store body (.bool false) store 6 ∧
    ConditionalReturnBodyEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store body (.bool true) store 4 ∧
    elaborateConditionalReturnBody? (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).context) body =
        some (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0)), .bool) := by
  have condition : LocalExpressionEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store (ref "c") (.bool true) store 1 :=
    .identifier (.tail names_ne .head) .head
  have value : ReturnBodyEvaluatesWithCost (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).environment) store single (.bool true) store 1 :=
    .expression (.identifier .head .head)
  have mapped : ConditionalReturnBodyElaborates (LocalNameTable.mapIds collapse (inputs false true).names)
      (Resolved.LocalScope.mapIds collapse (inputs false true).context) body
      (.ifE (.var 0) (.var 0) (.unary .boolNot (.var 0))) .bool :=
    .intro (.identifier (.tail names_ne .head)) (.var .head) (.var .head)
      (.expression (.identifier .head) (.var .head) (.var .head))
      (.expression (.logicalNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
  refine ⟨?_, costed false true store, .ifTrue condition value, mapped.complete⟩
  intro injective
  exact ids_ne (injective (a₁ := ⟨owner, 1⟩) (a₂ := ⟨owner, 0⟩) rfl)

end Tests.FrontendTerminalBodyInvariance
