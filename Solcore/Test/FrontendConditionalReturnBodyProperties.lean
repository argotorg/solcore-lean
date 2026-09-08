import Solcore.Frontend.ConditionalReturnBodyExecutionProperties
import Solcore.Frontend.ConditionalReturnBodyFuelBoundProperties
import Solcore.Frontend.ConditionalReturnBodyResumptionProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties

/-! Independent terminal conditional bodies retain both checked return arms,
but execute only the selected arm. Actual values and stores are not replaced
by type representatives; the existing runtime entry also accepts terminal bodies. -/

set_option autoImplicit false

namespace Tests.FrontendConditionalReturnBody

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "conditional-return.sol"⟩, 17, 5⟩
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ConditionalReturn", by decide⟩], by decide⟩⟩, 0⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (value : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt value⟩]⟩
private def branch (yes no : Syntax.Block) : Syntax.Block := ⟨span, [⟨span, .ifThen (ref "c") yes (some no)⟩]⟩
private def supplied (choice : Bool) (type : Core.Ty) (value : Core.Value)
    (typed : Core.ValueHasType value type) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool).bindFresh owner "x" type value typed
private theorem names_ne : "x" ≠ "c" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private def body : Syntax.Block := branch (returned (some (ref "x")))
  (returned (some ⟨span, .unary ⟨span, .bitNot⟩ (ref "x")⟩))
private def core : Core.Expr := .ifE (.var 1) (.var 0) (.unary .wordNot (.var 0))
private def required (choice : Bool) : Nat := if choice then 4 else 6
private def result (choice : Bool) (word : Core.Word) : Core.Value := .word (if choice then word else word.bitNot)
private def inputs (choice : Bool) (word : Core.Word) := supplied choice .word (.word word) .word
private theorem typed (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyHasType (inputs choice word).names (inputs choice word).context body .word :=
  .intro (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    (.expression (.identifier .head .head)) (.expression (.bitNot (.identifier .head .head)))
private theorem elaborated (choice : Bool) (word : Core.Word) :
    ConditionalReturnBodyElaborates (inputs choice word).names (inputs choice word).context body core .word :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (.expression (.identifier .head) (.var .head) (.var .head))
    (.expression (.bitNot (.identifier .head)) (.unary (.var .head)) (.unary (.var .head)))
private theorem checked (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkConditionalReturnBody? body = some (core, .word) := (elaborated choice word).complete
private theorem conditionCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "c") (.bool choice) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
private theorem valueCost (choice : Bool) (word : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store (ref "x") (.word word) store 1 := .identifier .head .head
private theorem costed (choice : Bool) (word : Core.Word) (store : Core.Store) :
    ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store body (result choice word) store (required choice) := by
  cases choice
  · exact .ifFalse (conditionCost false word store)
      (.expression (.bitNot (valueCost false word store)))
  · exact .ifTrue (conditionCost true word store) (.expression (valueCost true word store))

theorem independent_typing_elaboration_and_both_selected_arm_costs
    (choice : Bool) (word : Core.Word) (store : Core.Store) :
    ConditionalReturnBodyHasType (inputs choice word).names (inputs choice word).context body .word ∧
    ConditionalReturnBodyElaborates (inputs choice word).names (inputs choice word).context body core .word ∧
    (inputs choice word).checkConditionalReturnBody? body = some (core, .word) ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names (inputs choice word).environment
      store body (result choice word) store (required choice) ∧
    Core.Steps (required choice) (Core.State.initial core [.word word, .bool choice] store)
      (Core.State.final (result choice word) store) :=
  ⟨typed choice word, elaborated choice word, checked choice word, costed choice word store,
    (costed choice word store).checked_toSteps (checked choice word) (inputs choice word).sameIds⟩

theorem all_fuel_thresholds_keep_four_versus_six_steps_and_the_actual_store
    (choice : Bool) (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs choice word).runConditionalReturnBody? fuel body store =
      some (.word, .done (result choice word) store) ↔ required choice ≤ fuel) ∧
    ((∃ checkpoint, (inputs choice word).runConditionalReturnBody? fuel body store =
      some (.word, .outOfFuel checkpoint)) ↔ fuel < required choice) := by
  constructor
  · simpa only [LocalInputs.runConditionalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_done_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds
  · simpa only [LocalInputs.runConditionalReturnBody?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using (costed choice word store).checked_runStateful_outOfFuel_iff
        (fuel := fuel) (checked choice word) (inputs choice word).sameIds

theorem checked_core_reflection_needs_identity_alignment_but_not_runtime_typing
    (choice : Bool) (word : Core.Word) (environment : Resolved.Environment)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids (inputs choice word).context)
    (initialStore finalStore : Core.Store) (value : Core.Value) :
    ConditionalReturnBodyEvaluates (inputs choice word).names environment initialStore body value finalStore ↔
      Core.Evaluates (Resolved.LocalScope.values environment) initialStore core value finalStore :=
  elaborateConditionalReturnBody?_evaluates_iff (checked choice word) sameIds

theorem exact_selected_paths_leave_arbitrary_outer_frames_unexecuted
    (choice : Bool) (word : Core.Word) (store : Core.Store) (continuation : List Core.Frame) :
    Core.Steps (required choice) ⟨.eval core [.word word, .bool choice], continuation, store⟩
      ⟨.ret (result choice word), continuation, store⟩ :=
  (costed choice word store).checked_toStepsWithContinuation
    (checked choice word) (inputs choice word).sameIds continuation

theorem raw_meaning_cost_existence_safety_and_determinism_keep_actual_results
    (choice : Bool) (word : Core.Word) (store finalStore : Core.Store) (value : Core.Value) (cost : Nat)
    (other : ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names
      (inputs choice word).environment store body value finalStore cost) :
    value = result choice word ∧ finalStore = store ∧ cost = required choice ∧
    Core.ValueHasType (result choice word) .word ∧ 0 < required choice ∧
    ConditionalReturnBodyEvaluates (inputs choice word).names (inputs choice word).environment
      store body (result choice word) store ∧
    ∃ exactCost, ConditionalReturnBodyEvaluatesWithCost (inputs choice word).names
      (inputs choice word).environment store body (result choice word) store exactCost := by
  have counted := costed choice word store
  have unique := other.deterministic counted
  have safe := counted.erase.preserves_type (typed choice word) (inputs choice word).sameIds
    (inputs choice word).environmentTyped
  exact ⟨unique.1, other.store_eq, unique.2.2, safe.1, counted.cost_pos, counted.erase, counted.erase.exists_cost⟩

private def deciding (choice : Bool) (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.bool choice), [.ifBranches (.var 0) (.unary .wordNot (.var 0)) [.word word, .bool choice]], store⟩
private def complementing (word : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word word), [.unaryApply .wordNot], store⟩

theorem genuine_conditional_frames_and_selected_complement_resume_without_rechecking
    (choice : Bool) (word : Core.Word) (store : Core.Store) (additional : Nat) :
    (inputs choice word).runConditionalReturnBody? 2 body store = some (.word, .outOfFuel (deciding choice word store)) ∧
    Core.Steps (required choice - 2) (deciding choice word store) (Core.State.final (result choice word) store) ∧
    (inputs choice word).runConditionalReturnBody? (2 + additional) body store =
      some (.word, Core.runStateful additional (deciding choice word store)) ∧
    (inputs false word).runConditionalReturnBody? 5 body store = some (.word, .outOfFuel (complementing word store)) ∧
    Core.Steps 1 (complementing word store) (Core.State.final (.word word.bitNot) store) := by
  have exhausted : (inputs choice word).runConditionalReturnBody? 2 body store =
      some (.word, .outOfFuel (deciding choice word store)) := by
    rw [LocalInputs.runConditionalReturnBody?, checked]; cases choice <;> rfl
  have actual : Core.runStateful 2 (Core.State.initial core [.word word, .bool choice] store) =
      .outOfFuel (deciding choice word store) := by cases choice <;> rfl
  exact ⟨exhausted, ((costed choice word store).checked_residual_of_outOfFuel
      (checked choice word) (inputs choice word).sameIds actual).2,
    LocalInputs.runConditionalReturnBody?_resume exhausted additional,
    by rw [LocalInputs.runConditionalReturnBody?, checked]; rfl, .cons (.applyUnary rfl) .refl⟩

theorem structural_bound_is_conservative_for_the_shorter_selected_arm
    (choice : Bool) (word : Core.Word) (store : Core.Store) :
    conditionalReturnBodyFuelBound body = 6 ∧ required choice ≤ conditionalReturnBodyFuelBound body ∧
    (inputs choice word).runConditionalReturnBody? 6 body store = some (.word, .done (result choice word) store) ∧
    required true < conditionalReturnBodyFuelBound body := by
  have bound : conditionalReturnBodyFuelBound body = 6 := by
    simp [body, branch, returned, ref, conditionalReturnBodyFuelBound, returnBodyFuelBound, localExpressionFuelBound]
  have enough := (costed choice word store).cost_le_fuelBound
  exact ⟨bound, enough, (all_fuel_thresholds_keep_four_versus_six_steps_and_the_actual_store choice word store 6).1.mpr
    (by simpa only [bound] using enough), by simp [required, bound]⟩

private def sameArms := branch (returned (some (ref "x"))) (returned (some (ref "x")))
private theorem sameElaboration (choice : Bool) (type : Core.Ty) (value : Core.Value)
    (valueTyped : Core.ValueHasType value type) :
    ConditionalReturnBodyElaborates (supplied choice type value valueTyped).names
      (supplied choice type value valueTyped).context sameArms (.ifE (.var 1) (.var 0) (.var 0)) type :=
  .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head))
    (.expression (.identifier .head) (.var .head) (.var .head))
    (.expression (.identifier .head) (.var .head) (.var .head))

theorem arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation
    (choice : Bool) (type : Core.Ty) (value : Core.Value) (valueTyped : Core.ValueHasType value type)
    (store : Core.Store) :
    ConditionalReturnBodyHasType (supplied choice type value valueTyped).names
      (supplied choice type value valueTyped).context sameArms type ∧
    ConditionalReturnBodyEvaluates (supplied choice type value valueTyped).names
      (supplied choice type value valueTyped).environment store sameArms value store ∧
    (supplied choice type value valueTyped).runConditionalReturnBody? 4 sameArms store =
      some (type, .done value store) := by
  have check : (supplied choice type value valueTyped).checkConditionalReturnBody? sameArms =
      some (.ifE (.var 1) (.var 0) (.var 0), type) := (sameElaboration choice type value valueTyped).complete
  refine ⟨.intro (.identifier (.tail names_ne .head) (.tail ids_ne .head))
    (.expression (.identifier .head .head)) (.expression (.identifier .head .head)), ?_, ?_⟩
  · cases choice
    · exact .ifFalse (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.expression (.identifier .head .head))
    · exact .ifTrue (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.expression (.identifier .head .head))
  · rw [LocalInputs.runConditionalReturnBody?, check]
    cases choice <;> rfl

private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) := .closure .nil (.var rfl)

theorem unit_word_bool_cell_and_closure_values_keep_their_actual_identity
    (choice flag : Bool) (word : Core.Word) (location : Core.Location) (store : Core.Store) :
    (supplied choice .unit .unit .unit).runConditionalReturnBody? 4 sameArms store = some (.unit, .done .unit store) ∧
    (supplied choice .word (.word word) .word).runConditionalReturnBody? 4 sameArms store = some (.word, .done (.word word) store) ∧
    (supplied choice .bool (.bool flag) .bool).runConditionalReturnBody? 4 sameArms store = some (.bool, .done (.bool flag) store) ∧
    (supplied choice (.cell .word) (.cellRef .word location) .cellRef).runConditionalReturnBody? 4 sameArms store =
      some (.cell .word, .done (.cellRef .word location) store) ∧
    (supplied choice (.function .bool .bool) closure closureTyped).runConditionalReturnBody? 4 sameArms store =
      some (.function .bool .bool, .done closure store) :=
  ⟨(arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation choice .unit .unit .unit store).2.2,
    (arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation choice .word (.word word) .word store).2.2,
    (arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation choice .bool (.bool flag) .bool store).2.2,
    (arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation choice (.cell .word) (.cellRef .word location) .cellRef store).2.2,
    (arbitrary_existing_typed_values_are_returned_without_allocation_or_invocation choice (.function .bool .bool) closure closureTyped store).2.2⟩

private def bareArms := branch (returned none) (returned none)

theorem two_bare_returns_have_unit_type_and_four_step_selected_meaning
    (choice : Bool) (store : Core.Store) :
    ConditionalReturnBodyHasType (inputs choice .zero).names (inputs choice .zero).context bareArms .unit ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs choice .zero).names (inputs choice .zero).environment
      store bareArms .unit store 4 ∧
    (inputs choice .zero).runConditionalReturnBody? 4 bareArms store = some (.unit, .done .unit store) := by
  have elaboration : ConditionalReturnBodyElaborates (inputs choice .zero).names (inputs choice .zero).context
      bareArms (.ifE (.var 1) .unit .unit) .unit :=
    .intro (.identifier (.tail names_ne .head)) (.var (.tail ids_ne .head)) (.var (.tail ids_ne .head)) .bare .bare
  have check : (inputs choice .zero).checkConditionalReturnBody? bareArms = some (.ifE (.var 1) .unit .unit, .unit) :=
    elaboration.complete
  refine ⟨.intro (.identifier (.tail names_ne .head) (.tail ids_ne .head)) .bare .bare, ?_, ?_⟩
  · cases choice
    · exact .ifFalse (conditionCost false .zero store) .bare
    · exact .ifTrue (conditionCost true .zero store) .bare
  · rw [LocalInputs.runConditionalReturnBody?, check]; cases choice <;> rfl

private def missingArm := branch (returned (some (ref "x"))) (returned (some (ref "missing")))

theorem raw_success_skips_an_unresolved_arm_but_whole_checking_never_does
    (word : Core.Word) (store : Core.Store) (fuel : Nat) :
    ConditionalReturnBodyEvaluates (inputs true word).names (inputs true word).environment store missingArm (.word word) store ∧
    ConditionalReturnBodyEvaluatesWithCost (inputs true word).names (inputs true word).environment store missingArm (.word word) store 4 ∧
    (inputs true word).checkConditionalReturnBody? missingArm = none ∧
    (inputs true word).runConditionalReturnBody? fuel missingArm store = none := by
  have rejected : (inputs true word).checkConditionalReturnBody? missingArm = none := by
    simp [LocalInputs.checkConditionalReturnBody?, elaborateConditionalReturnBody?, missingArm, branch, returned,
      elaborateReturnBody?, elaborateLocalExpression?, resolveLocalExpression?, ref, inputs, supplied,
      LocalInputs.names, LocalInputs.context, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.ifTrue (conditionCost true word store).erase (.expression (valueCost true word store).erase),
    .ifTrue (conditionCost true word store) (.expression (valueCost true word store)),
    rejected, by simp only [LocalInputs.runConditionalReturnBody?, rejected, bind, Option.bind_none]⟩

private def boolAnnotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Bool"⟩, []⟩⟩⟩ none⟩
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "terminal"⟩, none,
    ⟨span, [⟨span, .typed none ⟨span, "c"⟩ boolAnnotation⟩]⟩, ⟨none, none⟩, none, none⟩, bareArms⟩⟩

theorem old_singleton_rejects_but_runtime_entry_compiles_conditional_statements
    (choice : Bool) (word : Core.Word) :
    (inputs choice word).checkReturnBody? body = none ∧
    RuntimeFunctionHeader [(["Bool"], .bool)] declaration.value.signature .unit ∧
    RuntimeParametersDeclare [(["Bool"], .bool)] owner declaration.value.signature.parameters.elements
      (LocalTypeInputs.empty.bindFresh owner "c" .bool) ∧
    compileRuntimeFunction? [(["Bool"], .bool)] owner declaration =
      some ⟨LocalTypeInputs.empty.bindFresh owner "c" .bool, .ifE (.var 0) .unit .unit, .unit⟩ := by
  have compilation : RuntimeFunctionCompiles [(["Bool"], .bool)] owner declaration
      ⟨LocalTypeInputs.empty.bindFresh owner "c" .bool, .ifE (.var 0) .unit .unit, .unit⟩ :=
    ⟨⟨rfl, rfl, rfl, rfl, .absent⟩,
      .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
      .conditional (.identifier .head) (.var .head) (.var .head) (.single .bare) (.single .bare)⟩
  exact ⟨rfl, compilation.header, compilation.parameters, compilation.complete⟩

end Tests.FrontendConditionalReturnBody
