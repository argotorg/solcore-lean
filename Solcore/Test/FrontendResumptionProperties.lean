import Solcore.Frontend.RuntimeFunctionResumptionProperties

/-! Independent source costs and actual machine frames witness exact suffix
execution. Resuming is not reinitializing or discarding a pending continuation. -/

set_option autoImplicit false

namespace Tests.FrontendResumption

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Resumption", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "resumption.sol"⟩, 17, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩
private def subtraction : Syntax.Expr := ⟨span, .binary (ref "l") ⟨span, .subtract⟩ (ref "r")⟩
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordSub (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem checked (left right : Core.Word) :
    (inputs left right).check? subtraction = some (core, .word) :=
  elaborateLocalExpression?_complete
    (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store subtraction (.word (left.sub right)) store 5 :=
  .subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private def beforeRight (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryRight .wordSub (.var 0) [.word right, .word left]], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.binaryApply .wordSub (.word left)], store⟩

theorem genuine_binary_checkpoint_retains_exactly_one_transition
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    (Core.runStateful additional (pending left right store) = .done (.word (left.sub right)) store ↔
      1 ≤ additional) ∧
    ((∃ checkpoint, Core.runStateful additional (pending left right store) = .outOfFuel checkpoint) ↔
      additional < 1) := by
  have exhausted : Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) := rfl
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  exact ⟨exhausted, (path.residual_of_outOfFuel exhausted).2,
    path.resumed_done_iff exhausted, path.resumed_outOfFuel_iff exhausted⟩

theorem checked_local_and_singleton_return_resume_the_actual_pending_frame
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    4 < 5 ∧ Core.Steps 1 (pending left right store) (Core.State.final (.word (left.sub right)) store) ∧
    (inputs left right).run? (4 + additional) subtraction store =
      some (.word, Core.runStateful additional (pending left right store)) ∧
    (inputs left right).runReturnBody? (4 + additional) (body subtraction) store =
      some (.word, Core.runStateful additional (pending left right store)) ∧
    (Core.runStateful additional (pending left right store) = .done (.word (left.sub right)) store ↔
      1 ≤ additional) := by
  have exhausted := (genuine_binary_checkpoint_retains_exactly_one_transition left right store additional).1
  have checkedResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds exhausted
  have rawResidual := (costed left right store).residual_of_outOfFuel
    (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
    (.binary (.var (.tail ids_ne .head)) (.var .head)) exhausted
  have bodyCost : ReturnBodyEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (body subtraction) (.word (left.sub right)) store 5 := .expression (costed left right store)
  have bodyChecked : (inputs left right).checkReturnBody? (body subtraction) = some (core, .word) :=
    checked left right
  have bodyResidual := bodyCost.checked_residual_of_outOfFuel bodyChecked (inputs left right).sameIds exhausted
  have localExhausted : (inputs left right).run? 4 subtraction store =
      some (.word, .outOfFuel (pending left right store)) := by
    rw [LocalInputs.run?, checked]; rfl
  have bodyExhausted : (inputs left right).runReturnBody? 4 (body subtraction) store =
      some (.word, .outOfFuel (pending left right store)) := by
    rw [LocalInputs.runReturnBody?, bodyChecked]; rfl
  exact ⟨checkedResidual.1, rawResidual.2, LocalInputs.run?_resume localExhausted additional,
    LocalInputs.runReturnBody?_resume bodyExhausted additional, bodyResidual.2.runStateful_done_iff⟩

theorem two_chunk_continuation_equals_one_larger_run_including_suspended_states
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (beforeRight left right store) ∧
    Core.runStateful 2 (beforeRight left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (2 + additional) (beforeRight left right store) ∧
    Core.runStateful additional (pending left right store) =
      Core.runStateful (4 + additional) (Core.State.initial core [.word right, .word left] store) := by
  have first : Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (beforeRight left right store) := rfl
  have second : Core.runStateful 2 (beforeRight left right store) = .outOfFuel (pending left right store) := rfl
  refine ⟨first, second, Core.runStateful_resume second additional, ?_⟩
  simpa only [← Nat.add_assoc] using (Core.runStateful_resume second additional).trans
    (Core.runStateful_resume first (2 + additional))

theorem dropping_the_binary_frame_changes_zero_fuel_recognition_and_the_value
    (left right : Core.Word) (different : left.sub right ≠ right) (store : Core.Store) :
    Core.runStateful 0 (pending left right store) = .outOfFuel (pending left right store) ∧
    Core.runStateful 0 ⟨.ret (.word right), [], store⟩ = .done (.word right) store ∧
    Core.runStateful 1 (pending left right store) = .done (.word (left.sub right)) store ∧
    Core.runStateful 0 ⟨.ret (.word right), [], store⟩ ≠ Core.runStateful 1 (pending left right store) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro same
  exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj same).1).symm

private def booleanInputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool
private def booleanSource : Syntax.Expr :=
  ⟨span, .binary (ref "c") ⟨span, .logicalAnd⟩ ⟨span, .unary ⟨span, .logicalNot⟩ (ref "c")⟩⟩
private def booleanCore : Core.Expr := .ifE (.var 0) (.unary .boolNot (.var 0)) (.bool false)
private theorem booleanChecked (choice : Bool) :
    (booleanInputs choice).check? booleanSource = some (booleanCore, .bool) :=
  elaborateLocalExpression?_complete (.logicalAnd (.identifier .head) (.logicalNot (.identifier .head)))
    (.ifE (.var .head) (.unary (.var .head)) .bool)
    (.ifE (.var .head) (.unary (.var .head)) .bool)
private theorem booleanCost (choice : Bool) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (booleanInputs choice).names (booleanInputs choice).environment
      store booleanSource (.bool false) store (if choice then 6 else 4) := by
  cases choice
  · exact .andFalse (.identifier .head .head)
  · have leaf : LocalExpressionEvaluatesWithCost (booleanInputs true).names (booleanInputs true).environment
        store (ref "c") (.bool true) store 1 := .identifier .head .head
    exact .andTrue leaf (.logicalNot leaf)
private def booleanCheckpoint (choice : Bool) (store : Core.Store) : Core.State :=
  if choice then ⟨.ret (.bool true), [.unaryApply .boolNot], store⟩
  else ⟨.eval (.bool false) [.bool false], [], store⟩

theorem short_circuit_paths_retain_different_checkpoints_with_the_same_remaining_cost
    (choice : Bool) (store : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (booleanInputs choice).names (booleanInputs choice).environment
      store booleanSource (.bool false) store (if choice then 6 else 4) ∧
    Core.runStateful (if choice then 5 else 3) (Core.State.initial booleanCore [.bool choice] store) =
      .outOfFuel (booleanCheckpoint choice store) ∧
    Core.Steps 1 (booleanCheckpoint choice store) (Core.State.final (.bool false) store) ∧
    (Core.runStateful additional (booleanCheckpoint choice store) = .done (.bool false) store ↔
      1 ≤ additional) := by
  have exhausted : Core.runStateful (if choice then 5 else 3)
      (Core.State.initial booleanCore [.bool choice] store) = .outOfFuel (booleanCheckpoint choice store) := by
    cases choice <;> rfl
  have path := (booleanCost choice store).checked_toSteps (booleanChecked choice) (booleanInputs choice).sameIds
  have residual := (path.residual_of_outOfFuel exhausted).2
  have remaining : (if choice then 6 else 4) - (if choice then 5 else 3) = 1 := by cases choice <;> rfl
  rw [remaining] at residual
  exact ⟨booleanCost choice store, exhausted, residual, residual.runStateful_done_iff⟩

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
private def prepared (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    PreparedRuntimeFunction := ⟨LocalInputs.empty.bindFresh owner "x" type value typed, .var 0, type⟩
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem preparation (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    RuntimeFunctionPrepares (types type) owner declaration [argument type value typed] (prepared type value typed) :=
  ⟨(compilation type).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil, (compilation type).body⟩

theorem independent_entry_and_compilation_resume_the_actual_argument_from_zero_spent
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (additional : Nat) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 ∧
    runRuntimeFunction? (types type) owner declaration [argument type value typed] 0 store =
      some (type, .outOfFuel (Core.State.initial (.var 0) [value] store)) ∧
    Core.Steps 1 (Core.State.initial (.var 0) [value] store) (Core.State.final value store) ∧
    (Core.runStateful additional (Core.State.initial (.var 0) [value] store) = .done value store ↔
      1 ≤ additional) ∧
    runRuntimeFunction? (types type) owner declaration [argument type value typed] additional store =
      some (type, Core.runStateful additional (Core.State.initial (.var 0) [value] store)) := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 := .intro (preparation type value typed) (.expression (.identifier .head .head))
  have exhausted : runRuntimeFunction? (types type) owner declaration [argument type value typed] 0 store =
      some (type, .outOfFuel (Core.State.initial (.var 0) [value] store)) := by
    rw [runRuntimeFunction?, (preparation type value typed).complete]; rfl
  have sourceResidual := evaluated.residual_of_outOfFuel exhausted
  have compiledResidual := evaluated.compiled_residual_of_outOfFuel (compilation type)
    (show Core.runStateful 0 (Core.State.initial (.var 0) [value] store) =
      .outOfFuel (Core.State.initial (.var 0) [value] store) from rfl)
  refine ⟨evaluated, exhausted, sourceResidual.2, compiledResidual.2.runStateful_done_iff, ?_⟩
  simpa only [Nat.zero_add] using runRuntimeFunction?_resume exhausted additional

private def illTypedCore : Core.Expr := .binary .wordSub (.bool true) (.word .zero)
private def beforeFault (store : Core.Store) : Core.State :=
  ⟨.eval (.word .zero) [], [.binaryApply .wordSub (.bool true)], store⟩
private def faultState (store : Core.Store) : Core.State :=
  ⟨.ret (.word .zero), [.binaryApply .wordSub (.bool true)], store⟩

theorem generic_core_resumption_also_preserves_faults_without_frontend_acceptance
    (store : Core.Store) (additional : Nat) :
    Core.runStateful 3 (Core.State.initial illTypedCore [] store) = .outOfFuel (beforeFault store) ∧
    Core.runStateful 1 (beforeFault store) =
      .fault (.invalidBinaryOperands .wordSub (.bool true) (.word .zero)) (faultState store) ∧
    Core.runStateful additional (beforeFault store) =
      Core.runStateful (3 + additional) (Core.State.initial illTypedCore [] store) :=
  ⟨rfl, rfl, Core.runStateful_resume rfl additional⟩

end Tests.FrontendResumption
