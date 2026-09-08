import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.LocalExpressionResumptionProperties

/-! Independent Word-only equality returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordEquality

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Equality", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "equality.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def equal (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .equal⟩ right⟩
private def source := equal (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordEq (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordEq (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .equal (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .equal (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store 5 :=
  .equal (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (left == right)) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (left == right)) store) :=
  ⟨typed left right, checked left right,
    .equal (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_fuel_four_checkpoint_preserves_left_and_right_operand_order
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (left == right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem equality_and_inequality_still_need_five_steps_and_return_no_word_flag
    (left right : Core.Word) (different : left ≠ right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 5 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 5 ≤ fuel) ∧
    ∀ word, Core.Value.bool (left == right) ≠ .word word := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left left store).2 fuel
  · have unequal : (left == right) = false := beq_eq_false_iff_ne.mpr different
    simpa only [unequal] using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left right store).2 fuel
  · intro word same; cases same

theorem zero_high_bit_and_maximum_keep_exact_word_equality (store : Core.Store) :
    (inputs .zero .zero).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .maximum).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 5 source store =
      some (.bool, .done (.bool false) store) ∧
    (inputs .zero .maximum).run? 5 source store = some (.bool, .done (.bool false) store) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .zero .zero store).2 5 |>.mpr (by decide)
  · simpa using (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .maximum .maximum store).2 5 |>.mpr (by decide)
  · have unequal : (Core.Word.ofNatModulo (2 ^ 255) == Core.Word.zero) = false := by decide
    exact ((exact_fuel_four_checkpoint_preserves_left_and_right_operand_order
      (Core.Word.ofNatModulo (2 ^ 255)) .zero store).2 5 |>.mpr (by decide)).trans
        (congrArg (fun result => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool result) store)) unequal)
  · have unequal : (Core.Word.zero == Core.Word.maximum) = false := by decide
    exact ((exact_fuel_four_checkpoint_preserves_left_and_right_operand_order .zero .maximum store).2 5 |>.mpr (by decide)).trans
      (congrArg (fun result => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool result) store)) unequal)

theorem independent_equality_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (equal left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (leftWord == rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | equal leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (equal (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (equal (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, equal, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_equality
    (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType)
    (wrong : leftType ≠ .word ∨ rightType ≠ .word) (fuel : Nat) (store : Core.Store) :
    (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none ∧
    (typedInputs leftType rightType left right leftTyped rightTyped).run? fuel source store = none := by
  have rejected : (typedInputs leftType rightType left right leftTyped rightTyped).check? source = none := by
    cases accepted : (typedInputs leftType rightType left right leftTyped rightTyped).check? source with
    | none => rfl
    | some result =>
      rcases result with ⟨compiledCore, resultType⟩
      have whole := LocalInputs.check?_iff_hasType.mp ⟨compiledCore, accepted⟩
      cases whole with
      | equal first second =>
        have firstTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "l") leftType :=
          .identifier (.tail names_ne .head) (.tail ids_ne .head)
        have secondTyped : LocalExpressionHasType
            (typedInputs leftType rightType left right leftTyped rightTyped).names
            (typedInputs leftType rightType left right leftTyped rightTyped).context (ref "r") rightType :=
          .identifier .head .head
        exact False.elim (wrong.elim (fun mismatch => mismatch (firstTyped.type_unique first))
          (fun mismatch => mismatch (secondTyped.type_unique second)))
  exact ⟨rejected, (LocalInputs.run?_eq_none_iff fuel store).mpr rejected⟩

theorem symmetric_final_equality_does_not_permit_swapping_pending_operands
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    Core.runStateful 5 (Core.State.initial core [.word right, .word left] store) =
      Core.runStateful 5 (Core.State.initial (.binary .wordEq (.var 0) (.var 1)) [.word right, .word left] store) ∧
    Core.runStateful 4 (Core.State.initial core [.word right, .word left] store) ≠
      Core.runStateful 4 (Core.State.initial (.binary .wordEq (.var 0) (.var 1)) [.word right, .word left] store) := by
  constructor
  · change Core.StatefulRunResult.done (.bool (left == right)) store = .done (.bool (right == left)) store
    rw [beq_eq_false_iff_ne.mpr different, beq_eq_false_iff_ne.mpr (Ne.symm different)]
  · intro same
    have controls := congrArg Core.State.control (Core.StatefulRunResult.outOfFuel.inj same)
    exact different (Core.Value.word.inj (Core.Control.ret.inj controls)).symm

theorem equality_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (left == right)) store 5 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .equal⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .equal (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_equal_spans _ _ _ _ _ _ _⟩

theorem replay_structural_budget_and_checkpoint_residual_keep_boolean_equality
    (left right : Core.Word) (first replacement : Core.Store) (additional : Nat) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (left == right)) replacement 5 ∧
    5 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 5 ∧
    Core.Steps 1 ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩
      (Core.State.final (.bool (left == right)) replacement) ∧
    (inputs left right).run? (4 + additional) source replacement = some (.bool,
      Core.runStateful additional ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩) := by
  have replayed := (costed left right first).change_store replacement
  have exhausted := (exact_fuel_four_checkpoint_preserves_left_and_right_operand_order left right replacement).1
  have coreExhausted : Core.runStateful 4 (Core.State.initial core [.word right, .word left] replacement) =
      .outOfFuel ⟨.ret (.word right), [.binaryApply .wordEq (.word left)], replacement⟩ := rfl
  refine ⟨replayed, replayed.cost_le_fuelBound, ?_,
    (replayed.checked_residual_of_outOfFuel (checked left right) (inputs left right).sameIds coreExhausted).2,
    LocalInputs.run?_resume exhausted additional⟩
  simp [source, equal, ref, localExpressionFuelBound]

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "equal"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation returnName]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .bool⟩
private theorem wordAnnotation : TypeNameDenotes types (annotation "Word") .word :=
  .named (.tail (by decide) .head)
private theorem compilation : RuntimeFunctionCompiles types owner (declaration "Bool") compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons wordAnnotation (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons wordAnnotation (by change "r" ∉ ["l"]; simp) .nil),
    .terminal <| .single <| .expression (.equal (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ :=
  ⟨compilation.header,
    .cons wordAnnotation (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons wordAnnotation (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_compilation_preparation_and_exact_bool_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (left == right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (left == right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (left == right)) store 5 :=
    .intro (preparation left right) (.terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_equality_result :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs := accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordEquality
