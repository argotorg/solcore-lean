import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.RuntimeFunctionStoreProperties
import Solcore.Frontend.RuntimeFunctionFuelBoundProperties
import Solcore.Frontend.RuntimeFunctionResumptionProperties
import Solcore.Frontend.LocalExpressionResumptionProperties

/-! Independent unsigned Word ordering returns Bool while preserving strict operand
order, exact transition counts, and the complete checked entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordLess

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Less", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "less.sol"⟩, 19, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def less (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .less⟩ right⟩
private def source := less (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := (Core.Expr.var 1).wordLt (.var 0)
private theorem coreShape :
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) := by
  simp [core, Core.Expr.wordLt_expansion, Core.Expr.weakenAt]
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .less (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .less (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.wordLt (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store 11 :=
  .less (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independent_bool_typing_evaluation_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left < right))) store 11 ∧
    Core.Steps 11 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (decide (left < right))) store) :=
  ⟨typed left right, checked left right,
    .less (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head),
    costed left right store, (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

private def firstBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.letBody (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1)))
    [.word right, .word left]], store⟩
private def secondBinding (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word right), [.letBody (.binary .wordGt (.var 0) (.var 1))
    [.word left, .word right, .word left]], store⟩
private def pending (left right : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word left), [.binaryApply .wordGt (.word right)], store⟩

theorem exact_resolved_and_core_shapes_keep_original_children_and_ordered_generated_bindings
    (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.wordLt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) ∧
    core = .letE (.var 1) (.letE (.var 1) (.binary .wordGt (.var 0) (.var 1))) :=
  ⟨resolved left right, coreShape⟩

theorem genuine_checkpoints_retain_left_then_right_before_the_reversed_primitive
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 2 source store = some (.bool, .outOfFuel (firstBinding left right store)) ∧
    (inputs left right).run? 5 source store = some (.bool, .outOfFuel (secondBinding left right store)) ∧
    (inputs left right).run? 10 source store = some (.bool, .outOfFuel (pending left right store)) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [LocalInputs.run?, checked, coreShape] <;> rfl

theorem all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair
    (left right : Core.Word) (store : Core.Store) (fuel : Nat) :
    ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (decide (left < right))) store) ↔ 11 ≤ fuel) ∧
    ((∃ checkpoint, (inputs left right).run? fuel source store =
      some (.bool, .outOfFuel checkpoint)) ↔ fuel < 11) := by
  have path := (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds
  constructor
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_done_iff (fuel := fuel)
  · simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using path.runStateful_outOfFuel_iff (fuel := fuel)

theorem equal_strict_and_reverse_orders_never_return_word_flags
    (left right : Core.Word) (strict : left < right) (fuel : Nat) (store : Core.Store) :
    ((inputs left left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 11 ≤ fuel) ∧
    ((inputs left right).run? fuel source store = some (.bool, .done (.bool true) store) ↔ 11 ≤ fuel) ∧
    ((inputs right left).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 11 ≤ fuel) ∧
    ∀ word, Core.Value.bool (decide (left < right)) ≠ .word word := by
  have reversed : ¬right < left := Nat.not_lt.mpr (Nat.le_of_lt strict)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair left left store fuel).1
  · simpa [strict] using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair left right store fuel).1
  · simpa [reversed] using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair right left store fuel).1
  · intro word same; cases same

theorem zero_high_bit_and_maximum_distinguish_unsigned_order (store : Core.Store) :
    (inputs .zero (Core.Word.ofNatModulo (2 ^ 255))).run? 11 source store = some (.bool, .done (.bool true) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 11 source store = some (.bool, .done (.bool false) store) ∧
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .maximum).run? 11 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .maximum (Core.Word.ofNatModulo (2 ^ 255))).run? 11 source store = some (.bool, .done (.bool false) store) ∧
    (inputs .maximum .maximum).run? 11 source store = some (.bool, .done (.bool false) store) := by
  have first := equal_strict_and_reverse_orders_never_return_word_flags
    .zero (Core.Word.ofNatModulo (2 ^ 255)) (by decide) 11 store
  have second := equal_strict_and_reverse_orders_never_return_word_flags
    (Core.Word.ofNatModulo (2 ^ 255)) .maximum (by decide) 11 store
  exact ⟨first.2.1.mpr (by decide), first.2.2.1.mpr (by decide),
    second.2.1.mpr (by decide), second.2.2.1.mpr (by decide),
    by simpa using (all_fuel_thresholds_count_eleven_steps_for_every_actual_word_pair .maximum .maximum store 11).1.mpr (by decide)⟩

theorem genuine_checkpoints_have_exact_residuals_and_same_state_resumption
    (left right : Core.Word) (store : Core.Store) (additional : Nat) :
    Core.Steps 9 (firstBinding left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.Steps 6 (secondBinding left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.Steps 1 (pending left right store) (Core.State.final (.bool (decide (left < right))) store) ∧
    Core.runStateful 3 (firstBinding left right store) = .outOfFuel (secondBinding left right store) ∧
    (inputs left right).run? (5 + additional) source store =
      some (.bool, Core.runStateful additional (secondBinding left right store)) ∧
    (inputs left right).run? (10 + additional) source store =
      some (.bool, Core.runStateful additional (pending left right store)) := by
  have first : Core.runStateful 2 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (firstBinding left right store) := by rw [coreShape]; rfl
  have second : Core.runStateful 5 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (secondBinding left right store) := by rw [coreShape]; rfl
  have last : Core.runStateful 10 (Core.State.initial core [.word right, .word left] store) =
      .outOfFuel (pending left right store) := by rw [coreShape]; rfl
  have firstResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds first
  have secondResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds second
  have lastResidual := (costed left right store).checked_residual_of_outOfFuel
    (checked left right) (inputs left right).sameIds last
  have checkpoints := genuine_checkpoints_retain_left_then_right_before_the_reversed_primitive left right store
  exact ⟨firstResidual.2, secondResidual.2, lastResidual.2, rfl,
    LocalInputs.run?_resume checkpoints.2.1 additional, LocalInputs.run?_resume checkpoints.2.2 additional⟩

theorem independent_less_requires_both_ordered_word_operands
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (less left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (decide (leftWord < rightWord)) ∧ cost = leftCost + rightCost + 9 := by
  cases evaluation with
  | less leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem missing_either_operand_is_not_bypassed_by_equal_known_values :
    (inputs .zero .zero).check? (less (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (less (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, less, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

private def typedInputs (leftType rightType : Core.Ty) (left right : Core.Value)
    (leftTyped : Core.ValueHasType left leftType) (rightTyped : Core.ValueHasType right rightType) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" leftType left leftTyped).bindFresh owner "r" rightType right rightTyped

theorem non_word_on_either_side_is_rejected_without_polymorphic_less
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
      | less first second =>
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

theorem less_preserves_unrelated_inputs_and_ignores_only_spans_and_injective_ids
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store)
    (otherSpan otherOperatorSpan : Syntax.SourceSpan) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (decide (left < right))) store 11 ∧
    resolveLocalExpression? (inputs left right).names source = resolveLocalExpression? (inputs left right).names
      ⟨otherSpan, .binary (ref "l") ⟨otherOperatorSpan, .less⟩ (ref "r")⟩ := by
  have avoids : AvoidsLocalName "unused" source := .less (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    resolveLocalExpression?_less_spans _ _ _ _ _ _ _⟩

theorem arbitrary_identity_maps_preserve_structural_resolution_without_fresh_names
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId) :
    ResolvesLocalExpression (LocalNameTable.mapIds mapping (inputs left right).names) source
      (.wordLt (.var (mapping ⟨owner, 0⟩)) (.var (mapping ⟨owner, 1⟩))) := by
  simpa only [Resolved.Expr.renameIds] using (resolved left right).mapIds mapping

theorem replay_structural_budget_and_type_erasure_preserve_the_source_contract
    (left right : Core.Word) (first replacement : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      replacement source (.bool (decide (left < right))) replacement 11 ∧
    11 ≤ localExpressionFuelBound source ∧ localExpressionFuelBound source = 11 ∧
    (inputs left right).toTypeInputs.names = (inputs left right).names ∧
    (inputs left right).toTypeInputs.context = (inputs left right).context := by
  have replayed := (costed left right first).change_store replacement
  exact ⟨replayed, replayed.cost_le_fuelBound, by simp [source, less, ref, localExpressionFuelBound],
    (inputs left right).toTypeInputs_names, (inputs left right).toTypeInputs_context⟩

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "less"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
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
    .single <| .expression (.less (.identifier (.tail names_ne .head)) (.identifier .head))
      (.wordLt (.var (.tail ids_ne .head)) (.var .head))
      (.wordLt (.var (.tail ids_ne .head)) (.var .head))⟩
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
      store .bool (.bool (decide (left < right))) store 11 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (decide (left < right))) store) ↔ 11 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left < right))) store 11 :=
    .intro (preparation left right) (.single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem declared_word_return_rejects_a_bool_less_result :
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

end Tests.FrontendWordLess
