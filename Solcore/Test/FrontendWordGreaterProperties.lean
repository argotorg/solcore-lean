import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties
import Solcore.Core.DirectWordComparisons

/-! Independent unsigned comparison changes the result type, not operand order,
strict checking, exact machine frames, or the whole entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordGreater

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Greater", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "greater.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def greater (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .greater⟩ right⟩
private def source := greater (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordGt (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordGt (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .greater (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool :=
  .greater (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .bool) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store 5 :=
  .greater (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_produce_independently_typed_booleans_and_exact_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .bool ∧
    (inputs left right).check? source = some (core, .bool) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.bool (decide (left > right))) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.bool (decide (left > right))) store) :=
  ⟨typed left right, checked left right, (costed left right store).erase, costed left right store,
    (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_completion_and_ordered_four_step_state
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.bool, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordGt (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem equal_words_still_take_five_steps (value : Core.Word) (fuel : Nat) (store : Core.Store) :
    ((inputs value value).run? fuel source store = some (.bool, .done (.bool false) store) ↔ 5 ≤ fuel) := by
  simpa using (exact_completion_and_ordered_four_step_state value value store).2 fuel

theorem unsigned_high_bit_and_maximum_are_greater_than_zero (store : Core.Store) :
    (inputs (Core.Word.ofNatModulo (2 ^ 255)) .zero).run? 5 source store =
      some (.bool, .done (.bool true) store) ∧
    (inputs .maximum .zero).run? 5 source store = some (.bool, .done (.bool true) store) ∧
    (inputs .zero .maximum).run? 5 source store = some (.bool, .done (.bool false) store) := by
  have high : decide (Core.Word.ofNatModulo (2 ^ 255) > Core.Word.zero) = true := by decide
  have maximum : decide (Core.Word.maximum > Core.Word.zero) = true := by decide
  have reversed : decide (Core.Word.zero > Core.Word.maximum) = false := by decide
  refine ⟨?_, ?_, ?_⟩
  · exact ((exact_completion_and_ordered_four_step_state
      (Core.Word.ofNatModulo (2 ^ 255)) .zero store).2 5 |>.mpr (by decide)).trans
      (congrArg (fun value => some (Core.Ty.bool, Core.StatefulRunResult.done (.bool value) store)) high)
  · simpa only [maximum] using
      (exact_completion_and_ordered_four_step_state .maximum .zero store).2 5 |>.mpr (by decide)
  · simpa only [reversed] using
      (exact_completion_and_ordered_four_step_state .zero .maximum store).2 5 |>.mpr (by decide)

theorem successful_comparison_requires_ordered_words_and_boolean_result
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (greater left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .bool (decide (leftWord > rightWord)) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | greater leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem zero_does_not_bypass_missing_operands :
    (inputs .zero .zero).check? (greater (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (greater (ref "missing") (ref "r")) = none := by
  constructor <;> simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, greater, ref,
    inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]

theorem unused_inputs_and_injective_ids_preserve_comparison
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.bool (decide (left > right))) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel source store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔
      (inputs left right).run? fuel source store = some (.bool, .done (.bool (decide (left > right))) store)) := by
  have avoids : AvoidsLocalName "unused" source := .greater (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def guarded : Syntax.Expr :=
  ⟨span, .conditional (greater ⟨span, .binary (ref "l") ⟨span, .multiply⟩ (ref "r")⟩ (ref "r")) span
    ⟨span, .binary (ref "l") ⟨span, .subtract⟩ (ref "r")⟩ span (ref "l")⟩
private def guardedCore : Core.Expr := .ifE
  (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
  (.binary .wordSub (.var 1) (.var 0)) (.var 1)

theorem arithmetic_comparison_selects_a_branch_with_exact_cost
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context guarded .word ∧
    (inputs left right).check? guarded = some (guardedCore, .word) ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store guarded (.word (if left.mul right > right then left.sub right else left)) store
      (if left.mul right > right then 16 else 12) ∧
    ∀ fuel, ((inputs left right).run? fuel guarded store =
      some (.word, .done (.word (if left.mul right > right then left.sub right else left)) store) ↔
      (if left.mul right > right then 16 else 12) ≤ fuel) := by
  have leftTyped : LocalExpressionHasType (inputs left right).names (inputs left right).context (ref "l") .word :=
    .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have rightTyped : LocalExpressionHasType (inputs left right).names (inputs left right).context (ref "r") .word :=
    .identifier .head .head
  have typing : LocalExpressionHasType (inputs left right).names (inputs left right).context guarded .word :=
    .conditional (.greater (.multiply leftTyped rightTyped) rightTyped) (.subtract leftTyped rightTyped) leftTyped
  have resolution : ResolvesLocalExpression (inputs left right).names guarded
      (.ifE (.binary .wordGt (.binary .wordMul (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) (.var ⟨owner, 1⟩))
        (.binary .wordSub (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) (.var ⟨owner, 0⟩)) :=
    .conditional (.greater (.multiply (.identifier (.tail names_ne .head)) (.identifier .head)) (.identifier .head))
      (.subtract (.identifier (.tail names_ne .head)) (.identifier .head)) (.identifier (.tail names_ne .head))
  have accepted : (inputs left right).check? guarded = some (guardedCore, .word) :=
    elaborateLocalExpression?_complete resolution
      (.ifE (.binary (.binary (.var (.tail ids_ne .head)) (.var .head)) (.var .head))
        (.binary (.var (.tail ids_ne .head)) (.var .head)) (.var (.tail ids_ne .head)))
      (resolution.preserves_type typing)
  have leftCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "l") (.word left) store 1 := .identifier (.tail names_ne .head) (.tail ids_ne .head)
  have rightCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (ref "r") (.word right) store 1 := .identifier .head .head
  have guardCost : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (greater ⟨span, .binary (ref "l") ⟨span, .multiply⟩ (ref "r")⟩ (ref "r"))
      (.bool (decide (left.mul right > right))) store 9 :=
    .greater (leftCost := 5) (rightCost := 1) (.multiply leftCost rightCost) rightCost
  have evaluation : LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store guarded (.word (if left.mul right > right then left.sub right else left)) store
      (if left.mul right > right then 16 else 12) := by
    by_cases selected : left.mul right > right
    · simp only [if_pos selected]
      exact .ifTrue (by simpa [selected] using guardCost) (.subtract leftCost rightCost)
    · simp only [if_neg selected]
      exact .ifFalse (by simpa [selected] using guardCost) leftCost
  refine ⟨typing, accepted, evaluation, ?_⟩
  intro fuel
  simpa only [LocalInputs.run?, accepted, bind, Option.bind_some, pure,
    Option.some.injEq, Prod.mk.injEq, true_and] using
    evaluation.checked_runStateful_done_iff (fuel := fuel) accepted (inputs left right).sameIds

private def annotation (name : String) : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, name⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter :=
  ⟨span, .typed none ⟨span, name⟩ (annotation "Word")⟩
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def declaration (returnName : String) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "greater"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
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
    .expression (.greater (.identifier (.tail names_ne .head)) (.identifier .head))
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

theorem independent_compilation_preparation_and_exact_boolean_entry_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration "Bool") compiled ∧
    compileRuntimeFunction? types owner (declaration "Bool") = some compiled ∧
    RuntimeFunctionPrepares types owner (declaration "Bool") (arguments left right)
      ⟨inputs left right, core, .bool⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left > right))) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration "Bool") (arguments left right) fuel store =
      some (.bool, .done (.bool (decide (left > right))) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration "Bool") (arguments left right)
      store .bool (.bool (decide (left > right))) store 5 :=
    .intro (preparation left right) (.expression (costed left right store))
  exact ⟨compilation, compilation.complete, preparation left right, evaluation, fun _ => evaluation.run_done_iff⟩

theorem word_return_annotation_rejects_a_boolean_comparison :
    compileRuntimeFunction? types owner (declaration "Word") = none := by
  apply compileRuntimeFunction?_eq_none_iff.mpr
  intro ⟨candidate, accepted⟩
  have sameInputs : candidate.inputs = compiled.inputs :=
    accepted.parameters.result_unique compilation.parameters
  have expectedHeader : RuntimeFunctionHeader types (declaration "Word").value.signature .word :=
    ⟨rfl, rfl, rfl, rfl, .single wordAnnotation⟩
  have sameReturn : candidate.returnType = .word := accepted.header.type_unique expectedHeader
  have candidateBody := accepted.body
  rw [sameInputs] at candidateBody
  have bodyReturn : candidate.returnType = .bool := (candidateBody.result_unique compilation.body).2
  cases sameReturn.symm.trans bodyReturn

end Tests.FrontendWordGreater
