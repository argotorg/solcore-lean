import Solcore.Frontend.LocalInputsCostInvariance
import Solcore.Frontend.LocalInputsRenamingProperties
import Solcore.Frontend.RuntimeFunctionPreparationFactorization
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties
import Solcore.Core.ModularArithmetic

/-! Independent strict Word addition retains actual Core, operand order,
modular results, and exact costs through local and function-entry adapters. -/

set_option autoImplicit false

namespace Tests.FrontendWordAddition

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Addition", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "addition.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def add (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, .add⟩ right⟩
private def source := add (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core : Core.Expr := .binary .wordAdd (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names source
      (.binary .wordAdd (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) :=
  .add (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .word :=
  .add (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (left right : Core.Word) :
    (inputs left right).check? source = some (core, .word) :=
  elaborateLocalExpression?_complete (resolved left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved left right).preserves_type (typed left right))
private theorem costed (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store 5 :=
  .add (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
    (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_evaluation_and_exact_core_steps
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context source .word ∧
    (inputs left right).check? source = some (core, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store source (.word (left.add right)) store 5 ∧
    Core.Steps 5 (Core.State.initial core [.word right, .word left] store)
      (Core.State.final (.word (left.add right)) store) :=
  ⟨typed left right, checked left right, (costed left right store).erase, costed left right store,
    (costed left right store).checked_toSteps (checked left right) (inputs left right).sameIds⟩

theorem exact_completion_and_the_ordered_four_step_suspended_state
    (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 source store = some (.word, .outOfFuel
      ⟨.ret (.word right), [.binaryApply .wordAdd (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel source store =
      some (.word, .done (.word (left.add right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked left right) (inputs left right).sameIds

theorem maximum_plus_one_wraps_but_does_not_fold_away_the_binary_core (store : Core.Store) :
    (inputs .maximum (Core.Word.ofNatModulo 1)).check? source = some (core, .word) ∧
    (inputs .maximum (Core.Word.ofNatModulo 1)).run? 5 source store =
      some (.word, .done (.word .zero) store) := by
  refine ⟨checked _ _, ?_⟩
  simpa only [Core.Word.add_maximum_one] using
    (exact_completion_and_the_ordered_four_step_suspended_state .maximum
      (Core.Word.ofNatModulo 1) store).2 5 |>.mpr (by decide)

theorem successful_addition_requires_both_ordered_word_children
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (add left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .word (leftWord.add rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases evaluation with
  | add leftEvaluation rightEvaluation => exact ⟨_, _, _, _, _, leftEvaluation, rightEvaluation, rfl, rfl⟩

theorem zero_does_not_bypass_an_unresolved_operand (store : Core.Store) :
    (inputs .zero .zero).check? (add (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (add (ref "missing") (ref "r")) = none ∧
    ∀ value finalStore, ¬ LocalExpressionEvaluates (inputs .zero .zero).names
      (inputs .zero .zero).environment store (add (ref "l") (ref "missing")) value finalStore := by
  have rightMissing : (inputs .zero .zero).check? (add (ref "l") (ref "missing")) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, add, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  have leftMissing : (inputs .zero .zero).check? (add (ref "missing") (ref "r")) = none := by
    simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, add, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  refine ⟨rightMissing, leftMissing, ?_⟩
  intro value finalStore evaluation
  cases evaluation with
  | add _ rightEvaluation =>
      cases rightEvaluation with
      | identifier named _ =>
          have found := LocalNameTable.lookup?_iff.mpr named
          have absent : (inputs .zero .zero).names.lookup? "missing" = none := rfl
          rw [absent] at found
          cases found

theorem unused_inputs_and_injective_ids_preserve_addition_cost_and_observations
    (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel source store =
      (inputs left right).run? fuel source store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store source (.word (left.add right)) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel source store =
      some (.word, .done (.word (left.add right)) store) ↔
      (inputs left right).run? fuel source store = some (.word, .done (.word (left.add right)) store)) := by
  have avoids : AvoidsLocalName "unused" source := .add (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel source store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def types : TypeNameTable := [(["Word"], .word)]
private def declaration : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "sum"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some source)⟩]⟩⟩⟩
private def compiled : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core, .word⟩
private theorem compilation : RuntimeFunctionCompiles types owner declaration compiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil),
    .terminal <| .single <| .expression (.add (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))⟩
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (left right : Core.Word) :
    RuntimeFunctionPrepares types owner declaration (arguments left right) ⟨inputs left right, core, .word⟩ :=
  ⟨compilation.header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), compilation.body⟩

theorem independent_value_free_function_compilation_reaches_exact_runtime_cost
    (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner declaration compiled ∧
    compileRuntimeFunction? types owner declaration = some compiled ∧
    RuntimeFunctionEvaluatesWithCost types owner declaration (arguments left right)
      store .word (.word (left.add right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner declaration (arguments left right) fuel store =
      some (.word, .done (.word (left.add right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner declaration (arguments left right)
      store .word (.word (left.add right)) store 5 :=
    .intro (preparation left right) (.terminal <| .single <| .expression (costed left right store))
  exact ⟨compilation, compilation.complete, evaluation, fun _ => evaluation.run_done_iff⟩

end Tests.FrontendWordAddition
