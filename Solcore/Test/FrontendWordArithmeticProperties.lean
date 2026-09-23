import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.RuntimeFunction
import Solcore.Core.ModularArithmetic

/-! Independent subtraction and multiplication preserve ordered Word operands,
modular results, exact Core frames, and the whole compiled entry contract. -/

set_option autoImplicit false

namespace Tests.FrontendWordArithmetic

open Solcore Solcore.Frontend

private inductive Kind where | subtractE | multiplyE
private def sourceOp : Kind → Syntax.BinaryOp | .subtractE => .subtract | .multiplyE => .multiply
private def coreOp : Kind → Core.BinaryOp | .subtractE => .wordSub | .multiplyE => .wordMul
private def result (kind : Kind) (left right : Core.Word) : Core.Word :=
  match kind with | .subtractE => left.sub right | .multiplyE => left.mul right
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Arithmetic", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "arithmetic.sol"⟩, 17, 3⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def binary (kind : Kind) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, sourceOp kind⟩ right⟩
private def source (kind : Kind) := binary kind (ref "l") (ref "r")
private def inputs (left right : Core.Word) : LocalInputs :=
  (LocalInputs.empty.bindFresh owner "l" .word (.word left) .word).bindFresh owner "r" .word (.word right) .word
private def core (kind : Kind) : Core.Expr := .binary (coreOp kind) (.var 1) (.var 0)
private theorem names_ne : "r" ≠ "l" := by decide
private theorem ids_ne : (⟨owner, 1⟩ : Resolved.LocalId) ≠ ⟨owner, 0⟩ := by decide
private theorem resolved (kind : Kind) (left right : Core.Word) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) := by
  cases kind
  · exact .subtract (.identifier (.tail names_ne .head)) (.identifier .head)
  · exact .multiply (.identifier (.tail names_ne .head)) (.identifier .head)
private theorem typed (kind : Kind) (left right : Core.Word) :
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word := by
  cases kind
  · exact .subtract (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .multiply (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
private theorem checked (kind : Kind) (left right : Core.Word) :
    (inputs left right).check? (source kind) = some (core kind, .word) :=
  elaborateLocalExpression?_complete (resolved kind left right)
    (.binary (.var (.tail ids_ne .head)) (.var .head))
    ((resolved kind left right).preserves_type (typed kind left right))
private theorem costed (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 := by
  cases kind
  · exact .subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)
  · exact .multiply (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier (.tail names_ne .head) (.tail ids_ne .head)) (.identifier .head .head)

theorem arbitrary_words_have_independent_typing_evaluation_and_exact_core_steps
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    ResolvesLocalExpression (inputs left right).names (source kind)
      (.binary (coreOp kind) (.var ⟨owner, 0⟩) (.var ⟨owner, 1⟩)) ∧
    LocalExpressionHasType (inputs left right).names (inputs left right).context (source kind) .word ∧
    (inputs left right).check? (source kind) = some (core kind, .word) ∧
    LocalExpressionEvaluates (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store ∧
    LocalExpressionEvaluatesWithCost (inputs left right).names (inputs left right).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    Core.Steps 5 (Core.State.initial (core kind) [.word right, .word left] store)
      (Core.State.final (.word (result kind left right)) store) :=
  ⟨resolved kind left right, typed kind left right, checked kind left right,
    (costed kind left right store).erase, costed kind left right store,
    (costed kind left right store).checked_toSteps (checked kind left right) (inputs left right).sameIds⟩

theorem exact_completion_and_ordered_four_step_state
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    (inputs left right).run? 4 (source kind) store = some (.word, .outOfFuel
      ⟨.ret (.word right), [.binaryApply (coreOp kind) (.word left)], store⟩) ∧
    ∀ fuel, ((inputs left right).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) := by
  constructor
  · rw [LocalInputs.run?, checked]; cases kind <;> rfl
  · intro fuel
    simpa only [LocalInputs.run?, checked, bind, Option.bind_some, pure,
      Option.some.injEq, Prod.mk.injEq, true_and] using
      (costed kind left right store).checked_runStateful_done_iff (fuel := fuel)
        (checked kind left right) (inputs left right).sameIds

theorem subtraction_underflow_is_not_commutative (store : Core.Store) :
    (inputs .zero (Core.Word.ofNatModulo 1)).check? (source .subtractE) =
      some (core .subtractE, .word) ∧
    (inputs .zero (Core.Word.ofNatModulo 1)).run? 5 (source .subtractE) store =
      some (.word, .done (.word .maximum) store) ∧
    (inputs (Core.Word.ofNatModulo 1) .zero).run? 5 (source .subtractE) store =
      some (.word, .done (.word (Core.Word.ofNatModulo 1)) store) ∧
    (Core.Word.maximum : Core.Word) ≠ Core.Word.ofNatModulo 1 := by
  refine ⟨checked .subtractE _ _, ?_, ?_, by decide⟩
  · simpa only [result, Core.Word.zero_sub_one] using
      (exact_completion_and_ordered_four_step_state .subtractE .zero
        (Core.Word.ofNatModulo 1) store).2 5 |>.mpr (by decide)
  · simpa only [result, Core.Word.sub_zero] using
      (exact_completion_and_ordered_four_step_state .subtractE
        (Core.Word.ofNatModulo 1) .zero store).2 5 |>.mpr (by decide)

theorem maximum_times_two_wraps_without_folding (store : Core.Store) :
    (inputs .maximum (Core.Word.ofNatModulo 2)).check? (source .multiplyE) =
      some (core .multiplyE, .word) ∧
    (inputs .maximum (Core.Word.ofNatModulo 2)).run? 5 (source .multiplyE) store =
      some (.word, .done (.word (Core.Word.ofNatModulo (Core.wordModulus - 2))) store) := by
  refine ⟨checked .multiplyE _ _, ?_⟩
  simpa only [result, Core.Word.maximum_mul_two] using
    (exact_completion_and_ordered_four_step_state .multiplyE .maximum
      (Core.Word.ofNatModulo 2) store).2 5 |>.mpr (by decide)

theorem successful_arithmetic_requires_ordered_word_costs (kind : Kind)
    {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {left right : Syntax.Expr} {value : Core.Value}
    {cost : Nat} (evaluation : LocalExpressionEvaluatesWithCost table environment
      initialStore (binary kind left right) value finalStore cost) :
    ∃ leftWord rightWord middleStore leftCost rightCost,
      LocalExpressionEvaluatesWithCost table environment initialStore left (.word leftWord) middleStore leftCost ∧
      LocalExpressionEvaluatesWithCost table environment middleStore right (.word rightWord) finalStore rightCost ∧
      value = .word (result kind leftWord rightWord) ∧ cost = leftCost + rightCost + 3 := by
  cases kind <;> cases evaluation <;> exact ⟨_, _, _, _, _, by assumption, by assumption, rfl, rfl⟩

private theorem missing_not_evaluates {initialStore finalStore : Core.Store} {value : Core.Value} :
    ¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
      initialStore (ref "missing") value finalStore := by
  intro evaluation
  cases evaluation with
  | identifier named _ =>
      have found := LocalNameTable.lookup?_iff.mpr named
      have absent : (inputs .zero .zero).names.lookup? "missing" = none := rfl
      rw [absent] at found
      cases found

theorem zero_multiplication_does_not_bypass_missing_operands (store : Core.Store) :
    (inputs .zero .zero).check? (binary .multiplyE (ref "l") (ref "missing")) = none ∧
    (inputs .zero .zero).check? (binary .multiplyE (ref "missing") (ref "r")) = none ∧
    ∀ value finalStore,
      (¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
        store (binary .multiplyE (ref "l") (ref "missing")) value finalStore) ∧
      (¬ LocalExpressionEvaluates (inputs .zero .zero).names (inputs .zero .zero).environment
        store (binary .multiplyE (ref "missing") (ref "r")) value finalStore) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, binary, sourceOp, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  · simp [LocalInputs.check?, elaborateLocalExpression?, resolveLocalExpression?, binary, sourceOp, ref,
      inputs, LocalInputs.names, LocalInputs.bindFresh, LocalInputs.empty, LocalNameTable.lookup?]
  · intro value finalStore
    constructor
    · intro evaluation
      cases evaluation with | multiply _ right => exact missing_not_evaluates right
    · intro evaluation
      cases evaluation with | multiply left _ => exact missing_not_evaluates left

theorem unused_inputs_and_injective_ids_preserve_arithmetic
    (kind : Kind) (left right : Core.Word) (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping) (fuel : Nat) (store : Core.Store) :
    ((inputs left right).mapIds mapping injective).run? fuel (source kind) store =
      (inputs left right).run? fuel (source kind) store ∧
    LocalExpressionEvaluatesWithCost ((inputs left right).bindFresh owner "unused" .unit .unit .unit).names
      ((inputs left right).bindFresh owner "unused" .unit .unit .unit).environment
      store (source kind) (.word (result kind left right)) store 5 ∧
    (((inputs left right).bindFresh owner "unused" .unit .unit .unit).run? fuel (source kind) store =
      some (.word, .done (.word (result kind left right)) store) ↔
      (inputs left right).run? fuel (source kind) store =
        some (.word, .done (.word (result kind left right)) store)) := by
  have avoids : AvoidsLocalName "unused" (source kind) := by
    cases kind
    · exact .subtract (.identifier (by decide)) (.identifier (by decide))
    · exact .multiply (.identifier (by decide)) (.identifier (by decide))
  exact ⟨(inputs left right).run?_mapIds mapping injective fuel (source kind) store,
    (avoids.bindFresh_cost_iff (inputs left right) owner .unit .unit .unit).mpr (costed kind left right store),
    avoids.bindFresh_run_done_at_fuel_iff (inputs left right) owner .unit .unit .unit⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def parameter (name : String) : Syntax.FunctionParameter := ⟨span, .typed none ⟨span, name⟩ annotation⟩
private def types : TypeNameTable := [(["Word"], .word)]
private def declaration (kind : Kind) : Syntax.FunctionDecl :=
  ⟨span, ⟨⟨span, ⟨span, "arithmetic"⟩, none, ⟨span, [parameter "l", parameter "r"]⟩,
    ⟨none, none⟩, some ⟨span, ⟨span, [annotation]⟩⟩, none⟩,
    ⟨span, [⟨span, .returnStmt (some (source kind))⟩]⟩⟩⟩
private def compiled (kind : Kind) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh owner "l" .word).bindFresh owner "r" .word, core kind, .word⟩
private theorem compilation (kind : Kind) : RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), ?_⟩
  cases kind
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.subtract (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
  · exact TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.multiply (.identifier (.tail names_ne .head)) (.identifier .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
      (.binary (.var (.tail ids_ne .head)) (.var .head))
private def arguments (left right : Core.Word) : List TypedRuntimeArgument :=
  [⟨.word, .word left, .word⟩, ⟨.word, .word right, .word⟩]
private theorem preparation (kind : Kind) (left right : Core.Word) :
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right)
      ⟨inputs left right, core kind, .word⟩ :=
  ⟨(compilation kind).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names])
      (.cons (.named .head) (by change "r" ∉ ["l"]; simp) .nil), (compilation kind).body⟩

theorem independent_compilation_preparation_and_exact_entry_cost
    (kind : Kind) (left right : Core.Word) (store : Core.Store) :
    RuntimeFunctionCompiles types owner (declaration kind) (compiled kind) ∧
    compileRuntimeFunction? types owner (declaration kind) = some (compiled kind) ∧
    RuntimeFunctionPrepares types owner (declaration kind) (arguments left right)
      ⟨inputs left right, core kind, .word⟩ ∧
    RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right)
      store .word (.word (result kind left right)) store 5 ∧
    ∀ fuel, (runRuntimeFunction? types owner (declaration kind) (arguments left right) fuel store =
      some (.word, .done (.word (result kind left right)) store) ↔ 5 ≤ fuel) := by
  have evaluation : RuntimeFunctionEvaluatesWithCost types owner (declaration kind) (arguments left right)
      store .word (.word (result kind left right)) store 5 :=
    .intro (preparation kind left right) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (costed kind left right store))
  exact ⟨compilation kind, (compilation kind).complete, preparation kind left right,
    evaluation, fun _ => evaluation.run_done_iff⟩

end Tests.FrontendWordArithmetic
