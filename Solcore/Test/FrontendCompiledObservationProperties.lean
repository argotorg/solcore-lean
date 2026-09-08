import Solcore.Frontend.RuntimeFunctionObservationProperties
import Solcore.Core.ModularArithmetic

/-! Independent compilation removes names, aliases, owners, ranges, and groups
from observations, but not ordered parameter types, actual values, or Core cost. -/

set_option autoImplicit false

namespace Tests.FrontendCompiledObservation

open Solcore Solcore.Frontend

private def owner (variant : Bool) : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"Observation", by decide⟩], by decide⟩⟩, if variant then 19 else 0⟩
private def span (variant : Bool) : Syntax.SourceSpan :=
  ⟨⟨.main, if variant then "renamed.sol" else "original.sol"⟩, if variant then 30 else 0, 2⟩
private def name (variant : Bool) := if variant then "renamed" else "x"
private def typeName (variant : Bool) := if variant then "AmountAlias" else "Word"
private def table (variant : Bool) : TypeNameTable := [([typeName variant], .word)]
private def annotation (variant : Bool) (spelling : String) : Syntax.TypeExpr :=
  ⟨span variant, .named ⟨span variant, ⟨⟨⟨span variant, spelling⟩, []⟩⟩⟩ none⟩
private def parameter (variant : Bool) (spelling type : String) : Syntax.FunctionParameter :=
  ⟨span variant, .typed none ⟨span variant, spelling⟩ (annotation variant type)⟩
private def reference (variant : Bool) : Syntax.Expr := ⟨span variant, .identifier ⟨span variant, name variant⟩⟩
private def zero (variant : Bool) : Syntax.Expr := ⟨span variant, .literal ⟨span variant, .decimal "0"⟩⟩
private theorem zeroMeaning (variant : Bool) : WordLiteralDenotes ⟨span variant, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (digit := 0) (.decimal (by decide) rfl) .nil)
private def added (variant : Bool) : Syntax.Expr :=
  ⟨span variant, .binary (reference variant) ⟨span variant, .add⟩ (zero variant)⟩
private def composite (variant : Bool) : Syntax.Expr :=
  ⟨span variant, .conditional ⟨span variant, .binary (added variant) ⟨span variant, .greater⟩ (zero variant)⟩
    (span variant) (reference variant) (span variant) (reference variant)⟩
private def source (variant : Bool) : Syntax.Expr :=
  if variant then ⟨span variant, .group ⟨span variant, .group (composite variant)⟩⟩ else composite variant
private def declaration (variant : Bool) (parameters : List Syntax.FunctionParameter) (body : Syntax.Expr) : Syntax.FunctionDecl :=
  ⟨span variant, ⟨⟨span variant, ⟨span variant, if variant then "otherFunction" else "function"⟩,
    none, ⟨span variant, parameters⟩, ⟨none, none⟩,
    some ⟨span variant, ⟨span variant, [annotation variant (typeName variant)]⟩⟩, none⟩,
    ⟨span variant, [⟨span variant, .returnStmt (some body)⟩]⟩⟩⟩
private def parameters (variant : Bool) := [parameter variant (name variant) (typeName variant)]
private def entry (variant : Bool) := declaration variant (parameters variant) (source variant)
private def staticInputs (variant : Bool) := LocalTypeInputs.empty.bindFresh (owner variant) (name variant) .word
private def core : Core.Expr := .ifE (.binary .wordGt (.binary .wordAdd (.var 0) (.word .zero)) (.word .zero)) (.var 0) (.var 0)
private def compiled (variant : Bool) : CompiledRuntimeFunction := ⟨staticInputs variant, core, .word⟩
private theorem header (variant : Bool) (parameters : List Syntax.FunctionParameter) (body : Syntax.Expr) :
    RuntimeFunctionHeader (table variant) (declaration variant parameters body).value.signature .word :=
  ⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩
private theorem declared (variant : Bool) : RuntimeParametersDeclare (table variant) (owner variant)
    (parameters variant) (staticInputs variant) :=
  .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil
private theorem compilation (variant : Bool) : RuntimeFunctionCompiles (table variant) (owner variant) (entry variant) (compiled variant) := by
  have base : ResolvesLocalExpression (staticInputs variant).names (composite variant)
      (.ifE (.binary .wordGt (.binary .wordAdd (.var ⟨owner variant, 0⟩) (.word .zero)) (.word .zero))
        (.var ⟨owner variant, 0⟩) (.var ⟨owner variant, 0⟩)) :=
    .conditional (.greater (.add (.identifier .head) (.wordLiteral (zeroMeaning variant)))
      (.wordLiteral (zeroMeaning variant))) (.identifier .head) (.identifier .head)
  refine ⟨header variant _ _, declared variant, .single <| .expression ?_
    (.ifE (.binary (.binary (.var .head) .word) .word) (.var .head) (.var .head))
    (.ifE (.binary (.binary (.var .head) .word) .word) (.var .head) (.var .head))⟩
  cases variant
  · exact base
  · exact .group (.group base)
private def argument (value : Core.Word) : TypedRuntimeArgument := ⟨.word, .word value, .word⟩

theorem renamed_aliased_grouped_owners_compile_independently :
    RuntimeFunctionCompiles (table false) (owner false) (entry false) (compiled false) ∧
    RuntimeFunctionCompiles (table true) (owner true) (entry true) (compiled true) ∧
    (compiled false).inputs.context.values = (compiled true).inputs.context.values ∧
    (compiled false).core = (compiled true).core ∧
    (compiled false).returnType = (compiled true).returnType ∧
    (compiled false).inputs.names ≠ (compiled true).inputs.names := by
  refine ⟨compilation false, compilation true, rfl, rfl,
    (compilation false).returnType_eq_of_same_core (compilation true) rfl rfl, ?_⟩
  intro same
  have spellings := congrArg (List.map Prod.fst) same
  change ["x"] = ["renamed"] at spellings
  exact (by decide : ["x"] ≠ ["renamed"]) spellings

theorem arbitrary_arguments_share_all_fuel_results_and_exact_costs
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (initialStore finalStore : Core.Store)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) :
    runRuntimeFunction? (table false) (owner false) (entry false) arguments fuel initialStore =
      runRuntimeFunction? (table true) (owner true) (entry true) arguments fuel initialStore ∧
    (RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) arguments
        initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost (table true) (owner true) (entry true) arguments
        initialStore type value finalStore cost) :=
  ⟨(compilation false).run_eq_of_same_core (compilation true) rfl rfl arguments fuel initialStore,
    (compilation false).cost_iff_of_same_core (compilation true) rfl rfl⟩

private def prepared (value : Core.Word) : PreparedRuntimeFunction :=
  ⟨LocalInputs.empty.bindFresh (owner false) (name false) .word (.word value) .word, core, .word⟩
private theorem prepares (value : Core.Word) : RuntimeFunctionPrepares (table false) (owner false)
    (entry false) [argument value] (prepared value) :=
  ⟨(compilation false).header, .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    (compilation false).body⟩
private theorem originalCost (value : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) [argument value]
      store .word (.word value) store 12 := by
  have leaf : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (reference false) (.word value) store 1 := .identifier .head .head
  have literal : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (zero false) (.word .zero) store 1 := .wordLiteral (zeroMeaning false)
  have sum : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store (added false) (.word value) store 5 := by
    simpa [added] using
      (LocalExpressionEvaluatesWithCost.add (span := span false) (operatorSpan := span false)
        (leftValue := value) (rightValue := Core.Word.zero) (leftCost := 1) (rightCost := 1) leaf literal)
  have comparison : LocalExpressionEvaluatesWithCost (prepared value).inputs.names (prepared value).inputs.environment
      store ⟨span false, .binary (added false) ⟨span false, .greater⟩ (zero false)⟩
      (.bool (decide (value > Core.Word.zero))) store 9 :=
    .greater (leftValue := value) (rightValue := Core.Word.zero) (leftCost := 5) (rightCost := 1) sum literal
  apply RuntimeFunctionEvaluatesWithCost.intro (prepares value)
  apply TerminalReturnTreeEvaluatesWithCost.single
  apply ReturnBodyEvaluatesWithCost.expression
  by_cases positive : value > Core.Word.zero
  · exact .ifTrue (by simpa only [positive, decide_true] using comparison) leaf
  · exact .ifFalse (by simpa only [positive, decide_false] using comparison) leaf

theorem composite_cost_transports_across_spelling_and_groups (value : Core.Word) (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost (table false) (owner false) (entry false) [argument value]
      store .word (.word value) store 12 ∧
    RuntimeFunctionEvaluatesWithCost (table true) (owner true) (entry true) [argument value]
      store .word (.word value) store 12 ∧ ∀ fuel,
    (runRuntimeFunction? (table true) (owner true) (entry true) [argument value] fuel store =
      some (.word, .done (.word value) store) ↔ 12 ≤ fuel) ∧
    ((∃ suspended, runRuntimeFunction? (table true) (owner true) (entry true) [argument value] fuel store =
      some (.word, .outOfFuel suspended)) ↔ fuel < 12) := by
  have transported := ((compilation false).cost_iff_of_same_core (compilation true) rfl rfl).mp (originalCost value store)
  exact ⟨originalCost value store, transported, fun _ => ⟨transported.run_done_iff, transported.run_outOfFuel_iff⟩⟩

private theorem mismatch_rejects {types : TypeNameTable} {id : Resolved.DeclarationId}
    {decl : Syntax.FunctionDecl} {output : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types id decl output) (args : List TypedRuntimeArgument)
    (mismatch : args.map (·.type) ≠ output.inputs.context.values.reverse) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types id decl args fuel store = none := by
  rw [runRuntimeFunction?_factorization, compilation.complete]
  simp only [bind, Option.bind_some, if_neg mismatch]

private def guardTable : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def guardEntry (swapped : Bool) := declaration false
  [parameter false "a" (if swapped then "Bool" else "Word"),
   parameter false "b" (if swapped then "Word" else "Bool")] (zero false)
private def guardCompiled (swapped : Bool) : CompiledRuntimeFunction :=
  ⟨(LocalTypeInputs.empty.bindFresh (owner false) "a" (if swapped then .bool else .word)).bindFresh
    (owner false) "b" (if swapped then .word else .bool), .word .zero, .word⟩
private theorem guardCompilation (swapped : Bool) :
    RuntimeFunctionCompiles guardTable (owner false) (guardEntry swapped) (guardCompiled swapped) := by
  refine ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, ?_,
    .single <| .expression (.wordLiteral (zeroMeaning false)) .word .word⟩
  cases swapped
  · exact .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named (.tail (by decide) .head)) (by change "b" ∉ ["a"]; decide) .nil)
  · exact .cons (.named (.tail (by decide) .head)) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names])
      (.cons (.named .head) (by change "b" ∉ ["a"]; decide) .nil)
private def emptyEntry := declaration false [] (zero false)
private def emptyCompiled : CompiledRuntimeFunction := ⟨LocalTypeInputs.empty, .word .zero, .word⟩
private theorem emptyCompilation : RuntimeFunctionCompiles guardTable (owner false) emptyEntry emptyCompiled :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩, .nil,
    .single <| .expression (.wordLiteral (zeroMeaning false)) .word .word⟩
private def guardedArguments (value : Core.Word) : List TypedRuntimeArgument :=
  [argument value, ⟨.bool, .bool false, .bool⟩]

theorem identical_core_does_not_remove_ordered_context_and_arity_guards
    (value : Core.Word) (store : Core.Store) :
    (guardCompiled false).core = (guardCompiled true).core ∧
    (guardCompiled false).core = emptyCompiled.core ∧
    (guardCompiled false).inputs.context.values ≠ (guardCompiled true).inputs.context.values ∧
    (guardCompiled false).inputs.context.values ≠ emptyCompiled.inputs.context.values ∧
    runRuntimeFunction? guardTable (owner false) (guardEntry false) (guardedArguments value) 1 store =
      some (.word, .done (.word .zero) store) ∧
    runRuntimeFunction? guardTable (owner false) emptyEntry [] 1 store = some (.word, .done (.word .zero) store) ∧
    ∀ fuel, runRuntimeFunction? guardTable (owner false) (guardEntry true) (guardedArguments value) fuel store = none ∧
      runRuntimeFunction? guardTable (owner false) emptyEntry (guardedArguments value) fuel store = none := by
  refine ⟨rfl, rfl, by decide, by decide,
    (guardCompilation false).run_eq (guardedArguments value) rfl 1 store,
    emptyCompilation.run_eq [] rfl 1 store, ?_⟩
  intro fuel
  exact ⟨mismatch_rejects (guardCompilation true) (guardedArguments value)
      (by change [Core.Ty.word, .bool] ≠ [.bool, .word]; decide) fuel store,
    mismatch_rejects emptyCompilation (guardedArguments value)
      (by change [Core.Ty.word, .bool] ≠ []; decide) fuel store⟩

private def simpleEntry (addition : Bool) :=
  declaration false (parameters false) (if addition then added false else reference false)
private def simpleCompiled (addition : Bool) : CompiledRuntimeFunction :=
  ⟨staticInputs false, if addition then .binary .wordAdd (.var 0) (.word .zero) else .var 0, .word⟩
private theorem simpleCompilation (addition : Bool) : RuntimeFunctionCompiles (table false) (owner false)
    (simpleEntry addition) (simpleCompiled addition) := by
  refine ⟨header false _ _, declared false, ?_⟩
  cases addition
  · exact .single <| .expression (.identifier .head) (.var .head) (.var .head)
  · exact .single <| .expression (.add (.identifier .head) (.wordLiteral (zeroMeaning false)))
      (.binary (.var .head) .word) (.binary (.var .head) .word)

theorem equal_eventual_values_do_not_preserve_exact_core_or_fuel
    (value : Core.Word) (store : Core.Store) :
    (simpleCompiled false).inputs.context.values = (simpleCompiled true).inputs.context.values ∧
    (simpleCompiled false).core ≠ (simpleCompiled true).core ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument value] 1 store =
      some (.word, .done (.word value) store) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry true) [argument value] 4 store =
      some (.word, .outOfFuel ⟨.ret (.word .zero), [.binaryApply .wordAdd (.word value)], store⟩) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry true) [argument value] 5 store =
      some (.word, .done (.word value) store) := by
  refine ⟨rfl, (by intro same; cases same), (simpleCompilation false).run_eq _ rfl 1 store,
    (simpleCompilation true).run_eq _ rfl 4 store, ?_⟩
  have result := (simpleCompilation true).run_eq [argument value] rfl 5 store
  change runRuntimeFunction? _ _ _ _ _ _ = some (.word, .done (.word (value.add Core.Word.zero)) store) at result
  simpa only [Core.Word.add_zero] using result

theorem equal_argument_types_do_not_replace_shared_values
    (left right : Core.Word) (different : left ≠ right) (store : Core.Store) :
    [argument left].map (·.type) = [argument right].map (·.type) ∧
    runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument left] 1 store ≠
      runRuntimeFunction? (table false) (owner false) (simpleEntry false) [argument right] 1 store := by
  refine ⟨rfl, ?_⟩
  rw [(simpleCompilation false).run_eq [argument left] rfl 1 store,
    (simpleCompilation false).run_eq [argument right] rfl 1 store]
  change some (Core.Ty.word, Core.StatefulRunResult.done (.word left) store) ≠
    some (.word, .done (.word right) store)
  intro same
  exact different (Core.Value.word.inj (Core.StatefulRunResult.done.inj (Prod.mk.inj (Option.some.inj same)).2).1)

end Tests.FrontendCompiledObservation
