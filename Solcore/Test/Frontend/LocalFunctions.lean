import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.LocalComputation
import Solcore.Frontend.ReturnBody
import Solcore.Core.LocalFragment
import Solcore.Core.Safety
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Frontend.RuntimeParameters

/-!
# Local function tests

Parsed local functions and applications: evaluation, the runner, runtime safety, return trees and fuel
bounds.
-/

section
-- leanmerge: from Solcore.Test.FrontendFuelBoundProperties
/-! Independent cost derivations distinguish sufficient structural budgets from
exact path costs, and never treat an unsupported zero-bound expression as checked. -/

set_option autoImplicit false

namespace Tests.FrontendFuelBound

open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"FuelBound", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "fuel-bound.sol"⟩, 13, 2⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def unary (operator : Syntax.UnaryOp) (child : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .unary ⟨span, operator⟩ child⟩
private def binary (operator : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .binary left ⟨span, operator⟩ right⟩
private def names : LocalNameTable := [("c", ⟨owner, 0⟩), ("x", ⟨owner, 1⟩), ("y", ⟨owner, 2⟩)]
private def environment (choice : Bool) (left right : Core.Word) : Resolved.Environment :=
  [(⟨owner, 0⟩, .bool choice), (⟨owner, 1⟩, .word left), (⟨owner, 2⟩, .word right)]
private theorem choiceCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "c") (.bool choice) store 1 := .identifier .head .head
private theorem leftCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "x") (.word left) store 1 :=
  .identifier (.tail (by decide) .head) (.tail (by decide) .head)
private theorem rightCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (ref "y") (.word right) store 1 :=
  .identifier (.tail (by decide) (.tail (by decide) .head))
    (.tail (by decide) (.tail (by decide) .head))

theorem leaf_spelling_spans_and_grouping_add_no_core_budget
    (literal : Syntax.CoreLiteral) (outer inner : Syntax.SourceSpan) (source : Syntax.Expr) :
    localExpressionFuelBound ⟨outer, .literal literal⟩ = 1 ∧
    localExpressionFuelBound ⟨outer, .group ⟨inner, .group source⟩⟩ = localExpressionFuelBound source ∧
    localExpressionFuelBound (ref "missing") = 1 := by
  simp [localExpressionFuelBound, ref]

theorem independently_denoted_literals_and_both_unaries_fit
    (literal : Syntax.CoreLiteral) (word : Core.Word) (meaning : WordLiteralDenotes literal word)
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      ⟨span, .group ⟨span, .literal literal⟩⟩ (.word word) store 1 ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .logicalNot (ref "c")) (.bool (!choice)) store 3 ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .bitNot (ref "x")) (.word left.bitNot) store 3 ∧
    1 ≤ localExpressionFuelBound ⟨span, .group ⟨span, .literal literal⟩⟩ ∧
    3 ≤ localExpressionFuelBound (unary .logicalNot (ref "c")) ∧
    3 ≤ localExpressionFuelBound (unary .bitNot (ref "x")) := by
  have literalCost : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      ⟨span, .group ⟨span, .literal literal⟩⟩ (.word word) store 1 := .group (.wordLiteral meaning)
  have negated : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .logicalNot (ref "c")) (.bool (!choice)) store 3 := .logicalNot (choiceCost choice left right store)
  have complemented : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (unary .bitNot (ref "x")) (.word left.bitNot) store 3 := .bitNot (leftCost choice left right store)
  exact ⟨literalCost, negated, complemented, literalCost.cost_le_fuelBound,
    negated.cost_le_fuelBound, complemented.cost_le_fuelBound⟩

private inductive StrictOp where
  | add | subtract | multiply | bitAnd | bitOr | bitXor | greater
private def operator : StrictOp → Syntax.BinaryOp
  | .add => .add | .subtract => .subtract | .multiply => .multiply
  | .bitAnd => .bitAnd | .bitOr => .bitOr | .bitXor => .bitXor | .greater => .greater
private def result (kind : StrictOp) (left right : Core.Word) : Core.Value :=
  match kind with
  | .add => .word (left.add right) | .subtract => .word (left.sub right)
  | .multiply => .word (left.mul right) | .bitAnd => .word (left.bitAnd right)
  | .bitOr => .word (left.bitOr right) | .bitXor => .word (left.bitXor right)
  | .greater => .bool (decide (left > right))

theorem every_strict_word_operator_has_independent_cost_and_bound_five
    (kind : StrictOp) (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (binary (operator kind) (ref "x") (ref "y")) (result kind left right) store 5 ∧
    5 ≤ localExpressionFuelBound (binary (operator kind) (ref "x") (ref "y")) ∧
    localExpressionFuelBound (binary (operator kind) (ref "x") (ref "y")) = 5 := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (binary (operator kind) (ref "x") (ref "y")) (result kind left right) store 5 := by
    cases kind
    · exact .add (leftCost choice left right store) (rightCost choice left right store)
    · exact .subtract (leftCost choice left right store) (rightCost choice left right store)
    · exact .multiply (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitAnd (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitOr (leftCost choice left right store) (rightCost choice left right store)
    · exact .bitXor (leftCost choice left right store) (rightCost choice left right store)
    · exact .greater (leftCost choice left right store) (rightCost choice left right store)
  refine ⟨evaluated, evaluated.cost_le_fuelBound, ?_⟩
  cases kind <;> simp [binary, operator, ref, localExpressionFuelBound]

private def shortCircuit (operator : Syntax.BinaryOp) := binary operator (ref "c") (unary .logicalNot (ref "c"))
private theorem andCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalAnd) (.bool false) store (if choice then 6 else 4) := by
  cases choice
  · exact .andFalse (choiceCost false left right store)
  · exact .andTrue (choiceCost true left right store) (.logicalNot (choiceCost true left right store))
private theorem orCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalOr) (.bool true) store (if choice then 4 else 6) := by
  cases choice
  · exact .orFalse (choiceCost false left right store) (.logicalNot (choiceCost false left right store))
  · exact .orTrue (choiceCost true left right store)

theorem boolean_paths_have_value_dependent_costs_but_shared_sufficient_bounds
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalAnd) (.bool false) store (if choice then 6 else 4) ∧
    LocalExpressionEvaluatesWithCost names (environment choice left right) store
      (shortCircuit .logicalOr) (.bool true) store (if choice then 4 else 6) ∧
    (if choice then 6 else 4) ≤ localExpressionFuelBound (shortCircuit .logicalAnd) ∧
    (if choice then 4 else 6) ≤ localExpressionFuelBound (shortCircuit .logicalOr) ∧
    localExpressionFuelBound (shortCircuit .logicalAnd) = 6 ∧
    localExpressionFuelBound (shortCircuit .logicalOr) = 6 := by
  refine ⟨andCost choice left right store, orCost choice left right store,
    (andCost choice left right store).cost_le_fuelBound,
    (orCost choice left right store).cost_le_fuelBound, ?_, ?_⟩ <;>
    simp [shortCircuit, binary, unary, ref, localExpressionFuelBound]

private def conditional : Syntax.Expr :=
  ⟨span, .conditional (ref "c") span (binary .multiply (ref "x") (ref "y")) span (ref "x")⟩
private theorem conditionalCost (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store conditional
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) := by
  cases choice
  · exact .ifFalse (choiceCost false left right store) (leftCost false left right store)
  · exact .ifTrue (choiceCost true left right store)
      (every_strict_word_operator_has_independent_cost_and_bound_five .multiply true left right store).1

theorem conditional_bound_is_conservative_not_the_selected_path_minimum
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment choice left right) store conditional
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) ∧
    (if choice then 8 else 4) ≤ localExpressionFuelBound conditional ∧
    localExpressionFuelBound conditional = 8 ∧ 4 < localExpressionFuelBound conditional := by
  refine ⟨conditionalCost choice left right store,
    (conditionalCost choice left right store).cost_le_fuelBound, ?_, ?_⟩ <;>
    simp [conditional, binary, ref, localExpressionFuelBound]

private def unsupported : Syntax.Expr := ⟨span, .call (ref "missing") ⟨span, []⟩⟩

theorem inserted_boolean_constant_requires_positive_budget_when_skipping_unsupported_source
    (left right : Core.Word) (store : Core.Store) :
    LocalExpressionEvaluatesWithCost names (environment false left right) store
      (binary .logicalAnd (ref "c") unsupported) (.bool false) store 4 ∧
    localExpressionFuelBound unsupported = 0 ∧
    localExpressionFuelBound (binary .logicalAnd (ref "c") unsupported) = 4 ∧
    4 ≤ localExpressionFuelBound (binary .logicalAnd (ref "c") unsupported) ∧
    resolveLocalExpression? names (binary .logicalAnd (ref "c") unsupported) = none := by
  have evaluated : LocalExpressionEvaluatesWithCost names (environment false left right) store
      (binary .logicalAnd (ref "c") unsupported) (.bool false) store 4 :=
    .andFalse (choiceCost false left right store)
  refine ⟨evaluated, ?_, ?_, evaluated.cost_le_fuelBound, ?_⟩
  · simp [unsupported, localExpressionFuelBound]
  · simp [binary, ref, unsupported, localExpressionFuelBound]
  · simp [binary, ref, unsupported, resolveLocalExpression?, names, LocalNameTable.lookup?]

private def body (source : Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some source)⟩]⟩

theorem singleton_return_inherits_the_bound_without_a_wrapper_cost
    (choice : Bool) (left right : Core.Word) (store : Core.Store) :
    ReturnBodyEvaluatesWithCost names (environment choice left right) store (body conditional)
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) ∧
    (if choice then 8 else 4) ≤ returnBodyFuelBound (body conditional) ∧
    returnBodyFuelBound ⟨span, [⟨span, .returnStmt none⟩]⟩ = 1 ∧
    returnBodyFuelBound ⟨span, []⟩ = 0 := by
  have evaluated : ReturnBodyEvaluatesWithCost names (environment choice left right) store (body conditional)
      (.word (if choice then left.mul right else left)) store (if choice then 8 else 4) :=
    .expression (conditionalCost choice left right store)
  exact ⟨evaluated, evaluated.cost_le_fuelBound, rfl, rfl⟩

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
private def inputs (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "x" type value typed
private theorem compilation (type : Core.Ty) : RuntimeFunctionCompiles (types type) owner declaration (compiled type) :=
  ⟨⟨rfl, rfl, rfl, rfl, .single (.named .head)⟩,
    .cons (.named .head) (by simp [LocalTypeInputs.empty, LocalTypeInputs.names]) .nil,
    TypedLetReturnBodyElaborates.returnTree <| .terminal <| .single <| .expression (.identifier .head) (.var .head) (.var .head)⟩
private theorem preparation (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) :
    RuntimeFunctionPrepares (types type) owner declaration [argument type value typed]
      ⟨inputs type value typed, .var 0, type⟩ :=
  ⟨(compilation type).header,
    .cons (.named .head) (by simp [LocalInputs.empty, LocalInputs.names]) .nil,
    (compilation type).body⟩

theorem checked_local_and_return_endpoints_finish_with_the_same_structural_budget
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (enough : 1 ≤ fuel) :
    (∃ result, Core.ValueHasType result type ∧
      (inputs type value typed).run? fuel (ref "x") store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧
      (inputs type value typed).runReturnBody? fuel (body (ref "x")) store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧
      Core.runStateful fuel (Core.State.initial (.var 0) [value] store) = .done result store) := by
  have localTyped : LocalExpressionHasType (inputs type value typed).names
      (inputs type value typed).context (ref "x") type := .identifier .head .head
  have localChecked : elaborateLocalExpression? (inputs type value typed).names
      (inputs type value typed).context (ref "x") = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have localEnough : localExpressionFuelBound (ref "x") ≤ fuel := by
    simpa [ref, localExpressionFuelBound] using enough
  have bodyEnough : returnBodyFuelBound (body (ref "x")) ≤ fuel := localEnough
  have localRun := elaborateLocalExpression?_run_done_of_fuelBound localChecked
    (inputs type value typed).sameIds (inputs type value typed).environmentTyped store fuel localEnough
  have bodyElaboration : ReturnBodyElaborates (inputs type value typed).names
      (inputs type value typed).context (body (ref "x")) (.var 0) type :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have bodyRun := elaborateReturnBody?_run_done_of_fuelBound bodyElaboration.complete
    (inputs type value typed).sameIds (inputs type value typed).environmentTyped store fuel bodyEnough
  obtain ⟨localResult, _, localDone⟩ := localRun
  obtain ⟨bodyResult, bodyResultTyped, bodyDone⟩ := bodyRun
  have sameResult : localResult = bodyResult := by
    have same := localDone.symm.trans bodyDone
    exact (Core.StatefulRunResult.done.inj same).1
  refine ⟨LocalInputs.run?_done_of_fuelBound localTyped store fuel localEnough,
    LocalInputs.runReturnBody?_done_of_fuelBound (.expression localTyped) store fuel bodyEnough,
    localResult, ?_, localDone⟩
  exact sameResult ▸ bodyResultTyped

theorem independently_compiled_identity_uses_only_its_actual_typed_argument
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type)
    (store : Core.Store) (fuel : Nat) (enough : 1 ≤ fuel) :
    RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 ∧ 1 ≤ typedLetReturnTreeFuelBound declaration.value.body ∧
    (∃ result, Core.ValueHasType result type ∧ runRuntimeFunction? (types type) owner declaration
      [argument type value typed] fuel store = some (type, .done result store)) ∧
    (∃ result, Core.ValueHasType result type ∧ runRuntimeFunction? (types type) owner declaration
      [argument type value typed] fuel store = some (type, .done result store) ∧
      Core.runStateful fuel (Core.State.initial (.var 0) [value] store) = .done result store) := by
  have evaluated : RuntimeFunctionEvaluatesWithCost (types type) owner declaration [argument type value typed]
      store type value store 1 := .intro (preparation type value typed) (TypedLetReturnBodyEvaluatesWithCost.returnTree <| .terminal <| .single <| .expression (.identifier .head .head))
  have bounded : typedLetReturnTreeFuelBound declaration.value.body ≤ fuel := by
    simpa [declaration, body, typedLetReturnTreeFuelBound,
      returnBodyFuelBound, ref, localExpressionFuelBound] using enough
  exact ⟨evaluated, evaluated.cost_le_fuelBound,
    (preparation type value typed).hasType.run_done_of_fuelBound store fuel bounded,
    (compilation type).run_done_of_fuelBound [argument type value typed] rfl store fuel bounded⟩

end Tests.FrontendFuelBound
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationRunnerProperties
/-! One supplied record fixes all original projections. Independent source and
actual-body evidence precedes wrapper observations; a static tag is not a world. -/
set_option autoImplicit false
namespace Tests.FrontendLocalApplicationRunner
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CallRunner", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def gid : Resolved.LocalId := ⟨owner, 91⟩
private def cid : Resolved.LocalId := ⟨owner, 1234⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 4 }, 999⟩
private def bundle (a b : Core.Ty) (f x : Core.Value)
    (ft : Core.ValueHasType f (.function a b)) (xt : Core.ValueHasType x a) : LocalInputs :=
  ⟨[⟨"x", aid, a, x, xt⟩, ⟨"f", fid, .function a b, f, ft⟩, ⟨"f", gid, .function a b, f, ft⟩,
      ⟨"c", cid, .bool, .bool true, .bool⟩],
    by change ([aid, fid, gid, cid] : List Resolved.LocalId).Nodup; decide⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "call-runner.sol"⟩, 31, 4⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (s t : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .call (ref s "f") ⟨t, [ref t "x"]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private theorem elaborated (a b : Core.Ty) (f x : Core.Value)
    (ft : Core.ValueHasType f (.function a b)) (xt : Core.ValueHasType x a) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates (bundle a b f x ft xt).names (bundle a b f x ft xt).context (source s t) core b :=
  .call (parameterType := a) (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (.identifier .head) (.var .head) (.var .head)
private theorem callCost (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment) (x value : Core.Value)
    (ft : Core.ValueHasType (.closure a b body captured) (.function a b)) (xt : Core.ValueHasType x a)
    (store final : Core.Store) (cost : Nat) (s t : Syntax.SourceSpan)
    (path : Core.Steps cost (.initial body (x :: captured) store) (.final value final)) :
    LocalFunctionApplicationEvaluatesWithCost (bundle a b (.closure a b body captured) x ft xt).names
      (bundle a b (.closure a b body captured) x ft xt).environment store (source s t) value final (1 + 1 + cost + 3) :=
  .call (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (by change aid ≠ fid; decide) .head))
    (.identifier .head .head) path
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private theorem delayTyped (n index : Nat) (rest : Core.Context)
    (found : (Core.Ty.unit :: rest)[index]? = some .unit) : Core.HasType (.unit :: rest) (delay n index) .unit := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index + 1) (.unit :: rest) (by simpa using found))
private theorem delayPath (n index : Nat) (rest : Core.Environment) (store : Core.Store) (k : List Core.Frame)
    (found : (Core.Value.unit :: rest)[index]? = some .unit) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n index) (.unit :: rest), k, store⟩ ⟨.ret .unit, k, store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (.unit :: rest) k (by simpa using found))))
private def delayed (n : Nat) : Core.Value := .closure .unit .unit (delay n 1) [.unit]
private theorem delayedTyped (n : Nat) : Core.ValueHasType (delayed n) (.function .unit .unit) :=
  .closure (.cons .unit .nil) (delayTyped n 1 [.unit] rfl)
private def inputs (n : Nat) : LocalInputs := bundle .unit .unit (delayed n) .unit (delayedTyped n) .unit
private theorem exact (n : Nat) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates (inputs n).names (inputs n).context (source s t) core .unit :=
  elaborated .unit .unit (delayed n) .unit (delayedTyped n) .unit s t
private theorem counted (n : Nat) (store : Core.Store) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationEvaluatesWithCost (inputs n).names (inputs n).environment store (source s t) .unit store (3 * n + 6) := by
  have actual := callCost .unit .unit (delay n 1) [.unit] .unit .unit (delayedTyped n) .unit store store (3 * n + 1) s t
    (delayPath n 1 [.unit] store [] rfl)
  have costs : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact costs ▸ actual
private theorem runtimeInputs (n : Nat) : Core.RuntimeEnvironmentHasTypes [] (inputs n).environment.values (inputs n).context.values := by
  have f : Core.RuntimeValueHasType [] (delayed n) (.function .unit .unit) :=
    .closure (.cons .unit .nil) (delayTyped n 1 [.unit] rfl)
  exact .cons .unit (.cons f (.cons f (.cons .bool .nil)))

theorem original_projection_checking_and_manual_paths (n : Nat) (s t : Syntax.SourceSpan) (store : Core.Store) :
    (inputs n).checkApplication? (source s t) = some (core, .unit) ∧
    LocalFunctionApplicationHasType (inputs n).names (inputs n).context (source s t) .unit ∧
    LocalFunctionApplicationEvaluatesWithCost (inputs n).names (inputs n).environment store (source s t) .unit store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (inputs n).environment.values, k, store⟩ ⟨.ret .unit, k, store⟩ := by
  have checked := LocalInputs.checkApplication?_iff_elaborates.mpr (exact n s t)
  refine ⟨checked, LocalInputs.checkApplication?_iff_hasType.mp ⟨core, checked⟩, counted n store s t, ?_⟩
  intro k
  have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (delayPath n 1 [.unit] store [] rfl) (function := .var 1) (argument := .var 0)
    (environment := (inputs n).environment.values) (parameterType := Core.Ty.unit) (resultType := Core.Ty.unit) (continuation := k)
  have costs : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact costs ▸ path

theorem one_actual_cost_gives_both_all_fuel_boundaries (n fuel : Nat) (store : Core.Store) :
    ((inputs n).runApplication? fuel (source span span) store = some (.unit, .done .unit store) ↔ 3 * n + 6 ≤ fuel) ∧
    ((∃ cp, (inputs n).runApplication? fuel (source span span) store = some (.unit, .outOfFuel cp)) ↔ fuel < 3 * n + 6) :=
  ⟨LocalInputs.runApplication?_done_iff_of_cost (exact n span span).hasType (counted n store span span),
    LocalInputs.runApplication?_outOfFuel_iff_of_cost (exact n span span).hasType (counted n store span span)⟩

theorem observed_completion_reflects_independent_typed_cost (n : Nat) (store : Core.Store) :
    LocalFunctionApplicationHasType (inputs n).names (inputs n).context (source span span) .unit ∧
    ∃ cost, LocalFunctionApplicationEvaluatesWithCost (inputs n).names (inputs n).environment store (source span span) .unit store cost ∧ cost ≤ 3 * n + 6 :=
  LocalInputs.runApplication?_done_iff_typed_cost.mp
    ((one_actual_cost_gives_both_all_fuel_boundaries n (3 * n + 6) store).1.mpr (Nat.le_refl _))

theorem runtime_existence_does_not_replace_the_actual_cost (n : Nat) :
    ∃ future, Core.WorldExtends [] future ∧ Core.RuntimeStoreHasTypes future [] ∧ Core.RuntimeValueHasType future .unit .unit ∧
      ∀ fuel, ((inputs n).runApplication? fuel (source span span) [] = some (.unit, .done .unit []) ↔ 3 * n + 6 ≤ fuel) ∧
        ((∃ cp, (inputs n).runApplication? fuel (source span span) [] = some (.unit, .outOfFuel cp)) ↔ fuel < 3 * n + 6) := by
  obtain ⟨future, final, value, cost, ext, st, vt, evaluation, thresholds⟩ :=
    LocalInputs.runApplication?_runtime_has_exact_cost (exact n span span).hasType (runtimeInputs n) Core.StoreHasTypes.nil ⟨.unit, [], (counted n [] span span).erase⟩
  obtain ⟨rfl, rfl, rfl⟩ := evaluation.deterministic (counted n [] span span)
  exact ⟨future, ext, st, vt, thresholds⟩

theorem fixed_source_and_types_do_not_bound_typed_actual_bodies (bound : Nat) :
    ∃ n cost, Core.RuntimeEnvironmentHasTypes [] (inputs n).environment.values (inputs n).context.values ∧ bound < cost ∧
      (inputs n).runApplication? cost (source span span) [] = some (.unit, .done .unit []) :=
  ⟨bound, 3 * bound + 6, runtimeInputs bound, by omega,
    (one_actual_cost_gives_both_all_fuel_boundaries bound (3 * bound + 6) []).1.mpr (Nat.le_refl _)⟩

private def delayCheckpoint (n : Nat) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (inputs n).environment.values, [.applyClosure .unit .unit (delay n 1) [.unit]], store⟩
theorem genuine_delayed_checkpoint_retains_type_and_every_resumed_result (n additional : Nat) (store : Core.Store) :
    (inputs n).runApplication? 3 (source span span) store = some (.unit, .outOfFuel (delayCheckpoint n store)) ∧
    Core.Steps (3 * n + 3) (delayCheckpoint n store) (.final .unit store) ∧
    (inputs n).runApplication? (3 + additional) (source span span) store =
      some (.unit, Core.runStateful additional (delayCheckpoint n store)) := by
  have stopped : (inputs n).runApplication? 3 (source span span) store = some (.unit, .outOfFuel (delayCheckpoint n store)) :=
    LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, (exact n span span).complete, rfl⟩
  have remaining : 3 * n + 6 - 3 = 3 * n + 3 := by omega
  exact ⟨stopped, by simpa only [remaining] using (LocalInputs.runApplication?_residual_of_outOfFuel (counted n store span span) stopped).2,
    LocalInputs.runApplication?_resume stopped additional⟩

private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def reader : Core.Value := .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]
private theorem readerTyped : Core.ValueHasType reader (.function .unit .word) :=
  .closure (.cons .cellRef .nil) (.loadCell (.var rfl))
private def readerInputs : LocalInputs := bundle .unit .word reader .unit readerTyped .unit
private theorem readerExact : LocalFunctionApplicationElaborates readerInputs.names readerInputs.context (source span span) core .word :=
  elaborated .unit .word reader .unit readerTyped .unit span span
private theorem readerRuntime : Core.RuntimeEnvironmentHasTypes [.word] readerInputs.environment.values readerInputs.context.values := by
  have f : Core.RuntimeValueHasType [.word] reader (.function .unit .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
  exact .cons .unit (.cons f (.cons f (.cons .bool .nil)))
private theorem storeTyped (n : Nat) : Core.StoreHasTypes [.word] [w n] := Core.StoreHasTypes.nil.allocate .word .word
private theorem readerCost (value : Core.Value) : LocalFunctionApplicationEvaluatesWithCost readerInputs.names readerInputs.environment
    [value] (source span span) value [value] 8 :=
  callCost .unit .word (.loadCell (.var 1)) [.cellRef .word 0] .unit value readerTyped .unit [value] [value] 3 span span
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
private def readerCheckpoint (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) readerInputs.environment.values, [.applyClosure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]], store⟩

theorem valid_reader_has_runtime_typed_soundness_and_all_fuel_safety
    (n fuel : Nat) (type : Core.Ty) (error : Core.MachineFault) (fault : Core.State) :
    readerInputs.runApplication? 8 (source span span) [w n] = some (.word, .done (w n) [w n]) ∧
    (∃ future, Core.WorldExtends [.word] future ∧ Core.RuntimeStoreHasTypes future [w n] ∧ Core.RuntimeValueHasType future (w n) .word) ∧
    readerInputs.runApplication? fuel (source span span) [w n] ≠ some (type, .fault error fault) := by
  have done := (LocalInputs.runApplication?_done_iff_of_cost readerExact.hasType (readerCost (w n))).mpr (Nat.le_refl 8)
  exact ⟨done, (LocalInputs.runApplication?_runtime_done_sound readerRuntime (storeTyped n) done).2,
    LocalInputs.runApplication?_runtime_never_faults readerRuntime (storeTyped n) (source span span) fuel type error fault⟩

theorem reader_resume_is_not_a_restart (n additional : Nat) :
    readerInputs.runApplication? 3 (source span span) [w n] = some (.word, .outOfFuel (readerCheckpoint [w n])) ∧
    Core.Steps 5 (readerCheckpoint [w n]) (.final (w n) [w n]) ∧
    Core.runStateful 5 (readerCheckpoint [w n]) = .done (w n) [w n] ∧
    readerInputs.runApplication? 5 (source span span) [w n] ≠ some (.word, .done (w n) [w n]) ∧
    readerInputs.runApplication? (3 + additional) (source span span) [w n] = some (.word, Core.runStateful additional (readerCheckpoint [w n])) := by
  have stopped : readerInputs.runApplication? 3 (source span span) [w n] = some (.word, .outOfFuel (readerCheckpoint [w n])) :=
    LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, readerExact.complete, rfl⟩
  refine ⟨stopped, (LocalInputs.runApplication?_residual_of_outOfFuel (readerCost (w n)) stopped).2, rfl, ?_,
    LocalInputs.runApplication?_resume stopped additional⟩
  intro done
  have enough := (LocalInputs.runApplication?_done_iff_of_cost readerExact.hasType (readerCost (w n))).mp done
  omega

theorem missing_store_remains_present_and_resumes_to_the_original_fault :
    Core.RuntimeEnvironmentHasTypes [.word] readerInputs.environment.values readerInputs.context.values ∧
    (¬ Core.StoreHasTypes [.word] []) ∧
    readerInputs.runApplication? 3 (source span span) [] = some (.word, .outOfFuel (readerCheckpoint [])) ∧
    readerInputs.runApplication? 7 (source span span) [] =
      some (.word, .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩) ∧
    readerInputs.runApplication? 7 (source span span) [] = some (.word, Core.runStateful 4 (readerCheckpoint [])) := by
  have stopped : readerInputs.runApplication? 3 (source span span) [] = some (.word, .outOfFuel (readerCheckpoint [])) :=
    LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, readerExact.complete, rfl⟩
  refine ⟨readerRuntime, ?_, stopped, LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, readerExact.complete, rfl⟩,
    LocalInputs.runApplication?_resume stopped 4⟩
  intro st
  have := st.length_eq
  contradiction

theorem wrong_payload_preserves_the_word_tag_and_actual_bool_result :
    readerInputs.runApplication? 8 (source span span) [.bool true] = some (.word, .done (.bool true) [.bool true]) ∧
    LocalFunctionApplicationEvaluates readerInputs.names readerInputs.environment [.bool true] (source span span) (.bool true) [.bool true] ∧
    (¬ Core.StoreHasTypes [.word] [.bool true]) ∧ (¬ Core.RuntimeValueHasType [.word] (.bool true) .word) := by
  have done := (LocalInputs.runApplication?_done_iff_of_cost readerExact.hasType (readerCost (.bool true))).mpr (Nat.le_refl 8)
  refine ⟨done, LocalInputs.runApplication?_done_sound done, ?_, by intro t; cases t⟩
  intro st
  obtain ⟨v, found, _, typed⟩ := st.lookup (location := 0) rfl
  have same : v = .bool true := Option.some.inj found.symm
  subst v
  cases typed

private def rejected : Syntax.Expr :=
  ⟨span, .call ⟨span, .conditional (ref span "c") span (ref span "f") span (ref span "missing")⟩ ⟨span, [ref span "x"]⟩⟩
theorem raw_selected_success_does_not_supply_the_whole_gate (fuel : Nat) (store : Core.Store) :
    LocalFunctionApplicationEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] rejected (w 23) [w 23] 11 ∧
    readerInputs.checkApplication? rejected = none ∧ readerInputs.runApplication? fuel rejected store = none := by
  have missing : readerInputs.checkApplication? rejected = none := by
    simp [LocalInputs.checkApplication?, elaborateLocalFunctionApplication?, rejected, elaborateLocalExpression?,
      resolveLocalExpression?, readerInputs, bundle, LocalInputs.names, ref, LocalNameTable.lookup?]
  refine ⟨?_, missing, (LocalInputs.runApplication?_eq_none_iff fuel store).mpr missing⟩
  have guard : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "c") (.bool true) [w 23] 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
      (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have function : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "f") reader [w 23] 1 :=
    .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have chosen : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23]
      ⟨span, .conditional (ref span "c") span (ref span "f") span (ref span "missing")⟩ reader [w 23] 4 :=
    .ifTrue guard function
  have argument : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "x") .unit [w 23] 1 :=
    .identifier .head .head
  exact .call (parameterType := .unit) (resultType := .word) (body := .loadCell (.var 1)) (captured := [.cellRef .word 0])
    chosen argument (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))

theorem old_pure_gate_and_raw_typed_completion_remain_distinct (n fuel : Nat) (store : Core.Store) :
    (inputs n).check? (source span span) = none ∧ (inputs n).run? fuel (source span span) store = none ∧
    (∃ chosen, (inputs n).runApplication? chosen (source span span) store = some (.unit, .done .unit store)) := by
  refine ⟨?_, ?_, LocalInputs.runApplication?_done_iff_typed_evaluation.mpr ⟨(exact n span span).hasType, (counted n store span span).erase⟩⟩
  all_goals simp [LocalInputs.run?, LocalInputs.check?, source, elaborateLocalExpression?, resolveLocalExpression?]

end Tests.FrontendLocalApplicationRunner
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationRuntimeSafetyProperties
/-! Actual values, worlds and stores are independent evidence, not inferred
from accepted source syntax. A typed continuation is a separate obligation. -/
set_option autoImplicit false
namespace Tests.FrontendLocalApplicationRuntimeSafety
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RuntimeCall", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def names : LocalNameTable := [("f", fid), ("x", aid), ("f", aid)]
private def context (a b : Core.Ty) : Resolved.Context := [(aid, a), (fid, .function a b)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "runtime-call.sol"⟩, 31, 4⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (s t : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .call (ref s "f") ⟨t, [ref t "x"]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private def environment (f x : Core.Value) : Resolved.Environment := [(aid, x), (fid, f)]
private theorem elaborated (a b : Core.Ty) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source s t) core b :=
  .call (parameterType := a) (.identifier .head)
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head)
private theorem callCost (a b : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (x value : Core.Value) (store final : Core.Store) (cost : Nat) (s t : Syntax.SourceSpan)
    (path : Core.Steps cost (.initial body (x :: captured) store) (.final value final)) :
    LocalFunctionApplicationEvaluatesWithCost names (environment (.closure a b body captured) x)
      store (source s t) value final (1 + 1 + cost + 3) :=
  .call (.identifier .head (.tail (by decide) .head))
    (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head) path
private theorem environmentTyped {world : Core.StoreTyping} {a b : Core.Ty} {f x : Core.Value}
    (ft : Core.RuntimeValueHasType world f (.function a b)) (xt : Core.RuntimeValueHasType world x a) :
    Core.RuntimeEnvironmentHasTypes world (environment f x).values (context a b).values :=
  .cons xt (.cons ft .nil)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private theorem delayTyped (n index : Nat) (a b : Core.Ty) (rest : Core.Context)
    (found : (a :: rest)[index]? = some b) : Core.HasType (a :: rest) (delay n index) b := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index + 1) (a :: rest) (by simpa using found))
private theorem delayPath (n index : Nat) (x v : Core.Value) (rest : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) (found : (x :: rest)[index]? = some v) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n index) (x :: rest), k, store⟩ ⟨.ret v, k, store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (x :: rest) k (by simpa using found))))
private def delayed (a b : Core.Ty) (n : Nat) (v : Core.Value) : Core.Value := .closure a b (delay n 1) [v]
private theorem delayedTyped {world : Core.StoreTyping} {a b : Core.Ty} {v : Core.Value}
    (typed : Core.RuntimeValueHasType world v b) (n : Nat) :
    Core.RuntimeValueHasType world (delayed a b n v) (.function a b) :=
  .closure (.cons typed .nil) (delayTyped n 1 a b [b] rfl)
private theorem delayedCost (a b : Core.Ty) (n : Nat) (x v : Core.Value) (store : Core.Store)
    (s t : Syntax.SourceSpan) : LocalFunctionApplicationEvaluatesWithCost names
      (environment (delayed a b n v) x) store (source s t) v store (3 * n + 6) := by
  have path := callCost a b (delay n 1) [v] x v store store (3 * n + 1) s t (delayPath n 1 x v [v] store [] rfl)
  have equal : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact equal ▸ path

theorem independent_actual_typed_depth_has_exact_cost {world : Core.StoreTyping} {a b : Core.Ty}
    {x v : Core.Value} (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) (store : Core.Store) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source s t) core b ∧
    Core.RuntimeEnvironmentHasTypes world (environment (delayed a b n v) x).values (context a b).values ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment (delayed a b n v) x) store (source s t) v store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment (delayed a b n v) x).values, k, store⟩ ⟨.ret v, k, store⟩ := by
  refine ⟨elaborated a b s t, environmentTyped (delayedTyped vt n) xt, delayedCost a b n x v store s t, ?_⟩
  intro k
  have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (delayPath n 1 x v [v] store [] rfl) (function := .var 1) (argument := .var 0)
    (environment := (environment (delayed a b n v) x).values) (parameterType := a) (resultType := b) (continuation := k)
  have equal : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact equal ▸ path

theorem fixed_source_and_types_have_no_uniform_actual_body_cost (bound : Nat) :
    ∃ f cost, Core.RuntimeEnvironmentHasTypes [] (environment f .unit).values (context .unit .unit).values ∧
      LocalFunctionApplicationEvaluatesWithCost names (environment f .unit) [] (source span span) .unit [] cost ∧ bound < cost :=
  ⟨delayed .unit .unit bound .unit, 3 * bound + 6, environmentTyped (delayedTyped .unit bound) .unit,
    delayedCost .unit .unit bound .unit .unit [] span span, by omega⟩

private def reader : Core.Value := .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private theorem readerTyped : Core.RuntimeValueHasType [.word] reader (.function .unit .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
private theorem wordStore (n : Nat) : Core.StoreHasTypes [.word] [w n] := by
  simpa [w] using Core.StoreHasTypes.nil.allocate .word (Core.ValueHasType.word (value := Core.Word.ofNatModulo n))
private theorem readerCost (n : Nat) : LocalFunctionApplicationEvaluatesWithCost names
    (environment reader .unit) [w n] (source span span) (w n) [w n] 8 :=
  callCost .unit .word (.loadCell (.var 1)) [.cellRef .word 0] .unit (w n) [w n] [w n] 3 span span
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
private def checkpoint (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (environment reader .unit).values, [.applyClosure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]], store⟩

theorem captured_reference_has_independent_world_store_and_value (n : Nat) :
    Core.RuntimeEnvironmentHasTypes [.word] (environment reader .unit).values (context .unit .word).values ∧
    Core.StoreHasTypes [.word] [w n] ∧ Core.RuntimeValueHasType [.word] (w n) .word ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment reader .unit) [w n] (source span span) (w n) [w n] 8 :=
  ⟨environmentTyped readerTyped .unit, wordStore n, .word, readerCost n⟩

theorem typed_reader_preserves_its_genuine_checkpoint_and_safe_resumption
    (n fuel additional : Nat) (error : Core.MachineFault) (faultState : Core.State) :
    Core.StateHasType (.initial core (environment reader .unit).values [w n]) .word ∧
    Core.runStateful fuel (.initial core (environment reader .unit).values [w n]) ≠ .fault error faultState ∧
    Core.runStateful 3 (.initial core (environment reader .unit).values [w n]) = .outOfFuel (checkpoint [w n]) ∧
    Core.StateHasType (checkpoint [w n]) .word ∧
    Core.runStateful additional (checkpoint [w n]) ≠ .fault error faultState ∧
    Core.runStateful additional (checkpoint [w n]) = Core.runStateful (3 + additional) (.initial core (environment reader .unit).values [w n]) ∧
    Core.Steps 5 (checkpoint [w n]) (.final (w n) [w n]) := by
  have e := elaborated .unit .word span span
  have envt := environmentTyped readerTyped Core.RuntimeValueHasType.unit
  have stopped : Core.runStateful 3 (.initial core (environment reader .unit).values [w n]) = .outOfFuel (checkpoint [w n]) := rfl
  exact ⟨e.runtime_state_hasType envt (wordStore n) .nil,
    e.runtime_run_never_faults envt (wordStore n) .nil fuel error faultState, stopped,
    e.runtime_checkpoint_hasType envt (wordStore n) .nil stopped,
    e.runtime_checkpoint_never_faults envt (wordStore n) .nil stopped additional error faultState,
    Core.runStateful_resume stopped additional, ((readerCost n).toSteps e rfl).residual_of_outOfFuel stopped |>.2⟩

theorem typed_completion_retains_the_independently_fixed_value_and_cost
    {world : Core.StoreTyping} {a b : Core.Ty} {x v : Core.Value}
    (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) {store : Core.Store} (st : Core.StoreHasTypes world store) :
    ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future store ∧
      Core.RuntimeValueHasType future v b ∧ LocalFunctionApplicationEvaluatesWithCost names
        (environment (delayed a b n v) x) store (source span span) v store (3 * n + 6) := by
  obtain ⟨future, final, result, cost, ext, stored, typed, evaluated⟩ :=
    (elaborated a b span span).hasType.runtime_evaluates rfl (environmentTyped (delayedTyped vt n) xt) st
      ⟨v, store, (delayedCost a b n x v store span span).erase⟩
  obtain ⟨rfl, rfl, rfl⟩ := evaluated.deterministic (delayedCost a b n x v store span span)
  exact ⟨future, ext, stored, typed, evaluated⟩

theorem actual_cost_precedes_all_endpoints_and_closed_fuel_thresholds
    {world : Core.StoreTyping} {a b : Core.Ty} {x v : Core.Value}
    (xt : Core.RuntimeValueHasType world x a) (vt : Core.RuntimeValueHasType world v b)
    (n : Nat) {store : Core.Store} (st : Core.StoreHasTypes world store) :
    (∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment (delayed a b n v) x).values, k, store⟩ ⟨.ret v, k, store⟩) ∧
    ∀ fuel, (Core.runStateful fuel (.initial core (environment (delayed a b n v) x).values store) = .done v store ↔ 3 * n + 6 ≤ fuel) ∧
      ((∃ cp, Core.runStateful fuel (.initial core (environment (delayed a b n v) x).values store) = .outOfFuel cp) ↔ fuel < 3 * n + 6) := by
  obtain ⟨_, final, result, cost, _, _, _, evaluated, paths, thresholds⟩ :=
    (elaborated a b span span).runtime_typed_execution rfl (environmentTyped (delayedTyped vt n) xt) st
      ⟨v, store, (delayedCost a b n x v store span span).erase⟩
  obtain ⟨rfl, rfl, rfl⟩ := evaluated.deterministic (delayedCost a b n x v store span span)
  exact ⟨paths, thresholds⟩

theorem preservation_and_checker_soundness_keep_the_actual_store (n : Nat) :
    (∃ future, Core.WorldExtends [.word] future ∧ Core.RuntimeStoreHasTypes future [w n] ∧ Core.RuntimeValueHasType future (w n) .word) ∧
    LocalFunctionApplicationEvaluates names (environment reader .unit) [w n] (source span span) (w n) [w n] := by
  have e := elaborated .unit .word span span
  have et := environmentTyped readerTyped Core.RuntimeValueHasType.unit
  have preservation := (readerCost n).erase.preserves_runtime_type e rfl et (wordStore n)
  have completed := ((readerCost n).toSteps e rfl).runStateful_done_iff.mpr (Nat.le_refl 8)
  have sound := elaborateLocalFunctionApplication?_runtime_run_done_sound e.complete rfl et (wordStore n) completed
  exact ⟨preservation, sound.1⟩

private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
theorem allocation_changes_both_the_store_and_its_world {world : Core.StoreTyping} {store : Core.Store}
    (st : Core.StoreHasTypes world store) (n : Nat) :
    Core.RuntimeEnvironmentHasTypes world (environment allocator (w n)).values (context .word (.cell .word)).values ∧
    Core.WorldExtends world (world ++ [.word]) ∧ Core.StoreHasTypes (world ++ [.word]) (store ++ [w n]) ∧
    Core.RuntimeValueHasType (world ++ [.word]) (.cellRef .word store.length) (.cell .word) ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment allocator (w n)) store (source span span)
      (.cellRef .word store.length) (store ++ [w n]) 8 ∧ store ++ [w n] ≠ store := by
  refine ⟨environmentTyped (.closure .nil (.newCell (.var rfl))) .word, ⟨[.word], rfl⟩,
    st.allocate .word .word, .cellRef ?_, ?_, ?_⟩
  · simp [← st.length_eq]
  · exact callCost .word (.cell .word) (.newCell .word (.var 0)) [] (w n) (.cellRef .word store.length)
      store (store ++ [w n]) 3 span span (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  · intro equal
    have lengths := congrArg List.length equal
    simp at lengths

theorem arbitrary_outer_frames_need_their_own_typing (n fuel : Nat) (k : List Core.Frame) (result : Core.Ty)
    (kt : Core.ContinuationHasType [.word] k .word result) (error : Core.MachineFault) (faultState : Core.State) :
    Core.StateHasType ⟨.eval core (environment reader .unit).values, k, [w n]⟩ result ∧
    Core.runStateful fuel ⟨.eval core (environment reader .unit).values, k, [w n]⟩ ≠ .fault error faultState :=
  ⟨(elaborated .unit .word span span).runtime_state_hasType (environmentTyped readerTyped .unit) (wordStore n) kt,
    (elaborated .unit .word span span).runtime_run_never_faults (environmentTyped readerTyped .unit) (wordStore n) kt fuel error faultState⟩

theorem runtime_world_alone_does_not_validate_an_empty_store :
    Core.RuntimeEnvironmentHasTypes [.word] (environment reader .unit).values (context .unit .word).values ∧
    ¬ Core.StoreHasTypes [.word] [] ∧
    Core.runStateful 7 (.initial core (environment reader .unit).values []) =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ := by
  refine ⟨environmentTyped readerTyped .unit, ?_, rfl⟩
  intro stored
  have lengths := stored.length_eq
  cases lengths

theorem equal_lengths_do_not_make_wrong_payloads_runtime_safe :
    ([Core.Ty.word] : Core.StoreTyping).length = ([Core.Value.bool true] : Core.Store).length ∧
    ¬ Core.StoreHasTypes [.word] [.bool true] ∧
    Core.runStateful 8 (.initial core (environment reader .unit).values [.bool true]) = .done (.bool true) [.bool true] ∧
    ¬ Core.RuntimeValueHasType [.word] (.bool true) .word := by
  refine ⟨rfl, ?_, rfl, by intro typed; cases typed⟩
  intro stored
  obtain ⟨v, found, _, typed⟩ := stored.lookup (location := 0) rfl
  have same : v = .bool true := Option.some.inj found.symm
  subst v
  cases typed

theorem structural_reference_typing_does_not_supply_a_runtime_world :
    Core.ValueHasType (.cellRef .word 700) (.cell .word) ∧
    ¬ Core.RuntimeValueHasType [] (.cellRef .word 700) (.cell .word) := by
  refine ⟨.cellRef, ?_⟩
  intro typed
  cases typed with
  | cellRef found => cases found

private def nominal : Core.Ty := .namedData ⟨0⟩
private def nominalIdentity : Core.Value := .closure nominal nominal (.var 0) []
private theorem noNominal (dataType : Core.DataTypeId) {v : Core.Value}
    (typed : Core.RuntimeValueHasType [] v (.namedData dataType)) : False := by
  cases typed with
  | constructed lookup _ => cases lookup
theorem higher_order_nominal_functions_are_values_without_nominal_inhabitants :
    (¬ ∃ v, Core.RuntimeValueHasType [] v nominal) ∧
    Core.RuntimeValueHasType [] nominalIdentity (.function nominal nominal) ∧
    Core.RuntimeEnvironmentHasTypes []
      (environment (delayed (.function nominal nominal) (.function nominal nominal) 0 nominalIdentity) nominalIdentity).values
      (context (.function nominal nominal) (.function nominal nominal)).values ∧
    LocalFunctionApplicationEvaluatesWithCost names
      (environment (delayed (.function nominal nominal) (.function nominal nominal) 0 nominalIdentity) nominalIdentity)
      [] (source span span) nominalIdentity [] 6 := by
  have typed : Core.RuntimeValueHasType [] nominalIdentity (.function nominal nominal) := .closure .nil (.var rfl)
  refine ⟨?_, typed, environmentTyped (delayedTyped typed 0) typed,
    delayedCost _ _ 0 nominalIdentity nominalIdentity [] span span⟩
  rintro ⟨v, vt⟩
  exact noNominal ⟨0⟩ vt

theorem a_typed_call_endpoint_does_not_type_an_arbitrary_pending_frame :
    Core.RuntimeEnvironmentHasTypes [] (environment (delayed .unit .unit 0 .unit) .unit).values (context .unit .unit).values ∧
    (¬ ∃ result, Core.ContinuationHasType [] [.unaryApply .wordNot] .unit result) ∧
    Core.Steps 6 ⟨.eval core (environment (delayed .unit .unit 0 .unit) .unit).values, [.unaryApply .wordNot], []⟩
      ⟨.ret .unit, [.unaryApply .wordNot], []⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], []⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], []⟩ := by
  refine ⟨environmentTyped (delayedTyped .unit 0) .unit, ?_,
    (independent_actual_typed_depth_has_exact_cost (world := []) .unit .unit 0 [] span span).2.2.2 _, rfl⟩
  rintro ⟨_, kt⟩
  cases kt with
  | cons frame _ => cases frame

end Tests.FrontendLocalApplicationRuntimeSafety
end

section
-- leanmerge: from Solcore.Test.FrontendLocalComputationProperties
/-! Independent pure and actual-call certificates preserve the raw boundary.
Source typing does not manufacture actual captures, safe stores or body support. -/
set_option autoImplicit false
namespace Tests.FrontendLocalComputation
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Computation", by decide⟩], by decide⟩⟩, 50⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 2⟩
private def names : LocalNameTable := [("f", fid), ("x", xid), ("f", gid)]
private def context (a b : Core.Ty) : Resolved.Context := [(xid, a), (fid, .function a b), (gid, .unit), (fid, .unit)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "computation.sol"⟩, 250, 3⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (app : Bool) (s : Syntax.SourceSpan) : Syntax.Expr :=
  if app then ⟨s, .call (ref s "f") ⟨s, [ref s "x"]⟩⟩ else ref s "x"
private def core (app : Bool) : Core.Expr := if app then .apply (.var 1) (.var 0) else .var 0
private def resultType (app : Bool) (a b : Core.Ty) := if app then b else a
private theorem provenance (app : Bool) (a b : Core.Ty) (s : Syntax.SourceSpan) :
    LocalComputationElaborates names (context a b) (source app s) (core app) (resultType app a b) := by
  cases app
  · exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head)
  · exact .application (.call (.identifier .head) (.var (.tail (by change xid ≠ fid; decide) .head))
      (.var (.tail (by change xid ≠ fid; decide) .head)) (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head))
private theorem typing (app : Bool) (a b : Core.Ty) (s : Syntax.SourceSpan) :
    LocalComputationHasType names (context a b) (source app s) (resultType app a b) := by
  cases app
  · exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  · exact .application (.call (.identifier .head (.tail (by change xid ≠ fid; decide) .head))
      (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head))
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def environment (n : Nat) (argument captured : Core.Value) : Resolved.Environment :=
  [(xid, argument), (fid, .closure .unit .unit (delay n 1) [captured]), (gid, .unit), (fid, .bool false)]
private def answer (app : Bool) (argument captured : Core.Value) := if app then captured else argument
private def cost (app : Bool) (n : Nat) := if app then 3 * n + 6 else 1
private theorem bodyRaw (n index : Nat) (argument : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (found : (argument :: rest)[index]? = some value) :
    Core.Evaluates (argument :: rest) store (delay n index) value store := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index + 1) (argument :: rest) (by simpa using found))
private theorem bodyPath (n index : Nat) (argument : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (k : List Core.Frame)
    (found : (argument :: rest)[index]? = some value) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n index) (argument :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (argument :: rest) k (by simpa using found))))
private theorem raw (app : Bool) (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    LocalComputationEvaluates names (environment n argument captured) store (source app span) (answer app argument captured) store := by
  cases app
  · exact .pure (.identifier (.tail (by decide) .head) .head)
  · exact .application (.call (.identifier .head (.tail (by decide) .head))
      (.identifier (.tail (by decide) .head) .head) (bodyRaw n 1 argument [captured] captured store rfl))
private theorem counted (app : Bool) (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    LocalComputationEvaluatesWithCost names (environment n argument captured) store (source app span)
      (answer app argument captured) store (cost app n) := by
  cases app
  · exact .pure (.identifier (.tail (by decide) .head) .head)
  · have count : 3 * n + 6 = 1 + 1 + (3 * n + 1) + 3 := by omega
    rw [cost, if_pos rfl, count]
    exact .application (.call (.identifier .head (.tail (by decide) .head))
      (.identifier (.tail (by decide) .head) .head) (bodyPath n 1 argument [captured] captured store [] rfl))
private theorem manual (app : Bool) (n : Nat) (argument captured : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost app n) ⟨.eval (core app) (environment n argument captured).values, k, store⟩
      ⟨.ret (answer app argument captured), k, store⟩ := by
  cases app
  · exact .cons (.var rfl) .refl
  · have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
      (bodyPath n 1 argument [captured] captured store [] rfl)
      (function := .var 1) (argument := .var 0) (environment := (environment n argument captured).values)
      (parameterType := .unit) (resultType := .unit) (continuation := k)
    have count : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
    simpa [cost, core, answer, count] using path

theorem original_static_types_and_spans_supply_no_runtime_inhabitants (app : Bool) (a b : Core.Ty) (s : Syntax.SourceSpan) :
    LocalComputationHasType names (context a b) (source app s) (resultType app a b) ∧
    elaborateLocalComputation? names (context a b) (source app s) = some (core app, resultType app a b) ∧
    Core.HasType (context a b).values (core app) (resultType app a b) ∧
    ∃ c, LocalComputationElaborates names (context a b) (source app s) c (resultType app a b) :=
  ⟨typing app a b s, elaborateLocalComputation?_iff.mpr (provenance app a b s),
    (provenance app a b s).core_hasType, localComputationHasType_iff_elaborates.mp (typing app a b s)⟩

theorem both_original_branches_have_independent_actual_costs (app : Bool) (n : Nat)
    (argument captured : Core.Value) (store : Core.Store) :
    LocalComputationEvaluates names (environment n argument captured) store (source app span) (answer app argument captured) store ∧
    LocalComputationEvaluatesWithCost names (environment n argument captured) store (source app span) (answer app argument captured) store (cost app n) ∧
    ∀ k, Core.Steps (cost app n) ⟨.eval (core app) (environment n argument captured).values, k, store⟩ ⟨.ret (answer app argument captured), k, store⟩ :=
  ⟨raw app n argument captured store, counted app n argument captured store, manual app n argument captured store⟩

theorem cost_existence_and_joint_uniqueness_do_not_check_actual_types (app : Bool) (n : Nat)
    (argument captured other : Core.Value) (store finalStore : Core.Store) (otherCost : Nat)
    (candidate : LocalComputationEvaluatesWithCost names (environment n argument captured) store (source app span) other finalStore otherCost) :
    other = answer app argument captured ∧ finalStore = store ∧ otherCost = cost app n ∧
    LocalComputationEvaluates names (environment n argument captured) store (source app span) other finalStore ∧
    ∃ c, LocalComputationEvaluatesWithCost names (environment n argument captured) store (source app span) (answer app argument captured) store c := by
  obtain ⟨v, s, c⟩ := candidate.deterministic (counted app n argument captured store)
  exact ⟨v, s, c, localComputationEvaluates_iff_exists_cost.mpr ⟨_, candidate⟩,
    localComputationEvaluates_iff_exists_cost.mp (raw app n argument captured store)⟩

theorem correspondence_uses_ordered_ids_not_static_runtime_tag_agreement (app : Bool) (a b : Core.Ty) (n : Nat)
    (argument captured : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Evaluates (environment n argument captured).values store (core app) (answer app argument captured) store ∧
    LocalComputationEvaluatesWithCost names (environment n argument captured) store (source app span) (answer app argument captured) store (cost app n) ∧
    Core.Steps (cost app n) ⟨.eval (core app) (environment n argument captured).values, k, store⟩ ⟨.ret (answer app argument captured), k, store⟩ :=
  ⟨((provenance app a b span).evaluates_iff rfl).mp (raw app n argument captured store),
    ((provenance app a b span).evaluatesWithCost_iff_steps rfl).mpr (manual app n argument captured store []),
    (counted app n argument captured store).toStepsWithContinuation (provenance app a b span) rfl k⟩

theorem typing_insertion_keeps_arbitrary_definitions_and_uninhabited_slot_types
    (app : Bool) (a b inserted : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType (inserted :: (context a b).values) ((core app).weakenAt 0) (resultType app a b) definitions ∧
    Core.HasType (context a b).values (core app) (resultType app a b) definitions := by
  have original : Core.HasType (context a b).values (core app) (resultType app a b) definitions := by
    cases app <;> first | exact .var rfl | exact .apply (.var rfl) (.var rfl)
  have added := ((provenance app .word .word span).core_hasType_insert_iff [] (context a b).values inserted).mpr original
  exact ⟨added, ((provenance app .word .word span).core_hasType_insert_iff [] (context a b).values inserted).mp added⟩

theorem insertion_shares_the_manual_cost_before_all_pending_frames (app : Bool) (n : Nat)
    (argument captured inserted : Core.Value) (store : Core.Store) (leading suffix : Core.Environment)
    (split : leading ++ suffix = (environment n argument captured).values) :
    Core.Evaluates (leading ++ inserted :: suffix) store ((core app).weakenAt leading.length) (answer app argument captured) store ∧
    ∃ c, c = cost app n ∧ ∀ k,
      Core.Steps c ⟨.eval (core app) (leading ++ suffix), k, store⟩ ⟨.ret (answer app argument captured), k, store⟩ ∧
      Core.Steps c ⟨.eval ((core app).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret (answer app argument captured), k, store⟩ := by
  have evaluation := split ▸ Core.steps_from_initial_sound (manual app n argument captured store [])
  have e := provenance app .word .word span
  have added := (e.core_evaluates_insert_iff leading suffix inserted).mpr evaluation
  have recovered := (e.core_evaluates_insert_iff leading suffix inserted).mp added
  obtain ⟨c, paths⟩ := e.core_insertion_paths leading suffix inserted recovered
  exact ⟨added, c, ((paths []).1.final_unique (split ▸ manual app n argument captured store [])).1, paths⟩

private def skipped : Syntax.Expr := ⟨span, .conditional (ref span "x") span (ref span "f") span (ref span "missing")⟩
theorem unselected_unknown_pure_child_keeps_raw_success_but_not_whole_checking (value : Core.Value) (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .bool true), (fid, value), (gid, .unit), (fid, .unit)]
    LocalComputationEvaluates names env store skipped value store ∧
    LocalComputationEvaluatesWithCost names env store skipped value store 4 ∧
    elaborateLocalComputation? names (context .bool .unit) skipped = none := by
  refine ⟨.pure (.ifTrue (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head))),
    .pure (.ifTrue (conditionCost := 1) (branchCost := 1)
      (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head))), ?_⟩
  simp [elaborateLocalComputation?, skipped, ref, elaborateLocalExpression?, resolveLocalExpression?, names, LocalNameTable.lookup?]

private def short (and : Bool) : Syntax.Expr := ⟨span, .binary (ref span "x") ⟨span, if and then .logicalAnd else .logicalOr⟩ (ref span "f")⟩
theorem selected_short_circuit_right_values_need_not_be_bool (and : Bool) (value : Core.Value) (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .bool and), (fid, value), (gid, .unit), (fid, .unit)]
    LocalComputationEvaluates names env store (short and) value store ∧
    LocalComputationEvaluatesWithCost names env store (short and) value store 4 ∧
    elaborateLocalComputation? names (context .bool .unit) (short and) = none := by
  cases and <;> refine ⟨?_, ?_, ?_⟩
  · exact .pure (.orFalse (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))
  · exact .pure (.orFalse (leftCost := 1) (rightCost := 1) (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))
  · simp [elaborateLocalComputation?, short, ref, elaborateLocalExpression?, resolveLocalExpression?, names, LocalNameTable.lookup?, context,
      Resolved.Expr.lower?, Resolved.LocalScope.index?, Resolved.LocalScope.ids, Resolved.LocalScope.values,
      fid, xid, gid, owner]
    intro a; change ¬ (none : Option Core.Ty) = some a; simp
  · exact .pure (.andTrue (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))
  · exact .pure (.andTrue (leftCost := 1) (rightCost := 1) (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))
  · simp [elaborateLocalComputation?, short, ref, elaborateLocalExpression?, resolveLocalExpression?, names, LocalNameTable.lookup?, context,
      Resolved.Expr.lower?, Resolved.LocalScope.index?, Resolved.LocalScope.ids, Resolved.LocalScope.values,
      fid, xid, gid, owner]
    intro a; change ¬ (none : Option Core.Ty) = some a; simp

private def readerEnv : Resolved.Environment :=
  [(xid, .unit), (fid, .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]), (gid, .unit), (fid, .unit)]
theorem a_checked_word_result_does_not_validate_the_actual_store :
    elaborateLocalComputation? names (context .unit .word) (source true span) = some (core true, .word) ∧
    Core.EnvironmentHasTypes readerEnv.values (context .unit .word).values ∧
    LocalComputationEvaluatesWithCost names readerEnv [.bool true] (source true span) (.bool true) [.bool true] 8 ∧
    Core.runStateful 8 (.initial (core true) readerEnv.values [.bool true]) = .done (.bool true) [.bool true] ∧
    ¬ Core.ValueHasType (.bool true) .word ∧
    Core.runStateful 7 (.initial (core true) readerEnv.values []) =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ := by
  refine ⟨elaborateLocalComputation?_iff.mpr (provenance true .unit .word span),
    .cons .unit (.cons (.closure (.cons .cellRef .nil) (.loadCell (.var rfl))) (.cons .unit (.cons .unit .nil))), ?_, rfl, ?_, rfl⟩
  · exact .application (.call (functionCost := 1) (argumentCost := 1) (bodyCost := 3)
      (.identifier .head (.tail (by decide) .head)) (.identifier (.tail (by decide) .head) .head)
      (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))
  · intro typed; cases typed

theorem application_effects_do_not_inherit_pure_store_preservation (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .unit), (fid, .closure .unit (.cell .unit) (.newCell .unit (.var 0)) []), (gid, .unit), (fid, .unit)]
    LocalComputationEvaluatesWithCost names env store (source true span) (.cellRef .unit store.length) (store ++ [.unit]) 8 ∧
    Core.Steps 8 (.initial (core true) env.values store) (.final (.cellRef .unit store.length) (store ++ [.unit])) ∧
    store ++ [Core.Value.unit] ≠ store := by
  dsimp only
  have actual : LocalComputationEvaluatesWithCost names
      [(xid, .unit), (fid, .closure .unit (.cell .unit) (.newCell .unit (.var 0)) []), (gid, .unit), (fid, .unit)]
      store (source true span) (.cellRef .unit store.length) (store ++ [.unit]) 8 :=
    .application (.call (functionCost := 1) (argumentCost := 1) (bodyCost := 3)
      (.identifier .head (.tail (by decide) .head)) (.identifier (.tail (by decide) .head) .head)
      (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))))
  refine ⟨actual, (actual.toStepsWithContinuation (provenance true .unit (.cell .unit) span) rfl []), ?_⟩
  intro same
  have impossible := congrArg List.length same
  simp at impossible

theorem pending_frames_and_delayed_captures_supply_no_source_only_bound (bound : Nat) (store : Core.Store) :
    bound < cost true bound ∧
    Core.Steps (cost true bound) ⟨.eval (core true) (environment bound .unit .unit).values, [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ :=
  ⟨by simp [cost]; omega, manual true bound .unit .unit store _, rfl⟩

private def bodyInputs : LocalTypeInputs :=
  ⟨[⟨"x", xid, .word⟩, ⟨"f", fid, .function .word .word⟩], by decide⟩
theorem accepting_the_call_leaf_does_not_integrate_a_call_initializer :
    elaborateLocalComputation? bodyInputs.names bodyInputs.context (source true span) = some (core true, .word) ∧
    elaborateTypedLetReturnTree? [] owner bodyInputs
      ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some (source true span))⟩,
        ⟨span, .returnStmt (some ⟨span, .binary (ref span "r") ⟨span, .add⟩ ⟨span, .literal ⟨span, .decimal "1"⟩⟩⟩)⟩]⟩ = none := by
  refine ⟨elaborateLocalComputation?_iff.mpr ?_, ?_⟩
  · exact .application (.call (.identifier (.tail (by decide) .head)) (.var (.tail (by decide) .head))
      (.var (.tail (by decide) .head)) (.identifier .head) (.var .head) (.var .head))
  · simp [elaborateTypedLetReturnTree?, source, bodyInputs, LocalTypeInputs.names, elaborateLocalExpression?, resolveLocalExpression?]

end Tests.FrontendLocalComputation
end

section
-- leanmerge: from Solcore.Test.FrontendLocalComputationReturnTreeProperties
/-! Original mixed statements, independently indexed Core, and manual paths.
Static result types neither constrain actual captures nor validate actual stores. -/
set_option autoImplicit false
namespace Tests.FrontendLocalComputationReturnTree
open Solcore Solcore.Frontend

theorem syntactic_fragment_constructors_do_not_require_valid_indices (i j : Nat) :
    LocalComputationFragment (.ifE (.apply (.var i) (.var j))
      (.letE (.var i) (.apply (.var (j + 1)) (.var 0))) .unit) :=
  .ifE (.application .var .var) (.letE (.pure .var) (.application .var .var)) (.pure .unit)

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Mixed", by decide⟩], by decide⟩⟩, 251⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 7 }, 999⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x", xid, a⟩, ⟨"f", fid, .function a b⟩], by change [xid, fid].Nodup; decide⟩
private def names := (inputs .unit .unit).names
private def span : Syntax.SourceSpan := ⟨⟨.main, "mixed.sol"⟩, 251, 2⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def call (s : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .call (ref s "f") ⟨s, [ref s "x"]⟩⟩
private def statements (s : Syntax.SourceSpan) : Nat → List Syntax.Statement
  | 0 => [⟨s, .returnStmt (some (call s))⟩]
  | n + 1 => ⟨s, .expression (call s) true⟩ :: statements s n
private def source (s : Syntax.SourceSpan) (n : Nat) : Syntax.Block := ⟨s, statements s n⟩
private def core : Nat → Nat → Core.Expr
  | 0, index => .apply (.var (index + 1)) (.var index)
  | n + 1, index => .letE (.apply (.var (index + 1)) (.var index)) (core n (index + 1))
private theorem shifted (n index cutoff : Nat) (before : cutoff ≤ index) :
    (core n index).weakenAt cutoff = core n (index + 1) := by
  induction n generalizing index cutoff with
  | zero => simp [core, Core.Expr.weakenAt, before, show cutoff ≤ index + 1 by omega]
  | succ n ih => simp [core, Core.Expr.weakenAt, before, show cutoff ≤ index + 1 by omega,
      ih (index + 1) (cutoff + 1) (by omega)]
private theorem child (a b : Core.Ty) (s : Syntax.SourceSpan) :
    LocalComputationElaborates (inputs a b).names (inputs a b).context (call s) (core 0 0) b :=
  .application (.call (.identifier (.tail (by change "x" ≠ "f"; decide) .head)) (.var (.tail (by change xid ≠ fid; decide) .head))
    (.var (.tail (by change xid ≠ fid; decide) .head)) (.identifier .head) (.var .head) (.var .head))
private theorem provenance (n : Nat) (a b : Core.Ty) (s : Syntax.SourceSpan) :
    LocalComputationReturnTreeElaborates [] owner (inputs a b) (source s n) (core n 0) b := by
  induction n with
  | zero => exact .expression (child a b s)
  | succ n ih => simpa only [source, statements, shifted n 0 0 (by omega), core] using
      LocalComputationReturnTreeElaborates.discard (child a b s) ih
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def closure (m : Nat) (captured : Core.Value) := Core.Value.closure .unit .unit (delay m 1) [captured]
private def environment (m : Nat) (argument captured : Core.Value) : Resolved.Environment :=
  [(xid, argument), (fid, closure m captured)]
private def cost (n m : Nat) := (n + 1) * (3 * m + 6) + 2 * n
private theorem cost_step (n m : Nat) : cost (n + 1) m = (3 * m + 6) + cost n m + 2 := by
  simp only [cost, Nat.add_mul]; omega
private theorem delayedRaw (m index : Nat) (arg : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (found : (arg :: rest)[index]? = some value) :
    Core.Evaluates (arg :: rest) store (delay m index) value store := by
  induction m generalizing index rest with
  | zero => exact .var found
  | succ m ih => exact .letE (.var rfl) (ih (index + 1) (arg :: rest) (by simpa using found))
private theorem delayedPath (m index : Nat) (arg : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (k : List Core.Frame) (found : (arg :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (arg :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (arg :: rest) k (by simpa using found))))
private theorem childRaw (m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationEvaluates names (environment m arg cap) store (call span) cap store :=
  .application (.call (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
    (.identifier .head .head) (delayedRaw m 1 arg [cap] cap store rfl))
private theorem childCost (m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationEvaluatesWithCost names (environment m arg cap) store (call span) cap store (3 * m + 6) := by
  have count : 3 * m + 6 = 1 + 1 + (3 * m + 1) + 3 := by omega
  rw [count]; exact .application (.call (.identifier (.tail (by decide) .head) (.tail (by decide) .head))
    (.identifier .head .head) (delayedPath m 1 arg [cap] cap store [] rfl))
private theorem raw (n m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationReturnTreeEvaluates owner names (environment m arg cap) store (source span n) cap store := by
  induction n with
  | zero => exact .expression (childRaw m arg cap store)
  | succ n ih => exact .discard (childRaw m arg cap store) ih
private theorem counted (n m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store (source span n) cap store (cost n m) := by
  induction n with
  | zero => simpa only [cost, Nat.zero_add, Nat.one_mul, Nat.mul_zero, Nat.add_zero, source, statements] using
      LocalComputationReturnTreeEvaluatesWithCost.expression (childCost m arg cap store) (owner := owner)
  | succ n ih => rw [cost_step]; exact .discard (childCost m arg cap store) ih
private theorem callManual (m : Nat) (arg cap : Core.Value) (kept : Core.Environment) (store : Core.Store) (frames : List Core.Frame) :
    Core.Steps (3 * m + 6) ⟨.eval (core 0 kept.length) (kept ++ [arg, closure m cap]), frames, store⟩ ⟨.ret cap, frames, store⟩ := by
    have path := CostStepComposition.apply (.cons (.var (by simp [closure])) .refl) (.cons (.var (by simp)) .refl)
      (delayedPath m 1 arg [cap] cap store [] rfl) (function := .var (kept.length + 1))
      (argument := .var kept.length) (environment := kept ++ [arg, closure m cap])
      (parameterType := .unit) (resultType := .unit) (continuation := frames)
    have count : 0 + 1 + (0 + 1) + (3 * m + 1) + 3 = 3 * m + 6 := by omega
    exact count ▸ path
private theorem manual (n m : Nat) (arg cap : Core.Value) (kept : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost n m) ⟨.eval (core n kept.length) (kept ++ [arg, closure m cap]), k, store⟩ ⟨.ret cap, k, store⟩ := by
  induction n generalizing kept k with
  | zero => simpa [cost] using callManual m arg cap kept store k
  | succ n ih =>
      rw [cost_step]
      exact CostStepComposition.letE (callManual m arg cap kept store _) (ih (cap :: kept) k)

theorem original_spans_and_arbitrary_static_types_keep_exact_core (n : Nat) (a b : Core.Ty) (s : Syntax.SourceSpan) :
    elaborateLocalComputationReturnTree? [] owner (inputs a b) (source s n) = some (core n 0, b) ∧
    LocalComputationReturnTreeHasType [] owner (inputs a b) (source s n) b ∧
    Core.HasType (inputs a b).context.values (core n 0) b ∧
    LocalComputationFragment (core 0 0) ∧ LocalComputationFragment ((core n 0).weakenAt n) :=
  ⟨elaborateLocalComputationReturnTree?_iff.mpr (provenance n a b s),
    localComputationReturnTreeHasType_iff_elaborates.mpr ⟨_, provenance n a b s⟩,
    (provenance n a b s).core_hasType, (child a b s).core_fragment, (provenance n a b s).core_fragment.weakenAt n⟩

theorem independent_paths_retain_captures_and_pending_frames (n m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationReturnTreeEvaluates owner names (environment m arg cap) store (source span n) cap store ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store (source span n) cap store (cost n m) ∧
    ∀ kept k, Core.Steps (cost n m) ⟨.eval (core n kept.length) (kept ++ [arg, closure m cap]), k, store⟩ ⟨.ret cap, k, store⟩ :=
  ⟨raw n m arg cap store, counted n m arg cap store, fun kept k => manual n m arg cap kept store k⟩

theorem raw_existence_and_exact_cost_do_not_type_actual_values (n m : Nat) (arg cap other : Core.Value)
    (store finalStore : Core.Store) (otherCost : Nat)
    (candidate : LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store (source span n) other finalStore otherCost) :
    other = cap ∧ finalStore = store ∧ otherCost = cost n m ∧
    LocalComputationReturnTreeEvaluates owner names (environment m arg cap) store (source span n) other finalStore ∧
    ∃ c, LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store (source span n) cap store c := by
  obtain ⟨v, s, c⟩ := candidate.deterministic (counted n m arg cap store)
  exact ⟨v, s, c, localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨_, candidate⟩,
    localComputationReturnTreeEvaluates_iff_exists_cost.mp (raw n m arg cap store)⟩

theorem ordered_ids_suffice_for_all_three_dynamic_bridges (n m : Nat) (a b : Core.Ty)
    (arg cap : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Evaluates (environment m arg cap).values store (core n 0) cap store ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store (source span n) cap store (cost n m) ∧
    Core.Steps (cost n m) ⟨.eval (core n 0) (environment m arg cap).values, k, store⟩ ⟨.ret cap, k, store⟩ :=
  ⟨((provenance n a b span).evaluates_iff rfl).mp (raw n m arg cap store),
    ((provenance n a b span).evaluatesWithCost_iff_steps rfl).mpr (manual n m arg cap [] store []),
    (counted n m arg cap store).toStepsWithContinuation (inputs := inputs a b) (provenance n a b span) rfl k⟩

theorem insertion_keeps_the_independent_cost_and_literal_answer (n m : Nat) (arg cap inserted : Core.Value)
    (leading suffix : Core.Environment) (store : Core.Store) (split : leading ++ suffix = (environment m arg cap).values) :
    Core.Evaluates (leading ++ inserted :: suffix) store ((core n 0).weakenAt leading.length) cap store ∧
    ∃ c, c = cost n m ∧ ∀ k,
      Core.Steps c ⟨.eval (core n 0) (leading ++ suffix), k, store⟩ ⟨.ret cap, k, store⟩ ∧
      Core.Steps c ⟨.eval ((core n 0).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret cap, k, store⟩ := by
  have fragment := (provenance n .unit .unit span).core_fragment
  have fixed : Core.Steps (cost n m) (.initial (core n 0) (environment m arg cap).values store) (.final cap store) :=
    manual n m arg cap [] store []
  have evaluation := split ▸ Core.steps_from_initial_sound fixed
  have added := (fragment.evaluates_insert_iff leading suffix inserted).mpr evaluation
  obtain ⟨c, paths⟩ := fragment.insertion_paths leading suffix inserted ((fragment.evaluates_insert_iff leading suffix inserted).mp added)
  exact ⟨added, c, ((paths []).1.final_unique (split ▸ fixed)).1, paths⟩

private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def mixed : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "r"⟩ (some annotation) (some (call span))⟩,
   ⟨span, .letDecl ⟨span, "s"⟩ none (some (ref span "r"))⟩,
   ⟨span, .expression (ref span "s") true⟩, ⟨span, .returnStmt (some (ref span "s"))⟩]⟩
private def mixedCore : Core.Expr := .letE (core 0 0) (.letE (.var 0) (.letE (.var 0) (.var 1)))
private theorem mixedElab (a b : Core.Ty) :
    LocalComputationReturnTreeElaborates [(["Payload"], b)] owner (inputs a b) mixed mixedCore b := by
  have shift : (Core.Expr.var 0).weakenAt 0 = .var 1 := by simp [Core.Expr.weakenAt]
  simp only [mixed, mixedCore, ← shift]
  refine .binding (show StructuralTypeDenotes [(["Payload"], b)] annotation b from .named .head)
    (by change "r" ∉ ["x", "f"]; decide) (child a b span) ?_
  refine .inferred (inferredType := b) (by change "s" ∉ ["r", "x", "f"]; decide)
    (.pure (.identifier .head) (.var .head) (.var .head)) ?_
  exact .discard (.pure (.identifier .head) (.var .head) (.var .head))
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
theorem named_and_inferred_bindings_do_not_become_discarded_source_names (a b : Core.Ty)
    (m : Nat) (arg cap : Core.Value) (store : Core.Store) :
    LocalComputationReturnTreeElaborates [(["Payload"], b)] owner (inputs a b) mixed mixedCore b ∧
    LocalComputationReturnTreeHasType [(["Payload"], b)] owner (inputs a b) mixed b ∧
    LocalComputationReturnTreeEvaluates owner names (environment m arg cap) store mixed cap store ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment m arg cap) store mixed cap store (3 * m + 15) := by
  refine ⟨mixedElab a b, .binding (.named .head) (by change "r" ∉ ["x", "f"]; decide)
    (.application (.call (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (by change xid ≠ fid; decide) .head)) (.identifier .head .head)))
    (.inferred (by change "s" ∉ ["r", "x", "f"]; decide) (.pure (.identifier .head .head))
      (.discard (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))),
    .binding (childRaw m arg cap store) (.inferred (.pure (.identifier .head .head))
      (.discard (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head))))), ?_⟩
  have count : 3 * m + 15 = (3 * m + 6) + (1 + (1 + 1 + 2) + 2) + 2 := by omega
  rw [count]; exact .binding (initializerCost := 3 * m + 6) (tailCost := 7) (childCost m arg cap store) (.inferred (.pure (.identifier .head .head))
    (.discard (.pure (.identifier .head .head)) (.expression (.pure (.identifier .head .head)))))

private def bare : Syntax.Block := ⟨span, [⟨span, .returnStmt none⟩]⟩
private def branches : Syntax.Block := ⟨span, [⟨span, .ifThen (ref span "x")
  ⟨span, [⟨span, .block (statements span 0)⟩]⟩ (some bare)⟩]⟩
theorem both_selected_branches_and_old_bare_provenance_are_independent (flag : Bool) (m : Nat) (store : Core.Store) :
    LocalComputationReturnTreeHasType [] owner (inputs .bool .unit) branches .unit ∧
    LocalComputationReturnTreeElaborates [] owner (inputs .bool .unit) branches (.ifE (.var 0) (core 0 0) .unit) .unit ∧
    LocalComputationReturnTreeEvaluates owner names (environment m (.bool flag) .unit) store branches .unit store ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment m (.bool flag) .unit) store branches .unit store (if flag then 3 * m + 9 else 4) ∧
    LocalComputationReturnTreeElaborates [] owner (inputs .bool .unit) bare .unit .unit := by
  refine ⟨.conditional (.pure (.identifier .head .head)) (.block (.expression
    (.application (.call (.identifier (.tail (by decide) .head) (.tail (by decide) .head)) (.identifier .head .head))))) .bare,
    .conditional (.pure (.identifier .head) (.var .head) (.var .head)) (.block (.expression (child .bool .unit span))) .bare,
    ?_, ?_, (show TypedLetReturnTreeElaborates [] owner (inputs .bool .unit) bare .unit .unit from .single .bare).toLocalComputationReturnTree⟩
  · cases flag
    · exact .ifFalse (.pure (.identifier .head .head)) .bare
    · exact .ifTrue (.pure (.identifier .head .head)) (.block (.expression (childRaw m (.bool true) .unit store)))
  · cases flag
    · exact .ifFalse (conditionCost := 1) (branchCost := 1) (.pure (.identifier .head .head)) .bare
    · have count : 3 * m + 9 = 1 + (3 * m + 6) + 2 := by omega
      simp only [↓reduceIte]; rw [count]
      exact .ifTrue (.pure (.identifier .head .head)) (.block (.expression (childCost m (.bool true) .unit store)))

private def skipped : Syntax.Block := ⟨span, [⟨span, .ifThen (ref span "x") (source span 0)
  (some ⟨span, [⟨span, .returnStmt (some (ref span "missing"))⟩]⟩)⟩]⟩
theorem unknown_unselected_return_prevents_whole_elaboration (store : Core.Store) :
    LocalComputationReturnTreeEvaluatesWithCost owner names (environment 0 (.bool true) .unit) store skipped .unit store 9 ∧
    elaborateLocalComputationReturnTree? [] owner (inputs .bool .unit) skipped = none := by
  refine ⟨.ifTrue (conditionCost := 1) (branchCost := 6) (.pure (.identifier .head .head))
    (.expression (childCost 0 (.bool true) .unit store)), ?_⟩
  have accepted := elaborateLocalComputationReturnTree?_iff.mpr (provenance 0 .bool .unit span)
  simp only [skipped, elaborateLocalComputationReturnTree?, accepted]
  simp [elaborateLocalComputation?, elaborateLocalExpression?, resolveLocalExpression?, inputs, ref,
    LocalTypeInputs.names, LocalTypeInputs.context, LocalNameTable.lookup?, Resolved.Expr.lower?,
    Resolved.LocalScope.index?, Resolved.LocalScope.ids, Resolved.LocalScope.values]

private def reader : Resolved.Environment := [(xid, .unit), (fid, .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0])]
theorem static_word_return_does_not_validate_the_actual_cell :
    LocalComputationReturnTreeElaborates [] owner (inputs .unit .word) (source span 0) (core 0 0) .word ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names reader [.bool true] (source span 0) (.bool true) [.bool true] 8 ∧
    Core.runStateful 8 (.initial (core 0 0) reader.values [.bool true]) = .done (.bool true) [.bool true] ∧
    Core.runStateful 7 (.initial (core 0 0) reader.values []) =
      .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩ :=
  ⟨provenance 0 .unit .word span, .expression (.application (.call (functionCost := 1) (argumentCost := 1) (bodyCost := 3)
    (.identifier (.tail (by decide) .head) (.tail (by decide) .head)) (.identifier .head .head)
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))), rfl, rfl⟩

private def allocatedThenReturn : Syntax.Block := ⟨span,
  [⟨span, .expression (call span) true⟩, ⟨span, .returnStmt (some (ref span "x"))⟩]⟩
theorem discarded_allocation_is_visible_to_the_original_tail_store (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .unit), (fid, .closure .unit (.cell .unit) (.newCell .unit (.var 0)) [])]
    LocalComputationReturnTreeElaborates [] owner (inputs .unit (.cell .unit)) allocatedThenReturn (.letE (core 0 0) (.var 1)) .unit ∧
    LocalComputationReturnTreeEvaluatesWithCost owner names env store allocatedThenReturn .unit (store ++ [.unit]) 11 ∧
    store ++ [Core.Value.unit] ≠ store := by
  have tail : LocalComputationReturnTreeElaborates [] owner (inputs .unit (.cell .unit))
      ⟨span, [⟨span, .returnStmt (some (ref span "x"))⟩]⟩ (.var 0) .unit :=
    .expression (.pure (.identifier .head) (.var .head) (.var .head))
  refine ⟨?_,
    .discard (expressionCost := 8) (tailCost := 1) (.application (.call (functionCost := 1) (argumentCost := 1) (bodyCost := 3)
      (.identifier (.tail (by decide) .head) (.tail (by decide) .head)) (.identifier .head .head)
      (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))))) (.expression (.pure (.identifier .head .head))), ?_⟩
  · simpa [allocatedThenReturn, Core.Expr.weakenAt] using
      LocalComputationReturnTreeElaborates.discard (child .unit (.cell .unit) span) tail (statementSpan := span)
  · intro same; have lengths := congrArg List.length same; simp at lengths

theorem source_only_cost_and_arbitrary_pending_frames_are_not_safety_guarantees (bound : Nat) (store : Core.Store) :
    bound < cost 0 bound ∧
    Core.Steps (cost 0 bound) ⟨.eval (core 0 0) (environment bound .unit .unit).values, [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ :=
  ⟨by simp [cost]; omega, manual 0 bound .unit .unit [] store _, rfl⟩

theorem nominal_annotation_meaning_does_not_provide_an_actual_capture (nominal : Core.DataTypeId) :
    LocalComputationReturnTreeElaborates [(["Payload"], .namedData nominal)] owner
      (inputs .unit (.namedData nominal)) mixed mixedCore (.namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨mixedElab .unit (.namedData nominal), ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem genuine_hidden_slot_checkpoint_keeps_all_resumed_outcomes (arg cap : Core.Value) (store : Core.Store) :
    let start := Core.State.initial (core 1 0) (environment 0 arg cap).values store
    let checkpoint : Core.State := ⟨.eval (core 0 1) [cap, arg, closure 0 cap], [], store⟩
    Core.runStateful 8 start = .outOfFuel checkpoint ∧
    Core.Steps 6 checkpoint (.final cap store) ∧
    (∀ fuel, Core.runStateful fuel start = .done cap store ↔ 14 ≤ fuel) ∧
    (∀ additional, Core.runStateful additional checkpoint = Core.runStateful (8 + additional) start) := by
  have exhausted : Core.runStateful 8 (.initial (core 1 0) (environment 0 arg cap).values store) =
      .outOfFuel ⟨.eval (core 0 1) [cap, arg, closure 0 cap], [], store⟩ := rfl
  have path := manual 1 0 arg cap [] store []
  exact ⟨exhausted, (path.residual_of_outOfFuel exhausted).2,
    fun _ => path.runStateful_done_iff, Core.runStateful_resume exhausted⟩

end Tests.FrontendLocalComputationReturnTree
end

section
-- leanmerge: from Solcore.Test.FrontendLocalFunctionApplicationProperties
/-! Original single arguments and independent child provenance determine the
application. Static contexts are separate from actual values and store safety. -/
set_option autoImplicit false
namespace Tests.FrontendLocalFunctionApplication
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Application", by decide⟩], by decide⟩⟩, 4⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 91 }
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨foreign, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 3⟩
private def cid : Resolved.LocalId := ⟨foreign, 2⟩
private def names : LocalNameTable := [("f", fid), ("f", gid), ("x", aid), ("c", cid)]
private def context (a b : Core.Ty) : Resolved.Context :=
  [(aid, a), (fid, .function a b), (gid, .function a b), (cid, .bool), (fid, .word)]
private structure Ranges where
  root : Syntax.SourceSpan
  arguments : Syntax.SourceSpan
  callee : Syntax.SourceSpan
  calleeName : Syntax.SourceSpan
  argument : Syntax.SourceSpan
  argumentName : Syntax.SourceSpan
private def badSpan : Syntax.SourceSpan := ⟨⟨.main, "local-call.sol"⟩, 37, 2⟩
private def ranges : Ranges := ⟨badSpan, badSpan, badSpan, badSpan, badSpan, badSpan⟩
private def ref (span nameSpan : Syntax.SourceSpan) (name : String) : Syntax.Expr :=
  ⟨span, .identifier ⟨nameSpan, name⟩⟩
private def groups : List Syntax.SourceSpan → Syntax.Expr → Syntax.Expr
  | [], source => source
  | span :: rest, source => ⟨span, .group (groups rest source)⟩
private theorem groupResolution {table : LocalNameTable} {source : Syntax.Expr} {resolved : Resolved.Expr}
    (evidence : ResolvesLocalExpression table source resolved) (spans : List Syntax.SourceSpan) :
    ResolvesLocalExpression table (groups spans source) resolved := by
  induction spans with
  | nil => exact evidence
  | cons _ _ ih => exact .group ih
private theorem groupTyping {table : LocalNameTable} {ctx : Resolved.Context} {source : Syntax.Expr} {type : Core.Ty}
    (evidence : LocalExpressionHasType table ctx source type) (spans : List Syntax.SourceSpan) :
    LocalExpressionHasType table ctx (groups spans source) type := by
  induction spans with
  | nil => exact evidence
  | cons _ _ ih => exact .group ih
private def source (r : Ranges) (fs xs : List Syntax.SourceSpan) : Syntax.Expr :=
  ⟨r.root, .call (groups fs (ref r.callee r.calleeName "f"))
    ⟨r.arguments, [groups xs (ref r.argument r.argumentName "x")]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private theorem exactCall (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source r fs xs) core b :=
  .call (parameterType := a)
    (groupResolution (table := names) (source := ref r.callee r.calleeName "f") (.identifier .head) fs)
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (groupResolution (table := names) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head))) xs) (.var .head) (.var .head)
private theorem typedCall (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationHasType names (context a b) (source r fs xs) b :=
  .call (parameterType := a)
    (groupTyping (table := names) (ctx := context a b) (source := ref r.callee r.calleeName "f")
      (.identifier .head (.tail (by change aid ≠ fid; decide) .head)) fs)
    (groupTyping (table := names) (ctx := context a b) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head)) .head) xs)

theorem arbitrary_groups_spans_and_types_retain_exact_original_children
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (definitions : Core.DataEnvironment) :
    LocalFunctionApplicationElaborates names (context a b) (source r fs xs) core b ∧
    LocalFunctionApplicationHasType names (context a b) (source r fs xs) b ∧
    elaborateLocalFunctionApplication? names (context a b) (source r fs xs) = some (core, b) ∧
    Core.HasType (Resolved.LocalScope.values (context a b)) core b definitions :=
  ⟨exactCall a b r fs xs, typedCall a b r fs xs, (exactCall a b r fs xs).complete,
    .apply (.var rfl) (.var rfl)⟩

theorem sparse_and_duplicate_rows_are_first_match_not_freshness_preconditions (a b : Core.Ty) :
    ¬ (names.map Prod.fst).Nodup ∧ ¬ (Resolved.LocalScope.ids (context a b)).Nodup ∧
    names.lookup? "f" = some fid ∧ (context a b).lookup? fid = some (.function a b) ∧
    elaborateLocalFunctionApplication? names (context a b) (source ranges [] []) = some (core, b) :=
  ⟨by decide, by simp [context, Resolved.LocalScope.ids, fid, aid, gid, cid, owner, foreign], rfl, rfl,
    (exactCall a b ranges [] []).complete⟩

theorem same_typed_other_function_is_not_the_original_application
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (definitions : Core.DataEnvironment) :
    Core.HasType (Resolved.LocalScope.values (context a b)) (.apply (.var 2) (.var 0)) b definitions ∧
    ¬ LocalFunctionApplicationElaborates names (context a b) (source r fs xs) (.apply (.var 2) (.var 0)) b := by
  refine ⟨.apply (.var rfl) (.var rfl), ?_⟩
  intro wrong
  have same := (exactCall a b r fs xs).result_unique wrong
  cases same.1

theorem all_static_correspondences_keep_the_candidate_core_and_type
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) (candidate : Core.Expr) (result : Core.Ty) :
    (elaborateLocalFunctionApplication? names (context a b) (source r fs xs) = some (candidate, result) ↔
      candidate = core ∧ result = b) ∧
    (LocalFunctionApplicationHasType names (context a b) (source r fs xs) result ↔ result = b) ∧
    Core.HasType (Resolved.LocalScope.values (context a b)) core b ∧
    Core.infer? (Resolved.LocalScope.values (context a b)) core = some b := by
  have original := exactCall a b r fs xs
  refine ⟨⟨fun accepted => (elaborateLocalFunctionApplication?_sound accepted).result_unique original,
    ?_⟩, ⟨fun typing => typing.type_unique original.hasType, ?_⟩,
    elaborateLocalFunctionApplication?_core_hasType original.complete, Core.infer_complete original.core_hasType⟩
  · rintro ⟨rfl, rfl⟩
    exact elaborateLocalFunctionApplication?_iff.mpr original
  · intro same; cases same
    exact localFunctionApplicationHasType_iff_elaborates.mpr (typedCall a b r fs xs).elaborates_exact

theorem original_child_decomposition_keeps_order_and_the_unique_argument
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    elaborateLocalExpression? names (context a b) (groups fs (ref r.callee r.calleeName "f")) =
      some (.var 1, .function a b) ∧
    elaborateLocalExpression? names (context a b) (groups xs (ref r.argument r.argumentName "x")) = some (.var 0, a) := by
  obtain ⟨functionCore, argumentCore, parameterType, functionChecked, argumentChecked, shape⟩ :=
    elaborateLocalFunctionApplication?_children.mp (exactCall a b r fs xs).complete
  have indices := Core.Expr.apply.inj shape
  cases indices.1; cases indices.2
  have actualArgument := elaborateLocalExpression?_complete (table := names) (context := context a b)
    (groupResolution (table := names) (source := ref r.argument r.argumentName "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) (.tail (by change "f" ≠ "x"; decide) .head))) xs)
    (.var (.head : Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids (context a b)) aid 0))
    (.var (.head : Resolved.LocalScope.Lookup (context a b) aid a))
  have same := Prod.mk.inj (Option.some.inj (argumentChecked.symm.trans actualArgument))
  cases same.2
  exact ⟨functionChecked, argumentChecked⟩

theorem nominal_static_types_do_not_supply_runtime_arguments (a b : Core.DataTypeId) :
    elaborateLocalFunctionApplication? names (context (.namedData a) (.namedData b)) (source ranges [] []) =
      some (core, .namedData b) ∧
    Core.ValueHasType (.closure (.namedData a) (.namedData a) (.var 0) [])
      (.function (.namedData a) (.namedData a)) ∧ ¬ ∃ value, Core.ValueHasType value (.namedData a) := by
  refine ⟨(exactCall _ _ ranges [] []).complete, .closure .nil (.var rfl), ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def unit : Syntax.Expr := ⟨badSpan, .tuple ⟨badSpan, []⟩⟩
private def pair : Syntax.Expr := ⟨badSpan, .tuple ⟨badSpan, [unit, unit]⟩⟩
private def call (args : List Syntax.Expr) : Syntax.Expr :=
  ⟨badSpan, .call (ref badSpan badSpan "f") ⟨badSpan, args⟩⟩
private theorem unitCall (b : Core.Ty) :
    LocalFunctionApplicationElaborates names (context .unit b) (call [unit]) (.apply (.var 1) .unit) b :=
  .call (.identifier .head) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head)) .unit .unit .unit
private theorem pairCall (b : Core.Ty) : LocalFunctionApplicationElaborates names (context (.product .unit .unit) b)
    (call [pair]) (.apply (.var 1) (.pair .unit .unit)) b :=
  .call (.identifier .head) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
    (.pair .unit .unit) (.pair .unit .unit) (.pair .unit .unit)
theorem a_unit_or_product_argument_is_one_written_argument (b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context .unit b) (call [unit]) = some (.apply (.var 1) .unit, b) ∧
    elaborateLocalFunctionApplication? names (context (.product .unit .unit) b) (call [pair]) =
      some (.apply (.var 1) (.pair .unit .unit), b) ∧
    elaborateLocalFunctionApplication? names (context .unit b) (call []) = none ∧
    elaborateLocalFunctionApplication? names (context (.product .unit .unit) b) (call [unit, unit]) = none :=
  ⟨(unitCall b).complete, (pairCall b).complete, rfl, rfl⟩

theorem zero_arguments_cannot_acquire_an_implicit_unit (b : Core.Ty) :
    ¬ ∃ type, LocalFunctionApplicationHasType names (context .unit b) (call []) type :=
  elaborateLocalFunctionApplication?_eq_none_iff.mp rfl

theorem old_pure_children_do_not_recursively_adopt_applications (a b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context a b) ⟨badSpan, .group (source ranges [] [])⟩ = none ∧
    elaborateLocalFunctionApplication? names (context a b) (call [source ranges [] []]) = none ∧
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (source ranges [] []) ⟨badSpan, [unit]⟩⟩ = none := by
  simp [elaborateLocalFunctionApplication?, call, source, groups, elaborateLocalExpression?, resolveLocalExpression?]

theorem exact_application_is_outside_the_old_pure_and_body_profiles
    (a b : Core.Ty) (r : Ranges) (fs xs : List Syntax.SourceSpan) :
    elaborateLocalExpression? names (context a b) (source r fs xs) = none ∧
    elaborateReturnBody? names (context a b) ⟨r.root, [⟨r.arguments, .returnStmt (some (source r fs xs))⟩]⟩ = none ∧
    ¬ Core.Expr.LocalFragment core := ⟨by simp [source, elaborateLocalExpression?, resolveLocalExpression?],
      by simp [elaborateReturnBody?, source, elaborateLocalExpression?, resolveLocalExpression?],
      by intro fragment; cases fragment⟩

private def conditional (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨badSpan, .conditional (ref badSpan badSpan "c") badSpan left badSpan right⟩
private def fn : Syntax.Expr := ref badSpan badSpan "f"
private def arg : Syntax.Expr := ref badSpan badSpan "x"
private def missing : Syntax.Expr := ref badSpan badSpan "missing"
private theorem conditionalCall (a b : Core.Ty) : LocalFunctionApplicationElaborates names (context a b)
    ⟨badSpan, .call (conditional fn fn) ⟨badSpan, [conditional arg arg]⟩⟩
    (.apply (.ifE (.var 3) (.var 1) (.var 1)) (.ifE (.var 3) (.var 0) (.var 0))) b :=
  .call (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier .head) (.identifier .head))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head))))
      (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head)))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head))))
      (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head)))
    (.conditional (.identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))))
      (.identifier (.tail (by decide) (.tail (by decide) .head))) (.identifier (.tail (by decide) (.tail (by decide) .head))))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head)))) (.var .head) (.var .head))
    (.ifE (.var (.tail (by change aid ≠ cid; decide) (.tail (by change fid ≠ cid; decide) (.tail (by change gid ≠ cid; decide) .head)))) (.var .head) (.var .head))
theorem both_conditional_children_are_checked_in_the_original_scope (a b : Core.Ty) :
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (conditional fn fn) ⟨badSpan, [conditional arg arg]⟩⟩ =
      some (.apply (.ifE (.var 3) (.var 1) (.var 1)) (.ifE (.var 3) (.var 0) (.var 0)), b) ∧
    elaborateLocalFunctionApplication? names (context a b) (call [conditional arg missing]) = none ∧
    elaborateLocalFunctionApplication? names (context a b)
      ⟨badSpan, .call (conditional fn missing) ⟨badSpan, [arg]⟩⟩ = none := by
  refine ⟨(conditionalCall a b).complete, ?_, ?_⟩ <;>
    simp [elaborateLocalFunctionApplication?, call, conditional, fn, arg, missing, ref, elaborateLocalExpression?,
      resolveLocalExpression?, LocalNameTable.lookup?, names]

theorem nonfunction_wrong_argument_and_mixed_conditional_types_do_not_coerce :
    elaborateLocalFunctionApplication? names [(fid, .bool), (aid, .unit)] (source ranges [] []) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool) (call [unit]) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool) (call [conditional arg unit]) = none ∧
    elaborateLocalFunctionApplication? names (context .word .bool)
      ⟨badSpan, .call (conditional fn arg) ⟨badSpan, [arg]⟩⟩ = none := by
  simp only [elaborateLocalFunctionApplication?, source, groups, call, conditional, fn, arg, unit, ref,
    elaborateLocalExpression?, resolveLocalExpression?, names, LocalNameTable.lookup?]
  exact ⟨rfl, rfl, rfl, rfl⟩

private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) []
private theorem identityPath (type : Core.Ty) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval core [value, identity type], k, store⟩ ⟨.ret value, k, store⟩ :=
  .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
    (.cons .invokeClosure (.cons (.var rfl) .refl)))))
theorem actual_identity_paths_keep_their_continuation_without_claiming_source_evaluation
    (type : Core.Ty) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval core [value, identity type], k, store⟩ ⟨.ret value, k, store⟩ ∧
    Core.runStateful 6 (Core.State.initial core [value, identity type] store) = .done value store ∧
    Core.runStateful 3 (Core.State.initial core [value, identity type] store) =
      .outOfFuel ⟨.eval (.var 0) [value, identity type], [.applyClosure type type (.var 0) []], store⟩ :=
  ⟨identityPath type value store k, rfl, rfl⟩

private def reader : Core.Value := .closure (.cell .word) .word (.loadCell (.var 0)) []
private def readerEnvironment (location : Core.Location) : Core.Environment :=
  [.cellRef .word location, reader, reader, .bool false, .word .zero]
theorem structurally_typed_actual_values_do_not_prove_cells_allocated (location : Core.Location) :
    elaborateLocalFunctionApplication? names (context (.cell .word) .word) (source ranges [] []) = some (core, .word) ∧
    Core.EnvironmentHasTypes (readerEnvironment location) (Resolved.LocalScope.values (context (.cell .word) .word)) ∧
    Core.runStateful 7 (Core.State.initial core (readerEnvironment location) []) =
      .fault (.invalidCellLocation location) ⟨.ret (.cellRef .word location), [.loadCellApply], []⟩ :=
  ⟨(exactCall _ _ ranges [] []).complete,
    .cons .cellRef (.cons (.closure .nil (.loadCell (.var rfl)))
      (.cons (.closure .nil (.loadCell (.var rfl))) (.cons .bool (.cons .word .nil)))), rfl⟩

end Tests.FrontendLocalFunctionApplication
end

section
-- leanmerge: from Solcore.Test.FrontendLocalApplicationEvaluationProperties
/-! Independent original child evaluations and actual closure bodies fix values
and costs. Static types, ordered identities and pending frames are separate. -/
set_option autoImplicit false
namespace Tests.FrontendLocalApplicationEvaluation
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ActualCall", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 2⟩
private def names : LocalNameTable := [("f", fid), ("x", aid), ("f", gid)]
private def context (a b : Core.Ty) : Resolved.Context :=
  [(aid, a), (fid, .function a b), (gid, .function a b), (fid, .function a b)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "actual-call.sol"⟩, 31, 4⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def groups : List Syntax.SourceSpan → Syntax.Expr → Syntax.Expr
  | [], source => source
  | s :: rest, source => ⟨s, .group (groups rest source)⟩
private def source (s t : Syntax.SourceSpan) (fs xs : List Syntax.SourceSpan) : Syntax.Expr :=
  ⟨s, .call (groups fs (ref s "f")) ⟨t, [groups xs (ref t "x")]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def closure (a b : Core.Ty) (n : Nat) (captured : Core.Value) : Core.Value :=
  .closure a b (delay n 1) [captured]
private def environment (a b : Core.Ty) (n : Nat) (argument captured : Core.Value) : Resolved.Environment :=
  [(aid, argument), (fid, closure a b n captured), (gid, .unit), (fid, .unit)]
private theorem groupedResolution {table : LocalNameTable} {e : Syntax.Expr} {r : Resolved.Expr}
    (found : ResolvesLocalExpression table e r) (ss : List Syntax.SourceSpan) :
    ResolvesLocalExpression table (groups ss e) r := by
  induction ss with
  | nil => exact found
  | cons _ _ ih => exact .group ih
private theorem groupedRaw {table : LocalNameTable} {env : Resolved.Environment}
    {s f : Core.Store} {e : Syntax.Expr} {v : Core.Value}
    (found : LocalExpressionEvaluates table env s e v f) (ss : List Syntax.SourceSpan) :
    LocalExpressionEvaluates table env s (groups ss e) v f := by
  induction ss with
  | nil => exact found
  | cons _ _ ih => exact .group ih
private theorem groupedCost {table : LocalNameTable} {env : Resolved.Environment}
    {s f : Core.Store} {e : Syntax.Expr} {v : Core.Value} {cost : Nat}
    (found : LocalExpressionEvaluatesWithCost table env s e v f cost) (ss : List Syntax.SourceSpan) :
    LocalExpressionEvaluatesWithCost table env s (groups ss e) v f cost := by
  induction ss with
  | nil => exact found
  | cons _ _ ih => exact .group ih
private theorem bodyRaw (n index : Nat) (argument : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (found : (argument :: rest)[index]? = some value) :
    Core.Evaluates (argument :: rest) store (delay n index) value store := by
  induction n generalizing index rest with
  | zero => exact .var found
  | succ n ih => exact .letE (.var rfl) (ih (index + 1) (argument :: rest) (by simpa using found))
private theorem bodyPath (n index : Nat) (argument : Core.Value) (rest : Core.Environment)
    (value : Core.Value) (store : Core.Store) (k : List Core.Frame)
    (found : (argument :: rest)[index]? = some value) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n index) (argument :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have tail := ih (index + 1) (argument :: rest) k (by simpa using found)
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet tail))
private theorem elaborated (a b : Core.Ty) (s t : Syntax.SourceSpan) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (source s t fs xs) core b :=
  .call (parameterType := a)
    (groupedResolution (table := names) (e := ref s "f") (.identifier .head) fs)
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (groupedResolution (table := names) (e := ref t "x") (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) xs)
    (.var .head) (.var .head)
private theorem raw (a b : Core.Ty) (n : Nat) (argument captured : Core.Value) (store : Core.Store)
    (s t : Syntax.SourceSpan) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationEvaluates names (environment a b n argument captured) store (source s t fs xs) captured store :=
  .call (groupedRaw (table := names) (env := environment a b n argument captured) (e := ref s "f")
      (.identifier .head (.tail (by change aid ≠ fid; decide) .head)) fs)
    (groupedRaw (table := names) (env := environment a b n argument captured) (e := ref t "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head) xs)
    (bodyRaw n 1 argument [captured] captured store rfl)
private theorem counted (a b : Core.Ty) (n : Nat) (argument captured : Core.Value) (store : Core.Store)
    (s t : Syntax.SourceSpan) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationEvaluatesWithCost names (environment a b n argument captured) store
      (source s t fs xs) captured store (3 * n + 6) := by
  have evidence := LocalFunctionApplicationEvaluatesWithCost.call
    (span := s) (argumentsSpan := t) (body := delay n 1) (captured := [captured])
    (groupedCost (table := names) (env := environment a b n argument captured) (e := ref s "f")
      (.identifier .head (.tail (by change aid ≠ fid; decide) .head)) fs)
    (groupedCost (table := names) (env := environment a b n argument captured) (e := ref t "x")
      (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head) xs)
    (bodyPath n 1 argument [captured] captured store [] rfl)
  have sameCost : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact sameCost ▸ evidence
private theorem manualCall (a b : Core.Ty) (n : Nat) (argument captured : Core.Value)
    (store : Core.Store) (k : List Core.Frame) : Core.Steps (3 * n + 6)
      ⟨.eval core (environment a b n argument captured).values, k, store⟩ ⟨.ret captured, k, store⟩ := by
  have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (bodyPath n 1 argument [captured] captured store [] rfl)
    (function := .var 1) (argument := .var 0) (environment := (environment a b n argument captured).values)
    (parameterType := a) (resultType := b) (continuation := k)
  have sameCost : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact sameCost ▸ path

theorem arbitrary_actual_body_depth_and_groups_have_independent_exact_cost
    (a b : Core.Ty) (n : Nat) (argument captured : Core.Value) (store : Core.Store)
    (s t : Syntax.SourceSpan) (fs xs : List Syntax.SourceSpan) :
    LocalFunctionApplicationEvaluates names (environment a b n argument captured) store (source s t fs xs) captured store ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment a b n argument captured) store
      (source s t fs xs) captured store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment a b n argument captured).values, k, store⟩ ⟨.ret captured, k, store⟩ :=
  ⟨raw a b n argument captured store s t fs xs, counted a b n argument captured store s t fs xs,
    manualCall a b n argument captured store⟩

theorem cost_existence_erasure_and_uniqueness_fix_actual_capture_not_static_tags
    (a b : Core.Ty) (n : Nat) (argument captured other : Core.Value) (store finalStore : Core.Store) (cost : Nat)
    (candidate : LocalFunctionApplicationEvaluatesWithCost names (environment a b n argument captured)
      store (source span span [] []) other finalStore cost) :
    other = captured ∧ finalStore = store ∧ cost = 3 * n + 6 ∧ 0 < cost ∧
    LocalFunctionApplicationEvaluates names (environment a b n argument captured) store (source span span [] []) other finalStore ∧
    ∃ chosen, LocalFunctionApplicationEvaluatesWithCost names (environment a b n argument captured)
      store (source span span [] []) captured store chosen := by
  have actual := counted a b n argument captured store span span [] []
  obtain ⟨valueEq, storeEq, _⟩ := candidate.deterministic actual
  exact ⟨valueEq, storeEq, candidate.cost_unique actual, candidate.cost_pos, candidate.erase,
    (raw a b n argument captured store span span [] []).exists_cost⟩

theorem raw_cost_correspondence_is_nonvacuous_for_every_capture
    (a b : Core.Ty) (n : Nat) (argument captured other : Core.Value) (store finalStore : Core.Store)
    (candidate : LocalFunctionApplicationEvaluates names (environment a b n argument captured)
      store (source span span [] []) other finalStore) :
    other = captured ∧ finalStore = store ∧
    LocalFunctionApplicationEvaluates names (environment a b n argument captured) store (source span span [] []) captured store :=
  ⟨(candidate.deterministic (raw a b n argument captured store span span [] [])).1,
    (candidate.deterministic (raw a b n argument captured store span span [] [])).2,
    localFunctionApplicationEvaluates_iff_exists_cost.mpr ⟨_, counted a b n argument captured store span span [] []⟩⟩

theorem exact_checked_bridges_require_ids_but_not_actual_type_tags
    (staticA staticB actualA actualB : Core.Ty) (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    Core.Evaluates (environment actualA actualB n argument captured).values store core captured store ∧
    LocalFunctionApplicationEvaluates names (environment actualA actualB n argument captured) store (source span span [] []) captured store ∧
    Core.Steps (3 * n + 6) (Core.State.initial core (environment actualA actualB n argument captured).values store)
      (Core.State.final captured store) ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment actualA actualB n argument captured) store
      (source span span [] []) captured store (3 * n + 6) := by
  have provenance := elaborated staticA staticB span span [] []
  have evaluation := raw actualA actualB n argument captured store span span [] []
  have path := manualCall actualA actualB n argument captured store []
  exact ⟨(provenance.evaluates_iff rfl).mp evaluation,
    (elaborateLocalFunctionApplication?_evaluates_iff provenance.complete rfl).mpr (Core.steps_from_initial_sound path),
    (provenance.evaluatesWithCost_iff_steps rfl).mp (counted actualA actualB n argument captured store span span [] []),
    (elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps provenance.complete rfl).mpr path⟩

theorem one_actual_cost_precedes_all_continuations (a b : Core.Ty) (n : Nat)
    (argument captured : Core.Value) (store : Core.Store) :
    (∃ cost, ∀ k, Core.Steps cost ⟨.eval core (environment a b n argument captured).values, k, store⟩ ⟨.ret captured, k, store⟩) ∧
    (∀ k, Core.Steps (3 * n + 6) ⟨.eval core (environment a b n argument captured).values, k, store⟩ ⟨.ret captured, k, store⟩) :=
  ⟨((elaborated a b span span [] []).evaluates_iff_exists_uniform_steps rfl).mp (raw a b n argument captured store span span [] []),
    (counted a b n argument captured store span span [] []).toStepsWithContinuation (elaborated a b span span [] []) rfl⟩

private def checkpoint (a b : Core.Ty) (n : Nat) (argument captured : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (environment a b n argument captured).values, [.applyClosure a b (delay n 1) [captured]], store⟩
theorem genuine_argument_checkpoint_keeps_captures_and_exact_remaining_cost
    (a b : Core.Ty) (n fuel additional : Nat) (argument captured : Core.Value) (store : Core.Store) :
    (Core.runStateful fuel (Core.State.initial core (environment a b n argument captured).values store) = .done captured store ↔ 3 * n + 6 ≤ fuel) ∧
    Core.runStateful 3 (Core.State.initial core (environment a b n argument captured).values store) = .outOfFuel (checkpoint a b n argument captured store) ∧
    Core.Steps (3 * n + 3) (checkpoint a b n argument captured store) (Core.State.final captured store) ∧
    Core.runStateful additional (checkpoint a b n argument captured store) =
      Core.runStateful (3 + additional) (Core.State.initial core (environment a b n argument captured).values store) := by
  have path := (counted a b n argument captured store span span [] []).toSteps (elaborated a b span span [] []) rfl
  have stopped : Core.runStateful 3 (Core.State.initial core (environment a b n argument captured).values store) =
      .outOfFuel (checkpoint a b n argument captured store) := rfl
  refine ⟨path.runStateful_done_iff, stopped, ?_, Core.runStateful_resume stopped additional⟩
  have remaining : 3 * n + 6 - 3 = 3 * n + 3 := by omega
  simpa only [remaining] using (path.residual_of_outOfFuel stopped).2

theorem same_source_with_longer_actual_bodies_has_unbounded_cost (bound : Nat) (argument captured : Core.Value) :
    ∃ cost, bound < cost ∧ LocalFunctionApplicationEvaluatesWithCost names (environment .unit .unit bound argument captured)
      [] (source span span [] []) captured [] cost :=
  ⟨3 * bound + 6, by omega, counted .unit .unit bound argument captured [] span span [] []⟩

theorem aligned_but_untyped_actual_values_can_return_a_different_type :
    elaborateLocalFunctionApplication? names (context .word .word) (source span span [] []) = some (core, .word) ∧
    (environment .unit .unit 0 .unit (.bool true)).ids = (context .word .word).ids ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment .unit .unit 0 .unit (.bool true)) []
      (source span span [] []) (.bool true) [] 6 ∧ ¬ Core.ValueHasType (.bool true) .word :=
  ⟨(elaborated .word .word span span [] []).complete, rfl, counted .unit .unit 0 .unit (.bool true) [] span span [] [],
    by intro typed; cases typed⟩

theorem equal_typed_function_slots_with_permuted_ids_do_not_preserve_the_result :
    let yes := closure .unit .bool 0 (.bool true)
    let no := closure .unit .bool 0 (.bool false)
    let env : Resolved.Environment := [(aid,.unit),(gid,no),(fid,yes),(fid,yes)]
    env.ids.length = (context .unit .bool).ids.length ∧ env.ids ≠ (context .unit .bool).ids ∧
    Core.EnvironmentHasTypes env.values (context .unit .bool).values ∧
    LocalFunctionApplicationEvaluates names env [] (source span span [] []) (.bool true) [] ∧
    Core.Steps 6 (Core.State.initial core env.values []) (Core.State.final (.bool false) []) ∧
    Core.runStateful 6 (Core.State.initial core env.values []) = .done (.bool false) [] := by
  refine ⟨rfl, by decide, .cons .unit (.cons ?_ (.cons ?_ (.cons ?_ .nil))), ?_,
    .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl)
      (.cons .invokeClosure (.cons (.var rfl) .refl))))), rfl⟩
  all_goals first
    | exact .closure (.cons .bool .nil) (.var rfl)
    | exact .call (.identifier .head (.tail (by decide) (.tail (by decide) .head)))
        (.identifier (.tail (by decide) .head) .head) (.var rfl)

private def skippedMissing : Syntax.Expr := ⟨span, .call
  ⟨span, .conditional (ref span "x") span (ref span "f") span (ref span "missing")⟩
  ⟨span, [ref span "x"]⟩⟩
theorem a_raw_selected_callee_does_not_make_the_unselected_child_check :
    LocalFunctionApplicationEvaluatesWithCost names (environment .bool .bool 0 (.bool true) (.bool false))
      [] skippedMissing (.bool false) [] 9 ∧
    LocalFunctionApplicationEvaluates names (environment .bool .bool 0 (.bool true) (.bool false))
      [] skippedMissing (.bool false) [] ∧
    elaborateLocalFunctionApplication? names (context .bool .bool) skippedMissing = none := by
  have costed : LocalFunctionApplicationEvaluatesWithCost names (environment .bool .bool 0 (.bool true) (.bool false))
      [] skippedMissing (.bool false) [] 9 :=
    .call (parameterType := .bool) (resultType := .bool) (body := .var 1) (captured := [.bool false])
      (functionCost := 4) (argumentCost := 1) (bodyCost := 1)
      (.ifTrue (condition := ref span "x") (thenBranch := ref span "f") (elseBranch := ref span "missing")
        (.identifier (.tail (by decide) .head) .head)
        (.identifier .head (.tail (by decide) .head)))
      (.identifier (.tail (by decide) .head) .head) (.cons (.var rfl) .refl)
  refine ⟨costed, costed.erase, ?_⟩
  simp [elaborateLocalFunctionApplication?, skippedMissing, ref, elaborateLocalExpression?,
    resolveLocalExpression?, names, LocalNameTable.lookup?]

theorem an_equally_typed_other_function_is_not_exact_source_provenance :
    Core.HasType (context .unit .bool).values (.apply (.var 2) (.var 0)) .bool ∧
    ¬ LocalFunctionApplicationElaborates names (context .unit .bool) (source span span [] [])
      (.apply (.var 2) (.var 0)) .bool := by
  refine ⟨.apply (.var rfl) (.var rfl), ?_⟩
  intro other
  have same := ((elaborated .unit .bool span span [] []).result_unique other).1
  cases same

theorem the_same_static_call_does_not_identify_different_actual_captures
    (argument left right : Core.Value) (different : left ≠ right) (store : Core.Store) :
    Core.runStateful 6 (Core.State.initial core (environment .unit .unit 0 argument left).values store) = .done left store ∧
    Core.runStateful 6 (Core.State.initial core (environment .unit .unit 0 argument right).values store) = .done right store ∧
    LocalFunctionApplicationEvaluates names (environment .unit .unit 0 argument left) store (source span span [] []) left store ∧
    ¬ LocalFunctionApplicationEvaluates names (environment .unit .unit 0 argument left) store (source span span [] []) right store := by
  have actual := raw .unit .unit 0 argument left store span span [] []
  exact ⟨rfl, rfl, actual, fun wrong => different (actual.deterministic wrong).1⟩

theorem pending_word_operation_may_fault_after_a_successful_unit_endpoint (store : Core.Store) :
    Core.Steps 6 ⟨.eval core (environment .unit .unit 0 .unit .unit).values, [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ :=
  ⟨manualCall .unit .unit 0 .unit .unit store _, rfl⟩

end Tests.FrontendLocalApplicationEvaluation
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationEvaluation
/-! Parsed call children and actual closure bodies supply independent evidence.
Expected Core, values, costs and checkpoints are fixed before correspondence. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationEvaluation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def own : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ApplicationEvaluation", by decide⟩], by decide⟩⟩, 17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨own,n⟩
private def foreign : Resolved.LocalId := ⟨{ own with declarationIndex := 9 },999⟩
private def names : LocalNameTable := [("f",id 7),("f",id 99),("x",id 2),("c",foreign),("g",id 4),("y",id 3)]
private def ctx (input output x : Core.Ty) : Resolved.Context :=
  [(id 2,x),(id 7,.function input output),(foreign,.bool),(id 4,.function input output),(id 3,.word)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def env (f g x : Core.Value) (c : Bool) : Resolved.Environment :=
  [(id 2,x),(id 7,f),(foreign,.bool c),(id 4,g),(id 3,w 9)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-evaluation.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) s!"original full expression range changed: {text}"
  return source
private structure Child (context : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers context.ids resolved core
  typing : Resolved.HasType context resolved type
private def child (context : Resolved.Context) (source : Syntax.Expr) : IO (Child context source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : context.lookup? localId, indexed : Resolved.LocalScope.index? context.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child context inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [original]; exact .unit,.unit,.unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← child context left; let b ← child context right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← child context left; let b ← child context right
      if ta : a.type = .word then
        if bt : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
          by rw [original]; exact .subtract a.resolution b.resolution,.binary a.lowered b.lowered,
          .binary (show Resolved.HasType context a.resolved .word from ta ▸ a.typing)
            (show Resolved.HasType context b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right word type differs")
      else throw (IO.userError "left word type differs")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child context condition; let a ← child context yes; let b ← child context no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "whole guard type differs")
  | _ => throw (IO.userError "outside independent static child grammar")
termination_by sizeOf source
private structure Application (context : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates names context source core type
private def application (context : Resolved.Context) (source : Syntax.Expr) : IO (Application context source) := do
  match original : source with
  | ⟨_,.call callee ⟨span,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains span && span.contains argument.span &&
        decide (callee.span.endByte ≤ span.startByte)) "original call ranges/order changed"
      let f ← child context callee; let a ← child context argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "single argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not a root single-argument call")
private structure Raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : LocalExpressionEvaluatesWithCost names environment s source value s cost
private def raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Raw environment s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : environment.lookup? localId with
          | some value => return ⟨value,1,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← raw environment s inner
      return ⟨a.value,a.cost,by rw [original]; exact .group a.evidence⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,1,by rw [original]; exact .unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← raw environment s left; let b ← raw environment s right
      return ⟨.pair a.value b.value,a.cost+b.cost+3,by rw [original]; exact .pair a.evidence b.evidence⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← raw environment s left; let b ← raw environment s right
      match av : a.value, bv : b.value with
      | .word x,.word y => return ⟨.word (x.sub y),a.cost+b.cost+3,by rw [original]; exact .subtract (av ▸ a.evidence) (bv ▸ b.evidence)⟩
      | _,_ => throw (IO.userError "actual subtraction operands differ")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw environment s condition
      match cv : c.value with
      | .bool true =>
          let a ← raw environment s yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw environment s no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual condition is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private structure Body (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : Core.Steps cost (.initial body actual s) (.final value final)
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) : IO (Body body actual s) := do
  match original : body, values : actual with
  | .var index,_ =>
      match found : actual[index]? with
      | some value => return ⟨value,s,1,by rw [original]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "actual closure body variable missing")
  | .pair (.var 0) (.var 1),left :: right :: _ => return ⟨.pair left right,s,5,by
      rw [original,values]; exact .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl))))⟩
  | .newCell .word (.var 0),value :: _ => return ⟨.cellRef .word s.length,s ++ [value],3,by
      rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | .loadCell (.var 0),.cellRef type location :: _ =>
      match found : s.read? location with
      | some value => return ⟨value,s,3,by rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell found) .refl))⟩
      | none => throw (IO.userError "actual cell is not allocated")
  | _,_ => throw (IO.userError "outside hand-built actual body paths")
private structure Counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : LocalFunctionApplicationEvaluatesWithCost names environment s source value final cost
private def counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Counted environment s source) := do
  match original : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
      let f ← raw environment s callee; let a ← raw environment s argument
      match shape : f.value with
      | .closure _ _ body captured =>
          let b ← bodyPath body (a.value :: captured) s
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence b.path⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not exactly one original argument")
private def verify (text : String) (input output xtype : Core.Ty) (f g x : Core.Value) (c : Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) (s final : Core.Store) : IO Unit := do
  let source ← parsed text
  let original ← application (ctx input output xtype) source
  let actual ← counted (env f g x c) s source
  check (decide (original.core = expected ∧ original.type = output ∧ actual.value = value ∧ actual.final = final ∧ actual.cost = cost ∧
    elaborateLocalExpression? names (ctx input output xtype) source = none))
    "independent original Core/value/store/cost expectation changed"
  have aligned : (env f g x c).ids = (ctx input output xtype).ids := rfl
  let p := actual.evidence.toSteps original.evidence aligned
  have _ := actual.evidence.erase.deterministic actual.evidence.erase
  have _ := actual.evidence.erase.exists_cost
  have _ := actual.evidence.cost_pos
  have _ := actual.evidence.cost_unique actual.evidence
  let ce := (original.evidence.evaluates_iff aligned).mp actual.evidence.erase
  have _ := (elaborateLocalFunctionApplication?_evaluates_iff original.evidence.complete aligned).mpr ce
  let restored := (original.evidence.evaluatesWithCost_iff_steps aligned).mpr p
  have _ := actual.evidence.deterministic restored
  have _ := (elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps original.evidence.complete aligned).mpr p
  have _ := (localFunctionApplicationEvaluates_iff_exists_cost).mpr ⟨actual.cost,actual.evidence⟩
  have uniform := (original.evidence.evaluates_iff_exists_uniform_steps aligned).mp actual.evidence.erase
  have _ := (original.evidence.evaluates_iff_exists_uniform_steps aligned).mpr uniform
  for k in [[],[.letBody (.var 0) [w 19]],[.unaryApply .wordNot]] do
    have _ := actual.evidence.toStepsWithContinuation original.evidence aligned k
    pure ()
  let k : List Core.Frame := [.unaryApply .wordNot]
  check (match Core.runStateful cost ⟨.eval expected (env f g x c).values,k,s⟩ with
    | .outOfFuel checkpoint => decide (checkpoint = ⟨.ret value,k,final⟩)
    | .fault error checkpoint => decide (error = .invalidUnaryOperand .wordNot value ∧ checkpoint = ⟨.ret value,k,final⟩)
    | _ => false) "fixed-cost arbitrary continuation endpoint was mistaken for completion"
  for fuel in List.range (cost+3) do
    check (match Core.runStateful fuel (.initial expected (env f g x c).values s) with
      | .done v t => decide (cost ≤ fuel ∧ v = value ∧ t = final)
      | .outOfFuel _ => decide (fuel < cost)
      | _ => false) "closed exact path threshold changed"
  for spent in List.range cost do
    match stopped : Core.runStateful spent (.initial original.core (env f g x c).values s) with
    | .outOfFuel checkpoint =>
        have _ := p.residual_of_outOfFuel stopped
        have _ := Core.runStateful_resume stopped (cost-spent)
        check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "actual saved continuation or residual changed"
    | _ => throw (IO.userError "genuine checkpoint missing")
private def fn : Core.Value := .closure .word (.product .word .word) (.pair (.var 0) (.var 1)) [w 7]
private def gn : Core.Value := .closure .word (.product .word .word) (.var 1) [.pair (w 2) (w 9)]
private def mixed : Core.Expr := .apply (.ifE (.var 2) (.var 1) (.var 3)) (.binary .wordSub (.var 0) (.var 4))
private def selected : IO Unit := do
  let source ← parsed "(c ? f : g)(x - y)"
  match source.value with
  | .call callee ⟨span,[⟨argumentSpan,.binary left op right⟩]⟩ =>
      check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 11 ∧ span.startByte = 11 ∧ span.endByte = 18 ∧
        argumentSpan.startByte = 12 ∧ argumentSpan.endByte = 17 ∧ left.span.startByte = 12 ∧ right.span.startByte = 16 ∧
        op.span.startByte = 14 ∧ op.value = .subtract)) "original nested byte ranges or subtraction spelling changed"
  | _ => throw (IO.userError "original conditional callee/subtraction argument changed shape")
  have ft : Core.ValueHasType fn (.function .word (.product .word .word)) := .closure (.cons .word .nil) (.pair (.var rfl) (.var rfl))
  have gt : Core.ValueHasType gn (.function .word (.product .word .word)) := .closure (.cons (.pair .word .word) .nil) (.var rfl)
  for c in [false,true] do
    have _ : Core.EnvironmentHasTypes (env fn gn (w 14) c).values (ctx .word (.product .word .word) .word).values :=
      .cons .word (.cons ft (.cons .bool (.cons gt (.cons .word .nil))))
    for s in [[],[w 91]] do
      let f := if c then fn else gn
      verify "(c ? f : g)(x - y)" .word (.product .word .word) .word fn gn (w 14) c mixed
        (if c then .pair (w 5) (w 7) else .pair (w 2) (w 9)) (if c then 17 else 13) s s
      check (decide (Core.runStateful 5 (.initial mixed (env fn gn (w 14) c).values s) =
        .outOfFuel ⟨.ret f,[.applyArgument (.binary .wordSub (.var 0) (.var 4)) (env fn gn (w 14) c).values],s⟩)) "function-first caller frame changed"
      let body := if c then Core.Expr.pair (.var 0) (.var 1) else .var 1
      let captured := if c then [w 7] else [.pair (w 2) (w 9)]
      check (decide (Core.runStateful 11 (.initial mixed (env fn gn (w 14) c).values s) =
        .outOfFuel ⟨.ret (w 5),[.applyClosure .word (.product .word .word) body captured],s⟩)) "strict argument or actual captures changed"
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) []
private theorem faultExcludesPath {start stopped : Core.State} {fuel : Nat} {error : Core.MachineFault}
    (fault : Core.runStateful fuel start = .fault error stopped) :
    ¬ ∃ cost value final, Core.Steps cost start (.final value final) := by
  rintro ⟨cost,value,final,path⟩
  by_cases enough : cost ≤ fuel
  · have done := path.runStateful_done_iff.mpr enough
    rw [fault] at done; cases done
  · obtain ⟨checkpoint,exhausted⟩ := path.runStateful_outOfFuel_iff.mpr (Nat.lt_of_not_ge enough)
    rw [fault] at exhausted; cases exhausted
private def effects : IO Unit := do
  for s in [[],[w 23]] do
    verify "f(())" .unit .unit .word (identity .unit) (identity .unit) (w 14) true (.apply (.var 1) .unit) .unit 6 s s
    verify "f((x,y))" (.product .word .word) (.product .word .word) .word (identity (.product .word .word)) (identity (.product .word .word))
      (w 14) true (.apply (.var 1) (.pair (.var 0) (.var 4))) (.pair (w 14) (w 9)) 10 s s
    let allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
    have _ : Core.ValueHasType allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
    verify "f(x)" .word (.cell .word) .word allocator allocator (w 14) true (.apply (.var 1) (.var 0)) (.cellRef .word s.length) 8 s (s ++ [w 14])
  let reader : Core.Value := .closure (.cell .word) .word (.loadCell (.var 0)) []
  have rt : Core.ValueHasType reader (.function (.cell .word) .word) := .closure .nil (.loadCell (.var rfl))
  have _ : Core.EnvironmentHasTypes (env reader reader (.cellRef .word 0) true).values (ctx (.cell .word) .word (.cell .word)).values :=
    .cons .cellRef (.cons rt (.cons .bool (.cons rt (.cons .word .nil))))
  verify "f(x)" (.cell .word) .word (.cell .word) reader reader (.cellRef .word 0) true (.apply (.var 1) (.var 0)) (w 23) 8 [w 23] [w 23]
  check (decide (Core.runStateful 7 (.initial (.apply (.var 1) (.var 0)) (env reader reader (.cellRef .word 0) true).values []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "structural value typing fabricated allocated cells"
  let source ← parsed "f(x)"
  let original ← application (ctx (.cell .word) .word (.cell .word)) source
  if exactCore : original.core = .apply (.var 1) (.var 0) then
    have fault : Core.runStateful 7 (.initial original.core (env reader reader (.cellRef .word 0) true).values []) =
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩ := by rw [exactCore]; rfl
    have _ : ¬ ∃ value final, LocalFunctionApplicationEvaluates names (env reader reader (.cellRef .word 0) true) [] source value final := by
      rintro ⟨value,final,evaluation⟩
      obtain ⟨cost,evidence⟩ := evaluation.exists_cost
      exact faultExcludesPath fault ⟨cost,value,final,evidence.toSteps original.evidence rfl⟩
    pure ()
  else throw (IO.userError "reader exact Core changed")
private def contrasts : IO Unit := do
  for text in ["(c ? f : missing)(x)","f(c ? x : missing)"] do
    let source ← parsed text
    let actual ← counted (env (identity .word) (identity .word) (w 14) true) [] source
    check (decide (actual.value = w 14 ∧ actual.cost = 9 ∧ actual.final = [] ∧
      elaborateLocalFunctionApplication? names (ctx .word .word .word) source = none)) "raw selected success was mistaken for whole acceptance"
    have _ := actual.evidence.erase
    pure ()
end ParsedLocalApplicationEvaluation
open ParsedLocalApplicationEvaluation
def frontendParsedLocalApplicationEvaluationTests : IO Unit := do
  selected; effects; contrasts
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationEvaluationEntries
/-! Original whole declarations retain their entry rejection. Independent
parameter records and actual closure bodies now feed the source-call laws. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalApplicationEvaluationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "actual-local-call.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Declared (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declare (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) : IO (Declared types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "outside parameter fixture")
private structure Bound (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def bindArgs (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Bound types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original, actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: remaining =>
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← bindArgs types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest remaining
          return ⟨tail.inputs, by rw [original, actual]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate actual parameter")
      else throw (IO.userError "actual type differs")
  | _, _ => throw (IO.userError "actual arity differs")
private structure Reference (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def reference (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Reference s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Call (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private structure OriginalCall (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
private def callShape (source : Syntax.Expr) : IO (OriginalCall source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ => return ⟨span, argumentsSpan, callee, argument, original⟩
  | _ => throw (IO.userError "not original singleton call")
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Call s source) := do
  let original ← callShape source
  let span := original.span; let argumentsSpan := original.argumentsSpan
  let callee := original.callee; let argument := original.argument
  check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
    decide (callee.span.endByte ≤ argumentsSpan.startByte)) "call child ranges/order changed"
  let f ← reference s callee; let a ← reference s argument
  match shape : f.type with
  | .function input output =>
      if same : a.type = input then
        return ⟨.apply f.core a.core, output, by
          rw [original.shape]
          exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
      else throw (IO.userError "argument type differs")
  | _ => throw (IO.userError "callee not Function")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output)]
private def staticCase (input output : Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed; let types := table input output
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = [("x", ⟨owner, 1⟩), ("f", ⟨owner, 0⟩)] ∧
    ps.inputs.context.values = [input, .function input output])) "parameter-only static layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "return range changed"
  let a ← application ps.inputs returned
  check (decide (a.core = target ∧ a.type = output ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (target, output) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent original call differs"
  have wrong : ¬ LocalFunctionApplicationElaborates ps.inputs.names ps.inputs.context returned
      (.letE .unit (target.weakenAt 0)) output := by intro evidence; cases evidence
  have _ := wrong
  check (decide (Core.infer? ps.inputs.context.values (.letE .unit (target.weakenAt 0)) = some output)) "wrong Core not same typed"
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature output := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "header policy changed")
      else throw (IO.userError "return type differs")
  | _ => throw (IO.userError "return clause differs")
  check ((compileRuntimeFunction? types owner source).isNone) "source call entered old compilation"
  return (source, ps.inputs)
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row value changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (value : Core.Store → Core.Value) (finalStore : Core.Store → Core.Store) (bodyCost : Nat)
    (bodyEvaluation : ∀ s, Core.Evaluates (argument.value :: captured) s body (value s) (finalStore s))
    (bodyPath : ∀ s k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret (value s), k, finalStore s⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped⟩
  let args := [f, argument]; let types := table argument.type output
  let (source, statics) ← staticCase argument.type output
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.context = statics.context ∧
    actual.inputs.environment.values = (args.map (·.value)).reverse ∧
    actual.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "actual records/order changed"
  let ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "original body changed")
  let call ← application actual.inputs.toTypeInputs returned
  if originalCore : call.core = target then
    have elaboration : LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context returned target call.type := by
      simpa only [originalCore, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using call.evidence
    let original ← callShape returned
    let span := original.span; let argumentsSpan := original.argumentsSpan
    let callee := original.callee; let arg := original.argument
    have elaboration := Eq.mp (congrArg (fun src =>
      LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context src target call.type) original.shape) elaboration
    let functionObserved ← observed actual.inputs callee f.value
    let argumentObserved ← observed actual.inputs arg argument.value
    let actualValues : PLift (actual.inputs.environment.values = [argument.value, f.value]) ←
      if same : actual.inputs.environment.values = [argument.value, f.value] then pure ⟨same⟩
      else throw (IO.userError "original runtime values not retained")
    for s in [[], [w 91, w 73]] do
      have manual (k) : Core.Steps (bodyCost + 5)
          ⟨.eval target actual.inputs.environment.values, k, s⟩ ⟨.ret (value s), k, finalStore s⟩ := by
        rw [actualValues.down]
        exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument
          (.cons (.var rfl) (.cons .invokeClosure (bodyPath s k)))))
      have raw : LocalFunctionApplicationEvaluates actual.inputs.names actual.inputs.environment s
          ⟨span, .call callee ⟨argumentsSpan, [arg]⟩⟩ (value s) (finalStore s) :=
        .call (functionObserved.evidence s).erase (argumentObserved.evidence s).erase (bodyEvaluation s)
      have costed := LocalFunctionApplicationEvaluatesWithCost.call (span := span) (argumentsSpan := argumentsSpan)
        (functionObserved.evidence s) (argumentObserved.evidence s) (bodyPath s [])
      have path := costed.toSteps elaboration actual.inputs.sameIds
      have _ := raw.deterministic costed.erase
      have _ := raw.exists_cost
      have _ := localFunctionApplicationEvaluates_iff_exists_cost.mpr ⟨_, costed⟩
      have reflected := elaboration.evaluatesWithCost_iff_steps actual.inputs.sameIds |>.mpr (manual [])
      have _ := costed.deterministic reflected
      have _ := costed.cost_unique reflected
      have _ := costed.cost_pos
      have _ := elaboration.evaluates_iff actual.inputs.sameIds |>.mpr ((elaboration.evaluates_iff actual.inputs.sameIds).mp raw)
      have _ := elaboration.evaluates_iff_exists_uniform_steps actual.inputs.sameIds |>.mp raw
      have _ := elaborateLocalFunctionApplication?_evaluates_iff elaboration.complete actual.inputs.sameIds |>.mp raw
      have _ := elaborateLocalFunctionApplication?_evaluatesWithCost_iff_steps elaboration.complete actual.inputs.sameIds |>.mp costed
      let cost := bodyCost + 5
      for fuel in List.range (cost + 3) do
        check ((prepareRuntimeFunction? types owner source args).isNone &&
          (runRuntimeFunction? types owner source args fuel s).isNone) "call leaked into old whole entry"
        check (match Core.runStateful fuel (.initial target actual.inputs.environment.values s) with
          | .done v t => decide (cost ≤ fuel ∧ v = value s ∧ t = finalStore s)
          | .outOfFuel _ => decide (fuel < cost)
          | .fault .. => false) "independent source call cost/value/store differs"
      check (decide (Core.runStateful 2 (.initial target actual.inputs.environment.values s) =
        .outOfFuel ⟨.ret f.value, [.applyArgument (.var 0) actual.inputs.environment.values], s⟩ ∧
        Core.runStateful 4 (.initial target actual.inputs.environment.values s) =
        .outOfFuel ⟨.ret argument.value, [.applyClosure argument.type output body captured], s⟩)) "actual caller/capture frames differ"
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial target actual.inputs.environment.values s) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            for more in [0, 1, cost - spent, cost + 2] do
              have _ := Core.runStateful_resume stopped more
              check (decide (Core.runStateful more checkpoint = Core.runStateful (spent + more)
                (.initial target actual.inputs.environment.values s))) "genuine checkpoint did not resume full state"
            check (decide (Core.runStateful (cost - spent) checkpoint = .done (value s) (finalStore s))) "remaining fuel differs"
            if spent = 4 then
              match middle : Core.runStateful 1 checkpoint with
              | .outOfFuel next =>
                  have _ := Core.runStateful_resume middle (cost - 5)
                  check (decide (Core.runStateful (cost - 5) next = .done (value s) (finalStore s))) "actual three-chunk continuation differs"
              | _ => throw (IO.userError "actual body-entry checkpoint missing")
        | _ => throw (IO.userError "missing genuine call checkpoint")
      let k : List Core.Frame := [.unaryApply .wordNot]
      have _ := costed.toStepsWithContinuation elaboration actual.inputs.sameIds k
      check (match Core.UnaryOp.wordNot.apply (value s), Core.runStateful cost ⟨.eval target actual.inputs.environment.values, k, s⟩ with
        | some _, .outOfFuel endpoint => decide (endpoint = ⟨.ret (value s), k, finalStore s⟩)
        | none, .fault error endpoint => decide (error = .invalidUnaryOperand .wordNot (value s) ∧ endpoint = ⟨.ret (value s), k, finalStore s⟩)
        | _, _ => false) "pending continuation endpoint was confused with closed completion"
  else throw (IO.userError "actual static lowering changed")
private def delayed : Nat → Core.Expr | 0 => .word (Core.Word.ofNatModulo 7) | n + 1 => .letE .unit (delayed n)
private theorem delayedTyped (n : Nat) (ctx : Core.Context) : Core.HasType ctx (delayed n) .word := by
  induction n generalizing ctx with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedEvaluation (n : Nat) (env : Core.Environment) (s : Core.Store) :
    Core.Evaluates env s (delayed n) (w 7) s := by
  induction n generalizing env with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedPath (n : Nat) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) env, k, s⟩ ⟨.ret (w 7), k, s⟩ := by
  induction n generalizing env with
  | zero => exact .cons .word .refl
  | succ n ih => simpa [delayed, Nat.mul_succ, Nat.add_assoc] using Core.Steps.cons .enterLet (.cons .unit (.cons .bindLet (ih (.unit :: env))))
end LocalApplicationEvaluationEntries
open LocalApplicationEvaluationEntries
def frontendParsedLocalApplicationEvaluationEntryTests : IO Unit := do
  for argument in [(⟨.word, w 9, .word⟩ : TypedRuntimeArgument), ⟨.unit, .unit, .unit⟩,
      ⟨.cell .word, .cellRef .word 700, .cellRef⟩,
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩] do
    execute argument argument.type (.var 0) [] (.closure .nil (.var rfl)) (fun _ => argument.value) id 1
      (fun _ => .var rfl) (fun _ _ => .cons (.var rfl) .refl)
  for x in [9, 14] do
    let argument : TypedRuntimeArgument := ⟨.word, w x, .word⟩
    execute argument .word (.var 1) [w 7] (.closure (.cons .word .nil) (.var rfl)) (fun _ => w 7) id 1
      (fun _ => .var rfl) (fun _ _ => .cons (.var rfl) .refl)
    for n in [0, 1, 4, 9] do
      execute argument .word (delayed n) [] (.closure .nil (delayedTyped n _)) (fun _ => w 7) id (3 * n + 1)
        (delayedEvaluation n [w x]) (delayedPath n [w x])
    execute argument (.cell .word) (.newCell .word (.var 0)) [] (.closure .nil (.newCell (.var rfl)))
      (fun s => .cellRef .word s.length) (fun s => s ++ [w x]) 3
      (fun _ => .newCell (.var rfl)) (fun _ _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨17⟩))] do
    let _ ← staticCase type type
    pure ()
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationRunner
/-! One actual input record supplies every projection. Original source and
hand-built closure-body paths fix the expected result before either runner. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationRunner
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ApplicationRunner",by decide⟩],by decide⟩⟩,19⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 3},999⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def inputs (output : Core.Ty) (f shadow : Core.Value)
    (ft : Core.ValueHasType f (.function .word output)) (gt : Core.ValueHasType shadow (.function .word output)) (x : Nat) : LocalInputs :=
  ⟨[⟨"x",id 2,.word,w x,.word⟩,⟨"f",id 7,.function .word output,f,ft⟩,
    ⟨"f",id 91,.function .word output,shadow,gt⟩,⟨"c",foreign,.bool,.bool true,.bool⟩],by
      change [id 2,id 7,id 91,foreign].Nodup; decide⟩
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-runner.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original full byte range changed"
  return source
private structure Child (s : LocalInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def child (s : LocalInputs) (source : Syntax.Expr) : IO (Child s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some localId =>
          match typed : s.context.lookup? localId, indexed : Resolved.LocalScope.index? s.context.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child s inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | _ => throw (IO.userError "outside independent static child certificate")
termination_by sizeOf source
private structure Application (s : LocalInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private def application (s : LocalInputs) (source : Syntax.Expr) : IO (Application s source) := do
  match original : source with
  | ⟨_,.call callee ⟨span,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains span && span.contains argument.span &&
        decide (callee.span.endByte ≤ span.startByte)) "original call ranges/order changed"
      let f ← child s callee; let a ← child s argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not exactly one original argument")
private structure Raw (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : LocalExpressionEvaluatesWithCost s.names s.environment store source value store cost
private def raw (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) : IO (Raw s store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some localId =>
          match found : s.environment.lookup? localId with
          | some value => return ⟨value,1,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← raw s store inner
      return ⟨a.value,a.cost,by rw [original]; exact .group a.evidence⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw s store condition
      match cv : c.value with
      | .bool true =>
          let a ← raw s store yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw s store no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual guard is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private def readBody : Core.Expr := .loadCell (.var 1)
private def writeBody : Core.Expr := .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))
private def reader : Core.Value := .closure .word .word readBody [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word writeBody [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private theorem readerTyped : Core.ValueHasType reader (.function .word .word) :=
  .closure (.cons .cellRef .nil) (.loadCell (.var rfl))
private theorem writerTyped : Core.ValueHasType writer (.function .word .word) :=
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
private theorem allocatorTyped : Core.ValueHasType allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
private structure Body (body : Core.Expr) (actual : Core.Environment) (store : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : ∀ k, Core.Steps cost ⟨.eval body actual,k,store⟩ ⟨.ret value,k,final⟩
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (store : Core.Store) : IO (Body body actual store) := do
  match original : body, values : actual, saved : store with
  | .loadCell (.var 1),arg :: .cellRef .word 0 :: [],[old] => return ⟨old,store,3,by
      intro k; rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell (by rw [saved]; rfl)) .refl))⟩
  | .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)),arg :: .cellRef .word 0 :: [],[old] => return ⟨arg,[arg],10,by
      intro k; rw [original,values,saved]
      exact .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet
        (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))))))))⟩
  | .newCell .word (.var 0),arg :: [],_ => return ⟨.cellRef .word store.length,store ++ [arg],3,by
      intro k; rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | _,_,_ => throw (IO.userError "outside independent actual body path")
private structure Counted (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store source value final cost
private def counted (s : LocalInputs) (store : Core.Store) (source : Syntax.Expr) : IO (Counted s store source) := do
  match original : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
      let f ← raw s store callee; let a ← raw s store argument
      match shape : f.value with
      | .closure _ _ body captured =>
          let b ← bodyPath body (a.value :: captured) store
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence (b.path [])⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not a single argument call")
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def verify (s : LocalInputs) (text : String) (type : Core.Ty) (value : Core.Value)
    (cost : Nat) (store final : Core.Store)
    (runtime : Option (PLift (Core.RuntimeEnvironmentHasTypes [.word] s.environment.values s.context.values ∧
      Core.StoreHasTypes [.word] store)) := none) : IO Unit := do
  let source ← parsed text
  let original ← application s source
  let actual ← counted s store source
  if staticEq : original.core = target ∧ original.type = type then
    if actualEq : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have elaboration : LocalFunctionApplicationElaborates s.names s.context source target type := by
        simpa only [staticEq.1,staticEq.2] using original.evidence
      have evaluation : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store source value final cost := by
        simpa only [actualEq.1,actualEq.2.1,actualEq.2.2] using actual.evidence
      let path := evaluation.toSteps elaboration s.sameIds
      have checked := LocalInputs.checkApplication?_iff_elaborates.mpr elaboration
      have whole := LocalInputs.checkApplication?_iff_hasType.mp ⟨target,checked⟩
      have _ := LocalInputs.checkApplication?_iff_hasType.mpr whole
      have done := (LocalInputs.runApplication?_done_iff_of_cost whole evaluation (fuel := cost)).mpr (Nat.le_refl cost)
      have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mpr ⟨whole,evaluation.erase⟩
      have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mp ⟨cost,done⟩
      have _ := LocalInputs.runApplication?_done_iff_typed_cost.mp done
      have _ := LocalInputs.runApplication?_done_iff_typed_cost.mpr ⟨whole,cost,evaluation,Nat.le_refl cost⟩
      match runtime with
      | some proof =>
          have _ := LocalInputs.runApplication?_runtime_done_sound proof.down.1 proof.down.2 done
          have identified : ∃ future, Core.WorldExtends [.word] future ∧ Core.RuntimeStoreHasTypes future final ∧
              Core.RuntimeValueHasType future value type := by
            obtain ⟨fw,fs,v,n,extension,st,vt,e,_⟩ := LocalInputs.runApplication?_runtime_has_exact_cost whole proof.down.1 proof.down.2 ⟨value, final, evaluation.erase⟩
            obtain ⟨rfl,rfl,rfl⟩ := e.deterministic evaluation
            exact ⟨fw,extension,st,vt⟩
          have _ := identified
          for fuel in List.range (cost+3) do
            have _ := LocalInputs.runApplication?_runtime_never_faults proof.down.1 proof.down.2 source fuel type
            pure ()
      | none => pure ()
      check (decide (s.checkApplication? source = some (target,type) ∧ s.check? source = none)) "new checker exactness or old pure boundary changed"
      for fuel in List.range (cost+3) do
        have _ := LocalInputs.runApplication?_outOfFuel_iff_of_cost whole evaluation (fuel := fuel)
        check (decide (s.run? fuel source store = none)) "new call entered old pure runner"
        check (match result : s.runApplication? fuel source store with
          | some (tag,.done v t) => decide (tag = type ∧ cost ≤ fuel ∧ v = value ∧ t = final)
          | some (tag,.outOfFuel _) => decide (tag = type ∧ fuel < cost)
          | _ => false) "checked full result/type tag or exact cost changed"
        match result : s.runApplication? fuel source store with
        | some (tag,.done v t) =>
            have _ := LocalInputs.runApplication?_done_sound result
            have _ := LocalInputs.runApplication?_eq_some_iff.mp result
            pure ()
        | _ => pure ()
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial target s.environment.values store) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            have suspended := LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,stopped⟩
            have _ := LocalInputs.runApplication?_residual_of_outOfFuel evaluation suspended
            for additional in [0,1,cost-spent,cost+2] do
              have _ := LocalInputs.runApplication?_resume suspended additional
              check (decide (s.runApplication? (spent+additional) source store =
                some (type,Core.runStateful additional checkpoint))) "full-result resumption changed"
            check (decide (s.runApplication? spent source store = some (type,.outOfFuel checkpoint) ∧
              Core.runStateful (cost-spent) checkpoint = .done value final)) "original full checkpoint/residual changed"
        | _ => throw (IO.userError "genuine checked checkpoint missing")
    else throw (IO.userError "independent expected value/store/cost changed")
  else throw (IO.userError "independent source Core/type changed")
private def fixtures : IO Unit := do
  let r := inputs .word reader writer readerTyped writerTyped 14
  let writerInputs := inputs .word writer reader writerTyped readerTyped 14
  let a := inputs (.cell .word) allocator allocator allocatorTyped allocatorTyped 14
  check (decide (r.names = [("x",id 2),("f",id 7),("f",id 91),("c",foreign)] ∧
    r.environment.values = [w 14,reader,writer,.bool true])) "one actual record lost duplicate first-match/order"
  let source ← parsed "f(x)"
  match source.value with
  | .call f ⟨span,[x]⟩ => check (decide (f.span.startByte = 0 ∧ f.span.endByte = 1 ∧ span.startByte = 1 ∧
      span.endByte = 4 ∧ x.span.startByte = 2 ∧ x.span.endByte = 3)) "original argument byte ranges changed"
  | _ => throw (IO.userError "original singleton call changed")
  for old in [23,91] do
    have st : Core.StoreHasTypes [.word] [w old] := Core.StoreHasTypes.nil.allocate .word .word
    have rt : Core.RuntimeValueHasType [.word] reader (.function .word .word) := .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
    have wt : Core.RuntimeValueHasType [.word] writer (.function .word .word) := .closure (.cons (.cellRef rfl) .nil)
      (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
    have atyped : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
    verify r "f(x)" .word (w old) 8 [w old] [w old] (some ⟨⟨.cons .word (.cons rt (.cons wt (.cons .bool .nil))),st⟩⟩)
    verify writerInputs "f(x)" .word (w 14) 15 [w old] [w 14] (some ⟨⟨.cons .word (.cons wt (.cons rt (.cons .bool .nil))),st⟩⟩)
    verify a "f(x)" (.cell .word) (.cellRef .word 1) 8 [w old] [w old,w 14]
      (some ⟨⟨.cons .word (.cons atyped (.cons atyped (.cons .bool .nil))),st⟩⟩)
    check (decide (writerInputs.runApplication? 11 source [w old] = some (.word,
      .outOfFuel ⟨.ret .unit,[.letBody (.loadCell (.var 2)) [w 14,.cellRef .word 0]],[w 14]⟩))) "writer checkpoint lost updated store or actual captures"
  verify r "(f)(x)" .word (w 23) 8 [w 23] [w 23]
  verify r "f(x)" .word (.bool true) 8 [.bool true] [.bool true]
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro h; cases h
  have _ : ¬ Core.StoreHasTypes [.word] [.bool true] := by
    intro h; obtain ⟨v,found,_,typed⟩ := h.read (location := 0) rfl
    have eq : v = .bool true := (Option.some.inj found).symm
    subst v; cases typed
  for store in [[],[w 23],[.bool true]] do
    let checkpoint : Core.State := ⟨.eval (.var 0) r.environment.values,[.applyClosure .word .word readBody [.cellRef .word 0]],store⟩
    check (decide (r.runApplication? 3 source store = some (.word,.outOfFuel checkpoint))) "original genuine cp3 changed"
    if checked : r.checkApplication? source = some (target,.word) then
      have stopped : r.runApplication? 3 source store = some (.word,.outOfFuel checkpoint) :=
        LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,rfl⟩
      for additional in [0,4,5,9] do
        have _ := LocalInputs.runApplication?_resume stopped additional
        check (decide (r.runApplication? (3+additional) source store = some (.word,Core.runStateful additional checkpoint))) "fault/exhaustion resumption lost original tag"
    else throw (IO.userError "original reader check failed")
    if store.isEmpty then
      check (decide (r.runApplication? 7 source store = some (.word,
        .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩) ∧
        Core.runStateful 4 checkpoint = .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "missing store fault was hidden or restart used"
      check (match r.runApplication? 4 source store with
        | some (.word,.outOfFuel _) => true | _ => false) "restart was confused with saved cp3 plus four steps"
    else
      let some value := store[0]? | throw (IO.userError "original allocated payload missing")
      check (decide (Core.runStateful 5 checkpoint = .done value store)) "saved actual store was not used on resumption"
  let rejected ← parsed "(c ? f : missing)(x)"
  let actual ← counted r [w 23] rejected
  check (decide (actual.value = w 23 ∧ actual.final = [w 23] ∧ actual.cost = 11 ∧ r.checkApplication? rejected = none)) "raw selected success bypassed whole checking"
  for fuel in [0,3,11,30] do
    have _ := LocalInputs.runApplication?_eq_none_iff (inputs := r) (source := rejected) fuel [w 23]
    check (decide (r.runApplication? fuel rejected [w 23] = none)) "whole failure depended on fuel"
end ParsedLocalApplicationRunner
open ParsedLocalApplicationRunner
def frontendParsedLocalApplicationRunnerTests : IO Unit := fixtures
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationRunnerEntries
/-! Original declaration rows feed only the separate local application runner.
Independent paths and costs precede every executable comparison; whole entries remain closed. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalApplicationRunnerEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RunActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "checked-local-call.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Declared (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declare (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) : IO (Declared types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "outside parameter fixture")
private structure Bound (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def bindArgs (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Bound types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original, actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: remaining =>
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← bindArgs types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest remaining
          return ⟨tail.inputs, by rw [original, actual]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate actual parameter")
      else throw (IO.userError "actual type differs")
  | _, _ => throw (IO.userError "actual arity differs")
private structure Reference (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def reference (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Reference s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Call (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private structure OriginalCall (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
private def callShape (source : Syntax.Expr) : IO (OriginalCall source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ => return ⟨span, argumentsSpan, callee, argument, original⟩
  | _ => throw (IO.userError "not original singleton call")
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Call s source) := do
  let original ← callShape source
  let span := original.span; let argumentsSpan := original.argumentsSpan
  let callee := original.callee; let argument := original.argument
  check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
    decide (callee.span.endByte ≤ argumentsSpan.startByte)) "call child ranges/order changed"
  let f ← reference s callee; let a ← reference s argument
  match shape : f.type with
  | .function input output =>
      if same : a.type = input then
        return ⟨.apply f.core a.core, output, by
          rw [original.shape]
          exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
      else throw (IO.userError "argument type differs")
  | _ => throw (IO.userError "callee not Function")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output)]
private def staticCase (input output : Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed; let types := table input output
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = [("x", ⟨owner, 1⟩), ("f", ⟨owner, 0⟩)] ∧
    ps.inputs.context.values = [input, .function input output])) "parameter-only static layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "return range changed"
  let a ← application ps.inputs returned
  check (decide (a.core = target ∧ a.type = output ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (target, output) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent original call differs"
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature output := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "header policy changed")
      else throw (IO.userError "return type differs")
  | _ => throw (IO.userError "return clause differs")
  check ((compileRuntimeFunction? types owner source).isNone) "source call entered old compilation"
  return (source, ps.inputs)
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row value changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def delayed : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (delayed n)
private theorem delayedTyped (n : Nat) (type : Core.Ty) (rest : Core.Context) :
    Core.HasType (type :: rest) (delayed n) type := by
  induction n generalizing rest with
  | zero => exact .var rfl
  | succ n ih => exact .letE (.var rfl) (ih _)
private theorem delayedPath (n : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) (value :: rest), k, s⟩ ⟨.ret value, k, s⟩ := by
  induction n generalizing rest k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have path :=
        Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: rest) k)))
      have count : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [count]; exact path
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (world : Core.StoreTyping) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (argumentTyped : Core.RuntimeValueHasType world argument.value argument.type)
    (closureTyped : Core.RuntimeValueHasType world (.closure argument.type output body captured) (.function argument.type output))
    (storeTyped : Core.StoreHasTypes world s)
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped.erase⟩
  let args := [f, argument]; let types := table argument.type output
  let (source, statics) ← staticCase argument.type output
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.context = statics.context ∧
    actual.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "original actual records differ"
  let rows : PLift (actual.inputs.environment.values = (args.map (·.value)).reverse ∧
      actual.inputs.context.values = [argument.type, f.type]) ←
    if same : actual.inputs.environment.values = (args.map (·.value)).reverse ∧
        actual.inputs.context.values = [argument.type, f.type] then pure ⟨same⟩
    else throw (IO.userError "original projection ordering changed")
  have runtimeTyped : Core.RuntimeEnvironmentHasTypes world actual.inputs.environment.values actual.inputs.context.values := by
    rw [rows.down.1, rows.down.2]; exact .cons argumentTyped (.cons closureTyped .nil)
  let ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "original return changed")
  let call ← application actual.inputs.toTypeInputs returned
  if expected : call.core = target ∧ call.type = output then
    have originalElab : LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context returned target output := by
      simpa only [expected.1, expected.2, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using call.evidence
    let original ← callShape returned
    let fp ← observed actual.inputs original.callee f.value
    let ap ← observed actual.inputs original.argument argument.value
    have costed : LocalFunctionApplicationEvaluatesWithCost actual.inputs.names actual.inputs.environment s returned value t (bodyCost + 5) := by
      rw [original.shape]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := original.span) (argumentsSpan := original.argumentsSpan)
          (fp.evidence s) (ap.evidence s) (bodyPath [])
    have manual (k) : Core.Steps (bodyCost + 5) ⟨.eval target actual.inputs.environment.values, k, s⟩ ⟨.ret value, k, t⟩ := by
      rw [rows.down.1]
      exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have checked := LocalInputs.checkApplication?_iff_elaborates.mpr originalElab
    have typing := LocalInputs.checkApplication?_iff_hasType.mp ⟨target, checked⟩
    have _ := LocalInputs.checkApplication?_iff_elaborates.mp checked
    have _ := LocalInputs.checkApplication?_iff_hasType.mpr typing
    let cost := bodyCost + 5
    have completed := (LocalInputs.runApplication?_done_iff_of_cost typing costed (fuel := cost)).mpr (Nat.le_refl cost)
    have _ := LocalInputs.runApplication?_done_sound completed
    have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mp ⟨cost, completed⟩
    have _ := LocalInputs.runApplication?_done_iff_typed_evaluation.mpr ⟨typing, costed.erase⟩
    have _ := LocalInputs.runApplication?_runtime_done_sound runtimeTyped storeTyped completed
    have agreement : ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld t ∧
        Core.RuntimeValueHasType finalWorld value output := by
      obtain ⟨future, final, v, count, extension, typedStore, typedValue, evaluated, _⟩ :=
        LocalInputs.runApplication?_runtime_has_exact_cost typing runtimeTyped storeTyped ⟨value, t, costed.erase⟩
      obtain ⟨rfl, rfl, _⟩ := costed.deterministic evaluated
      exact ⟨future, extension, typedStore, typedValue⟩
    have _ := agreement
    check (decide (actual.inputs.checkApplication? returned = some (target, output) ∧
      actual.inputs.runApplication? 3 returned s = some (output, .outOfFuel
        ⟨.eval (.var 0) actual.inputs.environment.values, [.applyClosure argument.type output body captured], s⟩))) "actual caller checkpoint changed"
    for fuel in List.range (cost + 3) do
      have _ := LocalInputs.runApplication?_eq_none_iff (inputs := actual.inputs) (source := returned) fuel s
      have _ := LocalInputs.runApplication?_done_iff_of_cost typing costed (fuel := fuel)
      have _ := LocalInputs.runApplication?_outOfFuel_iff_of_cost typing costed (fuel := fuel)
      have _ := LocalInputs.runApplication?_runtime_never_faults runtimeTyped storeTyped returned fuel output
      have factored := (LocalInputs.runApplication?_eq_some_iff (fuel := fuel) (store := s)).mpr ⟨target, checked, rfl⟩
      have _ := LocalInputs.runApplication?_eq_some_iff.mp factored
      check (decide (actual.inputs.runApplication? fuel returned s =
        some (output, Core.runStateful fuel (.initial target actual.inputs.environment.values s)))) "full Core factorization changed"
      check ((actual.inputs.check? returned).isNone && (actual.inputs.run? fuel returned s).isNone &&
        (prepareRuntimeFunction? types owner source args).isNone && (runRuntimeFunction? types owner source args fuel s).isNone) "opt-in call entered old endpoints"
      match outcome : actual.inputs.runApplication? fuel returned s with
      | some (_, .done v final) =>
          check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "independent completion differs"
      | some (_, .outOfFuel checkpoint) =>
          have residual := LocalInputs.runApplication?_residual_of_outOfFuel costed outcome
          have _ := residual.2
          check (decide (fuel < cost ∧ Core.runStateful (cost - fuel) checkpoint = .done value t)) "actual residual differs"
          for additional in [0, 1, cost - fuel, cost + 2] do
            have _ := LocalInputs.runApplication?_resume outcome additional
            check (decide (actual.inputs.runApplication? (fuel + additional) returned s =
              some (output, Core.runStateful additional checkpoint))) "genuine full-result resume differs"
      | _ => throw (IO.userError "typed actual input failed or faulted")
    have _ := (manual []).runStateful_done_iff (fuel := cost)
    have _ := LocalInputs.runApplication?_done_iff_typed_cost.mp completed
    have _ := LocalInputs.runApplication?_done_iff_typed_cost.mpr ⟨typing, cost, costed, Nat.le_refl cost⟩
  else throw (IO.userError "independent exact call changed")
end LocalApplicationRunnerEntries
open LocalApplicationRunnerEntries
def frontendParsedLocalApplicationRunnerEntryTests : IO Unit := do
  for n in [0, 1, 4, 9] do
    for x in [9, 14] do
      execute ⟨.word, w x, .word⟩ .word (delayed n) [] [] [] [] (w x) (3 * n + 1)
        .word (.closure .nil (delayedTyped n .word [])) .nil (delayedPath n (w x) [] [])
  for current in [3, 17] do
    have st : Core.StoreHasTypes [.word] [w current] := by
      simpa only [Core.Store.allocate, List.nil_append, w] using
        (Core.StoreHasTypes.nil.allocate Core.CellPayload.word (Core.ValueHasType.word (value := Core.Word.ofNatModulo current)))
    execute ⟨.unit, .unit, .unit⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [.word] [w current] [w current] (w current) 3
      .unit (.closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))) st
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word, w 9, .word⟩ (.cell .word) (.newCell .word (.var 0)) [] [.word] [w current] [w current, w 9] (.cellRef .word 1) 3
      .word (.closure .nil (.newCell (.var rfl))) st
      (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] [] a.value 1
      (.closure .nil (.var rfl)) (.closure .nil (.var rfl)) .nil (fun _ => .cons (.var rfl) .refl)
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationRuntimeSafety
/-! Original parsed children, independent actual world/store witnesses, and
hand-built captured-body paths precede every runtime safety observation. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalApplicationRuntimeSafety
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def own : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RuntimeSafety",by decide⟩],by decide⟩⟩,17⟩
private def id (n : Nat) : Resolved.LocalId := ⟨own,n⟩
private def foreign : Resolved.LocalId := ⟨{own with declarationIndex := 2},999⟩
private def names : LocalNameTable := [("f",id 7),("f",id 91),("x",id 2),("c",foreign),("g",id 4)]
private def ctx (output : Core.Ty) : Resolved.Context :=
  [(id 2,.word),(id 7,.function .word output),(foreign,.bool),(id 4,.function .word output)]
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def env (f g : Core.Value) (x : Nat) (c : Bool) : Resolved.Environment :=
  [(id 2,w x),(id 7,f),(foreign,.bool c),(id 4,g)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main,"runtime-safety.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original expression did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩)) "original complete byte range changed"
  return source
private structure Child (context : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers context.ids resolved core
  typing : Resolved.HasType context resolved type
private def child (context : Resolved.Context) (source : Syntax.Expr) : IO (Child context source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match typed : context.lookup? localId, indexed : Resolved.LocalScope.index? context.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_,.group inner⟩ =>
      let a ← child context inner
      return ⟨a.resolved,a.core,a.type,by rw [original]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child context condition; let a ← child context yes; let b ← child context no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "whole guard is not Bool")
  | _ => throw (IO.userError "outside independent child certificate")
termination_by sizeOf source
private structure Application (context : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates names context source core type
private def application (context : Resolved.Context) (source : Syntax.Expr) : IO (Application context source) := do
  match original : source with
  | ⟨_,.call callee ⟨span,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains span && span.contains argument.span &&
        decide (callee.span.endByte ≤ span.startByte)) "original call ranges/order changed"
      let f ← child context callee; let a ← child context argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,by
            rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "argument type differs")
      | _ => throw (IO.userError "callee is not Function")
  | _ => throw (IO.userError "not exactly one original argument")
private structure Raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : LocalExpressionEvaluatesWithCost names environment s source value s cost
private def raw (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Raw environment s source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : environment.lookup? localId with
          | some value => return ⟨value,1,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_,.group inner⟩ =>
      let a ← raw environment s inner
      return ⟨a.value,a.cost,by rw [original]; exact .group a.evidence⟩
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← raw environment s condition
      match cv : c.value with
      | .bool true =>
          let a ← raw environment s yes
          return ⟨a.value,c.cost+a.cost+2,by rw [original]; exact .ifTrue (cv ▸ c.evidence) a.evidence⟩
      | .bool false =>
          let b ← raw environment s no
          return ⟨b.value,c.cost+b.cost+2,by rw [original]; exact .ifFalse (cv ▸ c.evidence) b.evidence⟩
      | _ => throw (IO.userError "actual guard is not Bool")
  | _ => throw (IO.userError "selected unsupported child")
termination_by sizeOf source
private def readBody : Core.Expr := .loadCell (.var 1)
private def writeBody : Core.Expr := .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))
private def reader : Core.Value := .closure .word .word readBody [.cellRef .word 0]
private def writer : Core.Value := .closure .word .word writeBody [.cellRef .word 0]
private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private structure Body (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  path : ∀ k, Core.Steps cost ⟨.eval body actual,k,s⟩ ⟨.ret value,k,final⟩
private def bodyPath (body : Core.Expr) (actual : Core.Environment) (s : Core.Store) : IO (Body body actual s) := do
  match original : body, values : actual, store : s with
  | .loadCell (.var 1),arg :: .cellRef .word 0 :: [],[old] => return ⟨old,s,3,by
      intro k; rw [original,values]; exact .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell (by rw [store]; rfl)) .refl))⟩
  | .letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2)),arg :: .cellRef .word 0 :: [],[old] => return ⟨arg,[arg],10,by
      intro k; rw [original,values,store]
      exact .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet
        (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))))))))⟩
  | .newCell .word (.var 0),arg :: [],_ => return ⟨.cellRef .word s.length,s ++ [arg],3,by
      intro k; rw [original,values]; exact .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))⟩
  | _,_,_ => throw (IO.userError "outside independent actual body path")
private structure Counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : LocalFunctionApplicationEvaluatesWithCost names environment s source value final cost
private def counted (environment : Resolved.Environment) (s : Core.Store) (source : Syntax.Expr) : IO (Counted environment s source) := do
  match original : source with
  | ⟨_,.call callee ⟨_,[argument]⟩⟩ =>
      let f ← raw environment s callee; let a ← raw environment s argument
      match shape : f.value with
      | .closure _ _ body captured =>
          let b ← bodyPath body (a.value :: captured) s
          return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,by rw [original]; exact .call (shape ▸ f.evidence) a.evidence (b.path [])⟩
      | _ => throw (IO.userError "actual callee is not a closure")
  | _ => throw (IO.userError "not a single argument call")
private theorem storeTyped (n : Nat) : Core.StoreHasTypes [.word] [w n] :=
  Core.StoreHasTypes.nil.allocate .word .word
private theorem readerTyped : Core.RuntimeValueHasType [.word] reader (.function .word .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
private theorem writerTyped : Core.RuntimeValueHasType [.word] writer (.function .word .word) :=
  .closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))
private def verify (text : String) (output : Core.Ty) (f g : Core.Value) (x : Nat) (c : Bool)
    (expected : Core.Expr) (value : Core.Value) (cost : Nat) (s final : Core.Store)
    (world : Core.StoreTyping) (et : Core.RuntimeEnvironmentHasTypes world (env f g x c).values (ctx output).values)
    (st : Core.StoreHasTypes world s) : IO Unit := do
  let source ← parsed text
  let original ← application (ctx output) source
  let actual ← counted (env f g x c) s source
  if exactStatic : original.core = expected ∧ original.type = output then
    if exactRaw : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have elaboration : LocalFunctionApplicationElaborates names (ctx output) source expected output := by
        simpa only [exactStatic.1,exactStatic.2] using original.evidence
      have evaluation : LocalFunctionApplicationEvaluatesWithCost names (env f g x c) s source value final cost := by
        simpa only [exactRaw.1,exactRaw.2.1,exactRaw.2.2] using actual.evidence
      have aligned : (env f g x c).ids = (ctx output).ids := rfl
      have _ := evaluation.erase.preserves_runtime_type elaboration aligned et st
      have _ := elaboration.hasType.runtime_evaluates aligned et st ⟨value, final, evaluation.erase⟩
      have identified : ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld final ∧
          Core.RuntimeValueHasType finalWorld value output := by
        obtain ⟨fw,fs,v,n,ext,typed,vt,e,_,_⟩ := elaboration.runtime_typed_execution aligned et st ⟨value, final, evaluation.erase⟩
        obtain ⟨rfl,rfl,rfl⟩ := e.deterministic evaluation
        exact ⟨fw,ext,typed,vt⟩
      let path := evaluation.toSteps elaboration aligned
      have kt : Core.ContinuationHasType world [.pairApply (w 7)] output (.product .word output) := .cons (.pairApply .word) .nil
      have _ := elaboration.runtime_state_hasType et st kt
      check (decide (Core.runStateful cost ⟨.eval expected (env f g x c).values,[.pairApply (w 7)],s⟩ =
        .outOfFuel ⟨.ret value,[.pairApply (w 7)],final⟩)) "typed endpoint was confused with closed completion"
      for fuel in List.range (cost+3) do
        have _ := elaboration.runtime_run_never_faults et st kt fuel (.expectedCell value) (.final value final)
        check (match completed : Core.runStateful fuel (.initial expected (env f g x c).values s) with
          | .done v t => decide (cost ≤ fuel ∧ v = value ∧ t = final)
          | .outOfFuel _ => decide (fuel < cost)
          | _ => false) "actual closed typed execution threshold changed"
        match completed : Core.runStateful fuel (.initial expected (env f g x c).values s) with
        | .done v t =>
            have _ := elaborateLocalFunctionApplication?_runtime_run_done_sound elaboration.complete aligned et st completed
            pure ()
        | _ => pure ()
      for spent in List.range (cost+1) do
        match stopped : Core.runStateful spent ⟨.eval expected (env f g x c).values,[.pairApply (w 7)],s⟩ with
        | .outOfFuel checkpoint =>
            have _ := elaboration.runtime_checkpoint_hasType et st kt stopped
            have _ := elaboration.runtime_checkpoint_never_faults et st kt stopped (cost+1-spent) (.expectedCell value) checkpoint
            have _ := Core.runStateful_resume stopped (cost+1-spent)
            check (decide (Core.runStateful (cost+1-spent) checkpoint = .done (.pair (w 7) value) final)) "typed actual continuation/checkpoint changed"
        | _ => throw (IO.userError "typed continuation checkpoint missing")
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial expected (env f g x c).values s) with
        | .outOfFuel checkpoint =>
            have _ := path.residual_of_outOfFuel stopped
            check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "closed exact residual changed"
        | _ => throw (IO.userError "genuine closed checkpoint missing")
      check (decide (elaborateLocalExpression? names (ctx output) source = none)) "old pure expression gate changed"
    else throw (IO.userError "independent raw value/store/cost changed")
  else throw (IO.userError "independent original Core/type changed")
private def mixed : Core.Expr := .apply (.ifE (.var 2) (.var 1) (.var 3)) (.var 0)
private def selected : IO Unit := do
  let source ← parsed "(c ? f : g)(x)"
  match source.value with
  | .call callee ⟨span,[argument]⟩ => check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 11 ∧
      span.startByte = 11 ∧ span.endByte = 14 ∧ argument.span.startByte = 12 ∧ argument.span.endByte = 13)) "original child byte ranges changed"
  | _ => throw (IO.userError "original root call changed")
  for x in [14,9] do
    for old in [23,91] do
      for c in [true,false] do
        let actual := env reader writer x c
        have et : Core.RuntimeEnvironmentHasTypes [.word] actual.values (ctx .word).values :=
          .cons .word (.cons readerTyped (.cons .bool (.cons writerTyped .nil)))
        verify "(c ? f : g)(x)" .word reader writer x c mixed (w (if c then old else x)) (if c then 11 else 18)
          [w old] (if c then [w old] else [w x]) [.word] et (storeTyped old)
        if !c then
          check (decide (Core.runStateful 14 (.initial mixed actual.values [w old]) =
            .outOfFuel ⟨.ret .unit,[.letBody (.loadCell (.var 2)) [w x,.cellRef .word 0]],[w x]⟩)) "actual updated store/captured environment at cp14 changed"
          check (decide (Core.runStateful 15 (.initial mixed actual.values [w old]) =
            .outOfFuel ⟨.eval (.loadCell (.var 2)) [.unit,w x,.cellRef .word 0],[],[w x]⟩)) "post-let reread did not retain original reference"
private def allocation : IO Unit := do
  for old in [23,91] do
    have ft : Core.RuntimeValueHasType [.word] allocator (.function .word (.cell .word)) := .closure .nil (.newCell (.var rfl))
    have et : Core.RuntimeEnvironmentHasTypes [.word] (env allocator allocator 14 true).values (ctx (.cell .word)).values :=
      .cons .word (.cons ft (.cons .bool (.cons ft .nil)))
    have _ : Core.StoreHasTypes [.word,.word] [w old,w 14] := (storeTyped old).allocate .word .word
    have _ : Core.RuntimeValueHasType [.word,.word] (.cellRef .word 1) (.cell .word) := .cellRef rfl
    verify "f(x)" (.cell .word) allocator allocator 14 true (.apply (.var 1) (.var 0)) (.cellRef .word 1) 8
      [w old] [w old,w 14] [.word] et (storeTyped old)
private def boundaries : IO Unit := do
  have _ : Core.ValueHasType reader (.function .word .word) := readerTyped.erase
  have _ : Core.RuntimeEnvironmentHasTypes [.word] (env reader writer 14 true).values (ctx .word).values :=
    .cons .word (.cons readerTyped (.cons .bool (.cons writerTyped .nil)))
  have _ : ¬ Core.RuntimeValueHasType [] (.cellRef .word 0) (.cell .word) := by intro h; cases h; contradiction
  have _ : ¬ Core.RuntimeValueHasType [.bool] (.cellRef .word 0) (.cell .word) := by intro h; cases h; contradiction
  have _ : ¬ Core.StoreHasTypes [.word] [] := by intro h; have := h.length_eq; contradiction
  have _ : ¬ Core.StoreHasTypes [.word] [.bool true] := by
    intro h; obtain ⟨v,found,_,typed⟩ := h.read (location := 0) rfl
    have eq : v = .bool true := (Option.some.inj found).symm
    subst v; cases typed
  check (decide (Core.runStateful 10 (.initial mixed (env reader writer 14 true).values []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩)) "runtime typed reference fabricated allocated storage"
  check (decide (Core.runStateful 11 (.initial mixed (env reader writer 14 true).values [.bool true]) =
    .done (.bool true) [.bool true])) "equal store lengths fabricated payload typing"
  check (decide (Core.runStateful 11 ⟨.eval mixed (env reader writer 14 true).values,[.loadCellApply],[w 23]⟩ =
    .fault (.expectedCell (w 23)) ⟨.ret (w 23),[.loadCellApply],[w 23]⟩)) "untyped pending continuation was declared safe"
  let source ← parsed "(c ? f : missing)(x)"
  let actual ← counted (env reader writer 14 true) [w 23] source
  check (decide (actual.value = w 23 ∧ actual.final = [w 23] ∧ actual.cost = 11 ∧
    elaborateLocalFunctionApplication? names (ctx .word) source = none)) "raw selected success bypassed whole static typing"
  have _ := actual.evidence.erase
  pure ()
end ParsedLocalApplicationRuntimeSafety
open ParsedLocalApplicationRuntimeSafety
def frontendParsedLocalApplicationRuntimeSafetyTests : IO Unit := do
  selected; allocation; boundaries
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalApplicationRuntimeSafetyEntries
/-! The original parameter binding is checked against an actual runtime world.
Typed stores and typed outer frames justify safety, not structural values alone. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalApplicationRuntimeSafetyEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"SafeActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "runtime-safe-local-call.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Declared (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declare (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) : IO (Declared types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "outside parameter fixture")
private structure Bound (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def bindArgs (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Bound types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original, actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: remaining =>
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← bindArgs types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest remaining
          return ⟨tail.inputs, by rw [original, actual]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate actual parameter")
      else throw (IO.userError "actual type differs")
  | _, _ => throw (IO.userError "actual arity differs")
private structure Reference (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.context.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def reference (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Reference s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Call (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private structure OriginalCall (source : Syntax.Expr) where
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : source = ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩
private def callShape (source : Syntax.Expr) : IO (OriginalCall source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ => return ⟨span, argumentsSpan, callee, argument, original⟩
  | _ => throw (IO.userError "not original singleton call")
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Call s source) := do
  let original ← callShape source
  let span := original.span; let argumentsSpan := original.argumentsSpan
  let callee := original.callee; let argument := original.argument
  check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
    decide (callee.span.endByte ≤ argumentsSpan.startByte)) "call child ranges/order changed"
  let f ← reference s callee; let a ← reference s argument
  match shape : f.type with
  | .function input output =>
      if same : a.type = input then
        return ⟨.apply f.core a.core, output, by
          rw [original.shape]
          exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
      else throw (IO.userError "argument type differs")
  | _ => throw (IO.userError "callee not Function")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output)]
private def staticCase (input output : Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed; let types := table input output
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = [("x", ⟨owner, 1⟩), ("f", ⟨owner, 0⟩)] ∧
    ps.inputs.context.values = [input, .function input output])) "parameter-only static layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "return range changed"
  let a ← application ps.inputs returned
  check (decide (a.core = target ∧ a.type = output ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (target, output) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent original call differs"
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature output := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "header policy changed")
      else throw (IO.userError "return type differs")
  | _ => throw (IO.userError "return clause differs")
  check ((compileRuntimeFunction? types owner source).isNone) "source call entered old compilation"
  return (source, ps.inputs)
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row value changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (world : Core.StoreTyping) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (argumentTyped : Core.RuntimeValueHasType world argument.value argument.type)
    (closureTyped : Core.RuntimeValueHasType world (.closure argument.type output body captured) (.function argument.type output))
    (storeTyped : Core.StoreHasTypes world s)
    (bodyEvaluation : Core.Evaluates (argument.value :: captured) s body value t)
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩)
    (k : List Core.Frame) (resultType : Core.Ty) (continuationTyped : Core.ContinuationHasType world k output resultType)
    (afterCost : Nat) (result : Core.Value)
    (afterPath : Core.Steps afterCost ⟨.ret value, k, t⟩ (.final result t)) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped.erase⟩
  let args := [f, argument]; let types := table argument.type output
  let (source, statics) ← staticCase argument.type output
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.context = statics.context ∧
    actual.inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "original actual parameter records differ"
  let rows : PLift (actual.inputs.environment.values = (args.map (·.value)).reverse ∧
      actual.inputs.context.values = [argument.type, f.type]) ←
    if same : actual.inputs.environment.values = (args.map (·.value)).reverse ∧
        actual.inputs.context.values = [argument.type, f.type] then pure ⟨same⟩
    else throw (IO.userError "original projections lost their order")
  have runtimeTyped : Core.RuntimeEnvironmentHasTypes world actual.inputs.environment.values actual.inputs.context.values := by
    rw [rows.down.1, rows.down.2]; exact .cons argumentTyped (.cons closureTyped .nil)
  let ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "original return changed")
  let call ← application actual.inputs.toTypeInputs returned
  if acceptedCore : call.core = target ∧ call.type = output then
    have elaboration : LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context returned target output := by
      simpa only [acceptedCore.1, acceptedCore.2, LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using call.evidence
    let original ← callShape returned
    have elaboration := Eq.mp (congrArg (fun src =>
      LocalFunctionApplicationElaborates actual.inputs.names actual.inputs.context src target output) original.shape) elaboration
    let fp ← observed actual.inputs original.callee f.value
    let ap ← observed actual.inputs original.argument argument.value
    have raw := LocalFunctionApplicationEvaluates.call (span := original.span) (argumentsSpan := original.argumentsSpan)
      (fp.evidence s).erase (ap.evidence s).erase bodyEvaluation
    have costed := LocalFunctionApplicationEvaluatesWithCost.call (span := original.span) (argumentsSpan := original.argumentsSpan)
      (fp.evidence s) (ap.evidence s) (bodyPath [])
    have manual (continuation) : Core.Steps (bodyCost + 5)
        ⟨.eval target actual.inputs.environment.values, continuation, s⟩ ⟨.ret value, continuation, t⟩ := by
      rw [rows.down.1]
      exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath continuation)))))
    have _ := raw.preserves_runtime_type elaboration actual.inputs.sameIds runtimeTyped storeTyped
    have _ := elaboration.hasType.runtime_evaluates actual.inputs.sameIds runtimeTyped storeTyped ⟨value, t, raw⟩
    have agreement : ∃ finalWorld, Core.WorldExtends world finalWorld ∧ Core.RuntimeStoreHasTypes finalWorld t ∧
        Core.RuntimeValueHasType finalWorld value output ∧ finalWorld.length = t.length := by
      obtain ⟨future, final, v, count, extension, typedStore, typedValue, evaluation, _⟩ :=
        elaboration.runtime_typed_execution actual.inputs.sameIds runtimeTyped storeTyped ⟨value, t, raw⟩
      obtain ⟨rfl, rfl, _⟩ := costed.deterministic evaluation
      exact ⟨future, extension, typedStore, typedValue, typedStore.length_eq⟩
    have _ := agreement
    have _ := elaboration.runtime_state_hasType runtimeTyped storeTyped continuationTyped
    let cost := bodyCost + 5
    for fuel in List.range (cost + afterCost + 3) do
      have _ := elaboration.runtime_run_never_faults runtimeTyped storeTyped continuationTyped fuel
      have _ := elaboration.runtime_run_never_faults runtimeTyped storeTyped (.nil : Core.ContinuationHasType world [] output output) fuel
      check ((prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone) "runtime-world proofs leaked into old entry"
      match done : Core.runStateful fuel (.initial target actual.inputs.environment.values s) with
      | .done v final =>
          have _ := elaborateLocalFunctionApplication?_runtime_run_done_sound elaboration.complete actual.inputs.sameIds runtimeTyped storeTyped done
          check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "closed runtime-safe call differs"
      | .outOfFuel _ => check (decide (fuel < cost)) "closed exact cost differs"
      | .fault .. => throw (IO.userError "runtime-world typed closed call faulted")
      check (match Core.runStateful fuel ⟨.eval target actual.inputs.environment.values, k, s⟩ with
        | .done v final => decide (cost + afterCost ≤ fuel ∧ v = result ∧ final = t)
        | .outOfFuel _ => decide (fuel < cost + afterCost)
        | .fault .. => false) "typed pending continuation differs"
    have _ := (manual k).trans afterPath
    check (decide (Core.runStateful cost ⟨.eval target actual.inputs.environment.values, k, s⟩ =
      .outOfFuel ⟨.ret value, k, t⟩)) "typed continuation did not retain actual final store"
    for spent in List.range (cost + afterCost) do
      match exhausted : Core.runStateful spent ⟨.eval target actual.inputs.environment.values, k, s⟩ with
      | .outOfFuel checkpoint =>
          have _ := elaboration.runtime_checkpoint_hasType runtimeTyped storeTyped continuationTyped exhausted
          for additional in [0, 1, cost + afterCost - spent, cost + afterCost + 2] do
            have _ := elaboration.runtime_checkpoint_never_faults runtimeTyped storeTyped continuationTyped exhausted additional
            have _ := Core.runStateful_resume exhausted additional
            check (decide (Core.runStateful additional checkpoint = Core.runStateful (spent + additional)
              ⟨.eval target actual.inputs.environment.values, k, s⟩)) "genuine typed checkpoint changed on resume"
          check (decide (Core.runStateful (cost + afterCost - spent) checkpoint = .done result t)) "typed residual did not complete"
      | _ => throw (IO.userError "genuine typed checkpoint missing")
  else throw (IO.userError "independent original call Core/type changed")
end LocalApplicationRuntimeSafetyEntries
open LocalApplicationRuntimeSafetyEntries
def frontendParsedLocalApplicationRuntimeSafetyEntryTests : IO Unit := do
  for x in [9, 14] do
    execute ⟨.word, w x, .word⟩ (.cell .word) (.newCell .word (.var 0)) [] [] [] [w x] (.cellRef .word 0) 3
      .word (.closure .nil (.newCell (.var rfl))) .nil (.newCell (.var rfl))
      (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
      [.loadCellApply] .word (.cons .loadCellApply .nil) 1 (w x) (.cons (.applyLoadCell rfl) .refl)
  for current in [3, 17] do
    have storeTyped : Core.StoreHasTypes [.word] [w current] := by
      simpa only [Core.Store.allocate, List.nil_append, w] using
        (Core.StoreHasTypes.nil.allocate Core.CellPayload.word (Core.ValueHasType.word (value := Core.Word.ofNatModulo current)))
    execute ⟨.unit, .unit, .unit⟩ (.cell .word) (.newCell .word (.loadCell (.var 1))) [.cellRef .word 0]
      [.word] [w current] [w current, w current] (.cellRef .word 1) 5
      .unit (.closure (.cons (.cellRef rfl) .nil) (.newCell (.loadCell (.var rfl)))) storeTyped
      (.newCell (.loadCell (.var rfl) rfl))
      (fun _ => .cons .enterNewCell (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) (.cons .applyNewCell .refl)))))
      [.loadCellApply] .word (.cons .loadCellApply .nil) 1 (w current) (.cons (.applyLoadCell rfl) .refl)
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let argument : TypedRuntimeArgument := ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
    execute argument argument.type (.var 0) [] [] [] [] argument.value 1
      (.closure .nil (.var rfl)) (.closure .nil (.var rfl)) .nil (.var rfl) (fun _ => .cons (.var rfl) .refl)
      [.letBody .unit []] .unit (.cons (.letBody .nil .unit) .nil) 2 .unit (.cons .bindLet (.cons .unit .refl))
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalComputation
/-! Original parsed children supply independent exact static and raw evidence.
Manual Core paths, not checker outputs, fix each runtime value and cost. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputation
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Computation", by decide⟩], by decide⟩⟩, 50⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def fid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 302⟩
private def names : LocalNameTable := [("x", id 7), ("f", fid), ("c", id 14), ("y", id 9), ("f", id 88)]
private def context (a b : Core.Ty) : Resolved.Context :=
  [(id 7, a), (fid, .function a b), (id 14, .bool), (id 9, a), (fid, .bool)]
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) [.bool true]
private def environment (type : Core.Ty) (x y : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 7, x), (fid, identity type), (id 14, .bool choice), (id 9, y), (fid, .bool false)]
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-computation.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"original expression did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) s!"original complete span changed: {text}"
  return source
private structure Pure (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def pureChild (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Pure ctx source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _, _ => throw (IO.userError "original context missing")
      | none => throw (IO.userError "original name missing")
  | ⟨_, .group inner⟩ =>
      let a ← pureChild ctx inner
      return ⟨a.resolved, a.core, a.type, by rw [original]; exact .group a.resolution, a.lowered, a.typing⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, by rw [original]; exact .unit, .unit, .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← pureChild ctx left; let b ← pureChild ctx right
      if ta : a.type = .word then
        if bt : b.type = .word then return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
          by rw [original]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
          .binary (show Resolved.HasType ctx a.resolved .word from ta ▸ a.typing)
            (show Resolved.HasType ctx b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right Word mismatch")
      else throw (IO.userError "left Word mismatch")
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← pureChild ctx condition; let a ← pureChild ctx yes; let b ← pureChild ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved, .ifE c.core a.core b.core, a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered, .ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole arms differ")
      else throw (IO.userError "guard mismatch")
  | _ => throw (IO.userError "outside pure certificate")
termination_by sizeOf source
private structure Static (ctx : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationElaborates names ctx source core type
  typing : LocalComputationHasType names ctx source type
private def staticChild (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Static ctx source) := do
  match original : source with
  | ⟨_, .call callee ⟨argsSpan, [argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argsSpan && argsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argsSpan.startByte)) "original call delimiter/order changed"
      let f ← pureChild ctx callee; let a ← pureChild ctx argument
      match shape : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core, output,
            by rw [original]; exact .application (.call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
            by rw [original]; exact .application (.call (f.resolution.reflects_type (shape ▸ f.typing)) (a.resolution.reflects_type (same ▸ a.typing)))⟩
          else throw (IO.userError "argument mismatch")
      | _ => throw (IO.userError "callee not Function")
  | _ =>
      let p ← pureChild ctx source
      return ⟨p.core, p.type, .pure p.resolution p.lowered p.typing, .pure (p.resolution.reflects_type p.typing)⟩
private def staticCheck (input output : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (application : Bool) : IO Unit := do
  let source ← parsed text; let ctx := context input output; let p ← staticChild ctx source
  have _ := elaborateLocalComputation?_iff.mp (elaborateLocalComputation?_iff.mpr p.elaboration)
  have _ := localComputationHasType_iff_elaborates.mp p.typing
  have _ := localComputationHasType_iff_elaborates.mpr ⟨p.core, p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core = core ∧ p.type = type ∧ elaborateLocalComputation? names ctx source = some (core, type) ∧
    elaborateLocalExpression? names ctx source = (if application then none else some (core, type)) ∧
    elaborateLocalFunctionApplication? names ctx source = (if application then some (core, type) else none) ∧
    names.lookup? "f" = some fid ∧ ctx.lookup? fid = some (.function input output))) "exact static union or old boundary differs"
private structure PureCost (env : Resolved.Environment) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalExpressionEvaluatesWithCost names env store source value store cost
private def pureCost (env : Resolved.Environment) (source : Syntax.Expr) : IO (PureCost env source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : env.lookup? localId with
          | some value => return ⟨value, 1, fun _ => by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | none => throw (IO.userError "actual value missing")
      | none => throw (IO.userError "actual name missing")
  | ⟨_, .group inner⟩ =>
      let a ← pureCost env inner
      return ⟨a.value, a.cost, fun s => by rw [original]; exact .group (a.evidence s)⟩
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, 1, fun _ => by rw [original]; exact .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← pureCost env left; let b ← pureCost env right
      return ⟨.pair a.value b.value, a.cost+b.cost+3, fun s => by rw [original]; exact .pair (a.evidence s) (b.evidence s)⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← pureCost env left; let b ← pureCost env right
      match av : a.value, bv : b.value with
      | .word x, .word y => return ⟨.word (x.sub y), a.cost+b.cost+3,
          fun s => by rw [original]; exact .subtract (av ▸ a.evidence s) (bv ▸ b.evidence s)⟩
      | _, _ => throw (IO.userError "raw subtraction needs Words")
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← pureCost env condition
      match selected : c.value with
      | .bool true =>
          let a ← pureCost env yes
          return ⟨a.value, c.cost+a.cost+2, fun s => by rw [original]; exact .ifTrue (selected ▸ c.evidence s) (a.evidence s)⟩
      | .bool false =>
          let b ← pureCost env no
          return ⟨b.value, c.cost+b.cost+2, fun s => by rw [original]; exact .ifFalse (selected ▸ c.evidence s) (b.evidence s)⟩
      | _ => throw (IO.userError "raw guard needs Bool")
  | _ => throw (IO.userError "outside independent raw fixture")
termination_by sizeOf source
private structure Actual (env : Resolved.Environment) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  raw : ∀ store, LocalComputationEvaluates names env store source value store
  costed : ∀ store, LocalComputationEvaluatesWithCost names env store source value store cost
private def actual (env : Resolved.Environment) (source : Syntax.Expr) : IO (Actual env source) := do
  match original : source with
  | ⟨_, .call callee ⟨_, [argument]⟩⟩ =>
      let f ← pureCost env callee; let a ← pureCost env argument
      match shape : f.value with
      | .closure _ _ (.var 0) _ => return ⟨a.value, f.cost+a.cost+1+3,
          fun s => by rw [original]; exact .application (.call (shape ▸ (f.evidence s).erase) (a.evidence s).erase (.var rfl)),
          fun s => by rw [original]; exact .application (.call (shape ▸ f.evidence s) (a.evidence s) (.cons (.var rfl) .refl))⟩
      | _ => throw (IO.userError "not the independently supplied identity body")
  | _ =>
      let p ← pureCost env source
      return ⟨p.value, p.cost, fun s => .pure (p.evidence s).erase, fun s => .pure (p.evidence s)⟩
private def exercise (type : Core.Ty) (x y : Core.Value) (choice : Bool) (text : String)
    (core : Core.Expr) (resultType : Core.Ty) (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (environment type x y choice).values, k, store⟩ ⟨.ret value, k, store⟩) : IO Unit := do
  let source ← parsed text; let ctx := context type type; let env := environment type x y choice
  let p ← staticChild ctx source; let r ← actual env source
  if exactResult : p.core = core ∧ p.type = resultType ∧ r.value = value ∧ r.cost = cost then
    have e : LocalComputationElaborates names ctx source core resultType := by simpa only [exactResult.1, exactResult.2.1] using p.elaboration
    have ids : env.ids = ctx.ids := rfl
    for store in [[], [.bool true, .word (Core.Word.ofNatModulo 71)]] do
      have raw : LocalComputationEvaluates names env store source value store := exactResult.2.2.1 ▸ r.raw store
      have counted : LocalComputationEvaluatesWithCost names env store source value store cost := by
        simpa only [exactResult.2.2.1, exactResult.2.2.2] using r.costed store
      have _ := localComputationEvaluates_iff_exists_cost.mp raw
      have _ := localComputationEvaluates_iff_exists_cost.mpr ⟨cost, counted⟩
      have coreRaw := (e.evaluates_iff ids).mp raw
      have _ := (e.evaluates_iff ids).mpr coreRaw
      have _ := counted.deterministic ((e.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (e.evaluatesWithCost_iff_steps ids).mp counted
      let pending : List Core.Frame := [.letBody .unit []]
      have _ := counted.toStepsWithContinuation e ids pending
      for cutoff in [0, 2] do
        let leading := env.values.take cutoff; let suffix := env.values.drop cutoff
        have same : leading ++ suffix = env.values := List.take_append_drop cutoff env.values
        let leftTypes := ctx.values.take cutoff; let rightTypes := ctx.values.drop cutoff
        for insertedType in [Core.Ty.namedData ⟨999⟩, .function (.namedData ⟨7⟩) (.namedData ⟨8⟩)] do
          have typed : Core.HasType (leftTypes ++ rightTypes) core resultType := by simpa only [leftTypes, rightTypes, List.take_append_drop] using e.core_hasType
          have added := (e.core_hasType_insert_iff leftTypes rightTypes insertedType).mpr typed
          have _ := (e.core_hasType_insert_iff leftTypes rightTypes insertedType).mp added
        for inserted in [Core.Value.cellRef .word 99, .closure .bool .word (.var 19) [.unit], .bool false] do
          have originalRaw : Core.Evaluates (leading ++ suffix) store core value store := by rw [same]; exact coreRaw
          have changed := (e.core_evaluates_insert_iff leading suffix inserted).mpr originalRaw
          have _ := (e.core_evaluates_insert_iff leading suffix inserted).mp changed
          have paired : ∀ k, Core.Steps cost ⟨.eval core (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
              Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
            obtain ⟨n, paths⟩ := e.core_insertion_paths leading suffix inserted originalRaw
            have count : n = cost := ((paths []).1.final_unique (by simpa only [same, env, Core.State.final] using manual store [])).1
            exact count ▸ paths
          for fuel in List.range (cost+2) do
            have _ := (paired []).2.runStateful_done_iff (fuel := fuel)
            match Core.runStateful fuel (.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix) store) with
            | .done v s => check (decide (cost ≤ fuel ∧ v = value ∧ s = store)) "manual value/store/cost differs"
            | .outOfFuel _ => check (decide (fuel < cost)) "exact threshold differs"
            | .fault _ _ => throw (IO.userError "unused inserted value executed")
          check (decide (Core.runStateful cost ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), pending, store⟩ =
            .outOfFuel ⟨.ret value, pending, store⟩)) "pending endpoint was treated as final"
  else throw (IO.userError "independent static/raw expected result differs")
end ParsedLocalComputation
open ParsedLocalComputation
def frontendParsedLocalComputationTests : IO Unit := do
  for a in [Core.Ty.unit, .word, .namedData ⟨7⟩, .function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.bool, .unit, .namedData ⟨11⟩] do
      staticCheck a b "x" (.var 0) a false
      staticCheck a b "((x))" (.var 0) a false
      staticCheck a b "()" .unit .unit false
      staticCheck a b "(x,())" (.pair (.var 0) .unit) (.product a .unit) false
      staticCheck a b "c ? x : y" (.ifE (.var 2) (.var 0) (.var 3)) a false
      for text in ["f(x)", "((f))(((x)))"] do staticCheck a b text (.apply (.var 1) (.var 0)) b true
      staticCheck a b "(c ? f : f)(c ? x : y)" (.apply (.ifE (.var 2) (.var 1) (.var 1)) (.ifE (.var 2) (.var 0) (.var 3))) b true
  staticCheck .word .word "x - y" (.binary .wordSub (.var 0) (.var 3)) .word false
  for (type, x, y) in [(Core.Ty.unit, Core.Value.unit, Core.Value.unit),
      (.word, .word (Core.Word.ofNatModulo 17), .word (Core.Word.ofNatModulo 5))] do
    for choice in [false, true] do
      exercise type x y choice "x" (.var 0) type x 1 (fun _ _ => .cons (.var rfl) .refl)
      exercise type x y choice "()" .unit .unit .unit 1 (fun _ _ => .cons .unit .refl)
      exercise type x y choice "(x,())" (.pair (.var 0) .unit) (.product type .unit) (.pair x .unit) 5
        (fun _ _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons .unit (.cons .applyPair .refl)))))
      exercise type x y choice "c ? x : y" (.ifE (.var 2) (.var 0) (.var 3)) type (if choice then x else y) 4
        (by
          intro s k
          cases choice with
          | false => exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
          | true => exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl))))
      for text in ["f(x)", "((f))(((x)))"] do
        exercise type x y choice text (.apply (.var 1) (.var 0)) type x 6
          (fun _ _ => .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (.cons (.var rfl) .refl))))))
      exercise type x y choice "(c ? f : f)(c ? x : y)" (.apply (.ifE (.var 2) (.var 1) (.var 1)) (.ifE (.var 2) (.var 0) (.var 3)))
        type (if choice then x else y) 12 (by
          intro s k
          cases choice <;> apply CostStepComposition.apply (functionCost := 4) (argumentCost := 4) (bodyCost := 1)
          all_goals
            first
            | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl))))
  exercise .word (.word (Core.Word.ofNatModulo 17)) (.word (Core.Word.ofNatModulo 5)) true "x - y"
    (.binary .wordSub (.var 0) (.var 3)) .word (.word (Core.Word.ofNatModulo 12)) 5
    (fun _ _ => .cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons (.var rfl) (.cons (.applyBinary rfl) .refl)))))
  for text in ["f(f(x))", "(f(x))", "x + f(x)", "(lam(z: Word){return z;})(x)"] do
    let source ← parsed text
    check (decide (elaborateLocalComputation? names (context .word .word) source = none)) "union became a recursive expression profile"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalComputationEntries
/-! Original declarations retain their two existing entry profiles. The shared
child does not introduce a mixed body or a new function endpoint. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "application-return-entry.sol"⟩, text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside annotation fixture")
private structure Parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner .empty params statics
  bound : RuntimeParametersBindFrom types owner .empty params args actual
private def parameters (types : TypeNameTable) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Parameters types params args) := do
  match original : params, supplied : args with
  | [⟨s, .typed none f ft⟩, ⟨t, .typed none x xt⟩], [fv, xv] =>
      check (s.contains f.span && s.contains ft.span && t.contains x.span && t.contains xt.span &&
        decide (s.endByte ≤ t.startByte)) "original parameter spans/order changed"
      let fm ← meaning types ft; let xm ← meaning types xt
      if sameF : fm.type = fv.type then
        if sameX : xm.type = xv.type then
          if unused : x.value ∉ [f.value] then
            return ⟨(LocalTypeInputs.empty.bindFresh owner f.value fv.type).bindFresh owner x.value xv.type,
              (LocalInputs.empty.bindFresh owner f.value fv.type fv.value fv.valueTyped).bindFresh owner x.value xv.type xv.value xv.valueTyped,
              by
                rw [original]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalTypeInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil),
              by
                rw [original, supplied]
                exact .cons (sameF ▸ fm.evidence) (by simp [LocalInputs.empty_names])
                  (.cons (sameX ▸ xm.evidence) unused .nil)⟩
          else throw (IO.userError "duplicate parameter")
        else throw (IO.userError "argument type differs")
      else throw (IO.userError "function type differs")
  | _, _ => throw (IO.userError "original parameter shape or actual arity changed")
private structure Reference (inputs : LocalInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression inputs.names source resolved
  lowered : Resolved.Lowers inputs.context.ids resolved core
  typing : Resolved.HasType inputs.context resolved type
private def reference (inputs : LocalInputs) (source : Syntax.Expr) : IO (Reference inputs source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          match typed : inputs.context.lookup? id, indexed : Resolved.LocalScope.index? inputs.context.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original context row missing")
      | none => throw (IO.userError "original name missing")
  | _ => throw (IO.userError "not original identifier")
private structure Observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : Type where
  evidence : ∀ store, LocalExpressionEvaluatesWithCost inputs.names inputs.environment store source value store 1
private def observed (inputs : LocalInputs) (source : Syntax.Expr) (value : Core.Value) : IO (Observed inputs source value) := do
  match shape : source with
  | ⟨_, .identifier name⟩ =>
      match named : inputs.names.lookup? name.value with
      | some id =>
          if found : inputs.environment.lookup? id = some value then
            return ⟨fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          else throw (IO.userError "actual row changed")
      | none => throw (IO.userError "actual name missing")
  | _ => throw (IO.userError "raw child changed")
private def header (types : TypeNameTable) (source : Syntax.FunctionDecl) (output : Core.Ty) :
    IO (PLift (RuntimeFunctionHeader types source.value.signature output)) := do
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = output then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.evidence)⟩⟩
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return type")
  | _ => throw (IO.userError "original return shape")

private def verify (inputs : LocalInputs) (source : Syntax.Expr) (core shifted : Core.Expr) (type : Core.Ty)
    (s t : Core.Store) (value : Core.Value) (cost : Nat)
    (elaboration : LocalComputationElaborates inputs.names inputs.context source core type)
    (typing : LocalComputationHasType inputs.names inputs.context source type)
    (raw : LocalComputationEvaluates inputs.names inputs.environment s source value t)
    (costed : LocalComputationEvaluatesWithCost inputs.names inputs.environment s source value t cost)
    (manual : ∀ k, Core.Steps cost ⟨.eval core inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  have checked := elaborateLocalComputation?_iff.mpr elaboration
  have _ := elaborateLocalComputation?_iff.mp checked
  have _ := localComputationHasType_iff_elaborates.mp typing
  have _ := localComputationHasType_iff_elaborates.mpr ⟨core,elaboration⟩
  have coreTyped := elaboration.core_hasType
  have _ := localComputationEvaluates_iff_exists_cost.mp raw
  have _ := localComputationEvaluates_iff_exists_cost.mpr ⟨cost,costed⟩
  have evaluated := (elaboration.evaluates_iff inputs.sameIds).mp raw
  have _ := (elaboration.evaluates_iff inputs.sameIds).mpr evaluated
  have _ := costed.deterministic ((elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
  have _ := (elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mp costed
  have _ := costed.toStepsWithContinuation elaboration inputs.sameIds [.letBody .unit []]
  check (decide (elaborateLocalComputation? inputs.names inputs.context source = some (core,type) ∧
    core.weakenAt 0 = shifted)) "independent original and shifted Core"
  let inserted := Core.Value.cellRef .bool 999
  have _ := (elaboration.core_hasType_insert_iff [] inputs.context.values (.namedData ⟨700⟩)).mp
    ((elaboration.core_hasType_insert_iff [] inputs.context.values (.namedData ⟨700⟩)).mpr coreTyped)
  have changed := (elaboration.core_evaluates_insert_iff [] inputs.environment.values inserted).mpr evaluated
  have _ := (elaboration.core_evaluates_insert_iff [] inputs.environment.values inserted).mp changed
  have paired : ∀ k, Core.Steps cost ⟨.eval core inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ ∧
      Core.Steps cost ⟨.eval (core.weakenAt 0) (inserted::inputs.environment.values),k,s⟩ ⟨.ret value,k,t⟩ := by
    obtain ⟨common,paths⟩ := elaboration.core_insertion_paths [] inputs.environment.values inserted evaluated
    have sameCost := ((manual []).final_unique (paths []).1).1
    exact sameCost.symm ▸ paths
  for shiftedSide in [false,true] do
    let start := if shiftedSide then Core.State.initial (core.weakenAt 0) (inserted::inputs.environment.values) s
      else Core.State.initial core inputs.environment.values s
    have path : Core.Steps cost start (.final value t) := by
      cases shiftedSide
      · exact (paired []).1
      · exact (paired []).2
    for fuel in List.range (cost+2) do
      match exhausted : Core.runStateful fuel start with
      | .done actual final => check (decide (cost ≤ fuel ∧ actual=value ∧ final=t)) "exact independent cost/value/store"
      | .outOfFuel cp =>
          have _ := path.residual_of_outOfFuel exhausted
          have _ := Core.runStateful_resume exhausted (cost-fuel)
          check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp = .done value t ∧
            Core.runStateful 1 cp = Core.runStateful (fuel+1) start)) "own genuine residual/full resume"
      | .fault _ _ => throw (IO.userError "independent successful path faulted")
  let k := [Core.Frame.letBody .unit []]
  have _ := paired k
  check (decide (Core.runStateful (cost+2) ⟨.eval core inputs.environment.values,k,s⟩ = .done .unit t ∧
    Core.runStateful (cost+2) ⟨.eval shifted (inserted::inputs.environment.values),k,s⟩ = .done .unit t))
    "retained continuation runs after the costed endpoint"
private def outcomes (call : Bool) (types : TypeNameTable) (source : Syntax.FunctionDecl)
    (args : List TypedRuntimeArgument) (core : Core.Expr) (type : Core.Ty) (store : Core.Store) (cost : Nat) : IO Unit := do
  check (if call then decide (compileRuntimeFunction? types owner source = none ∧ prepareRuntimeFunction? types owner source args = none)
    else decide (compileRuntimeApplicationFunction? types owner source = none ∧
      prepareRuntimeApplicationFunction? types owner source args = none)) "other profile's whole rejection changed"
  for fuel in List.range (cost+2) do
    let expected := some (type,Core.runStateful fuel (.initial core (args.reverse.map (·.value)) store))
    check (if call then decide (runRuntimeApplicationFunction? types owner source args fuel store = expected ∧
        runRuntimeFunction? types owner source args fuel store = none)
      else decide (runRuntimeFunction? types owner source args fuel store = expected ∧
        runRuntimeApplicationFunction? types owner source args fuel store = none)) "old whole-entry boundaries changed"
private def execute (call : Bool) (argument : TypedRuntimeArgument) (output : Core.Ty)
    (body : Core.Expr) (captured : Core.Environment) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value::captured),k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output,.closure argument.type output body captured,closureTyped⟩
  let args := [f,argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],if call then output else argument.type)]
  let source ← parsed (if call then "function invoke(f:F,x:A) returns(R){return f(x);}"
    else "function invoke(f:F,x:A) returns(R){return x;}")
  let ps ← parameters types source.value.signature.parameters.elements args; let inputs := ps.actual
  let h ← header types source (if call then output else argument.type)
  have _ := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have rows : inputs.environment.values = [argument.value,f.value] := by
    simpa [args,LocalInputs.environment,Resolved.LocalScope.values,List.map_map,Function.comp_def] using
      RuntimeParametersBind.argument_values ps.bound
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
    [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "one original actual parameter record"
  match shape : source.value.body with
  | ⟨bs,[⟨rs,.returnStmt (some expression)⟩]⟩ =>
      check (bs.contains rs && rs.contains expression.span) "original body/return ranges"
      if choose : call then
        match original : expression with
        | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
            check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span &&
              decide (fn.span.endByte ≤ argsSpan.startByte)) "original ordered child spans"
            let fc ← reference inputs fn; let ac ← reference inputs arg
            if same : fc.type=f.type ∧ ac.type=argument.type ∧ fc.core=.var 1 ∧ ac.core=.var 0 then
              have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
                rw [original]; simpa only [target,same.2.2.1,same.2.2.2] using LocalFunctionApplicationElaborates.call
                  (span := span) (argumentsSpan := argsSpan) fc.resolution fc.lowered (same.1 ▸ fc.typing)
                  ac.resolution ac.lowered (same.2.1 ▸ ac.typing)
              let fp ← observed inputs fn f.value; let ap ← observed inputs arg argument.value
              have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost+5) := by
                rw [original]; simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
                  LocalFunctionApplicationEvaluatesWithCost.call (span := span) (argumentsSpan := argsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
              have whole : RuntimeApplicationFunctionPrepares types owner source args ⟨inputs,target,output⟩ :=
                ⟨by simpa [choose] using h.down,ps.bound,by rw [shape]; exact .application child⟩
              have _ := whole.complete; have _ := whole.compiles.complete
              have manual (k) : Core.Steps (bodyCost+5) ⟨.eval target inputs.environment.values,k,s⟩ ⟨.ret value,k,t⟩ := by
                rw [rows]; exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
              verify inputs expression target (.apply (.var 2) (.var 1)) output s t value (bodyCost+5)
                (.application child) (.application child.hasType) (.application costed.erase) (.application costed) manual
              outcomes true types source args target output s (bodyCost+5)
            else throw (IO.userError "fixed call children changed")
        | _ => throw (IO.userError "original root call changed")
      else
        let ac ← reference inputs expression; let ap ← observed inputs expression argument.value
        if same : ac.type=argument.type ∧ ac.core=.var 0 then
          have child : LocalComputationElaborates inputs.names inputs.context expression (.var 0) argument.type :=
            .pure ac.resolution (same.2 ▸ ac.lowered) (same.1 ▸ ac.typing)
          have whole : RuntimeFunctionPrepares types owner source args ⟨inputs,.var 0,argument.type⟩ := by
            refine ⟨by simpa [choose] using h.down,ps.bound,.single ?_⟩
            rw [LocalInputs.toTypeInputs_names,LocalInputs.toTypeInputs_context,shape]
            exact .expression ac.resolution (same.2 ▸ ac.lowered) (same.1 ▸ ac.typing)
          have _ := whole.complete; have _ := whole.compiles.complete
          verify inputs expression (.var 0) (.var 1) argument.type s s argument.value 1 child
            (.pure (ac.resolution.reflects_type (same.1 ▸ ac.typing))) (.pure (ap.evidence s).erase) (.pure (ap.evidence s))
            (fun _ => by rw [rows]; exact .cons (.var rfl) .refl)
          outcomes false types source args (.var 0) argument.type s 1
        else throw (IO.userError "fixed pure child changed")
  | _ => throw (IO.userError "original singleton return changed")
end ParsedLocalComputationEntries
open ParsedLocalComputationEntries
def frontendParsedLocalComputationEntryTests : IO Unit := do
  for argument in [TypedRuntimeArgument.mk .word (w 14) .word,⟨.unit,.unit,.unit⟩,
      ⟨.product .word .bool,.pair (w 3) (.bool false),.pair .word .bool⟩,
      ⟨.cell .word,.cellRef .word 999,.cellRef⟩,
      ⟨.function .word .word,.closure .word .word (.var 1) [w 23],.closure (.cons .word .nil) (.var rfl)⟩,
      ⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),.closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩] do
    execute false argument argument.type (.var 0) [] [w 23] [w 23] argument.value 1
      (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  for current in [3,17] do
    execute true ⟨.word,w 14,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl)))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute true ⟨.word,w 14,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 14] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl))) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  execute true ⟨.word,w 14,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0] [w 3] [w 14] (w 14) 10
    (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl))))
    (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
      (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  execute true ⟨.word,w 14,.word⟩ .word (.letE (.var 0) (.var 0)) [] [] [] (w 14) 4
    (.closure .nil (.letE (.var rfl) (.var rfl))) (fun _ => .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))
  let higher : TypedRuntimeArgument := ⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),
    .closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩
  execute true higher higher.type (.var 0) [] [] [] higher.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
  let source ← parsed "function invoke(f:F,x:A) returns(R){let r=f(x);return r+1;}"
  let args : List TypedRuntimeArgument := [⟨.function .word .word,.closure .word .word (.var 0) [],.closure .nil (.var rfl)⟩,⟨.word,w 14,.word⟩]
  let types := [(["F"],Core.Ty.function .word .word),(["A"],Core.Ty.word),(["R"],Core.Ty.word)]
  let ps ← parameters types source.value.signature.parameters.elements args
  match source.value.body.value with
  | ⟨_,.letDecl _ none (some child)⟩ :: _ =>
      check (decide (elaborateLocalComputation? ps.actual.names ps.actual.context child = some (target,.word) ∧
        prepareRuntimeFunction? types owner source args = none ∧ prepareRuntimeApplicationFunction? types owner source args = none ∧
        runRuntimeFunction? types owner source args 99 [] = none ∧ runRuntimeApplicationFunction? types owner source args 99 [] = none))
        "accepted child did not authorize a mixed whole body"
  | _ => throw (IO.userError "original mixed-body boundary changed")
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalComputationReturnTree
/-! Original parsed function bodies are checked against an explicit sparse caller,
not treated as newly supported whole entries. Static and raw certificates are
independent of checking; literal Core programs have separate manual paths. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalComputationReturnTree
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Mixed", by decide⟩], by decide⟩⟩, 51⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 90},302⟩
private def inputs (a b : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"x",id 4,a⟩,⟨"f",foreign,.function a b⟩,⟨"g",id 9,.function a .bool⟩,
  ⟨"maker",id 12,.function a (.function a b)⟩,⟨"f",id 15,.bool⟩],by change [id 4,foreign,id 9,id 12,id 15].Nodup; decide⟩
private def types (a b : Core.Ty) : TypeNameTable := [(["A"],a),(["B"],b)]
private def identity (a : Core.Ty) : Core.Value := .closure a a (.var 0) [.unit]
private def env (a : Core.Ty) (x : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(id 4,x),(foreign,identity a),(id 9,.closure a .bool (.bool choice) [.unit]),
    (id 12,.closure a (.function a a) (.var 1) [identity a]),(id 15,.bool false)]
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def parsed (text : String) : IO Syntax.Block := do
  let text := "function example(){" ++ text ++ "}"
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-body.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens) | throw (IO.userError "function parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span = ⟨file.id,0,text.utf8ByteSize⟩) &&
    source.span.contains source.value.body.span) "original full function/span"
  return source.value.body
private structure Atom (i : LocalTypeInputs) (s : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression i.names s resolved
  lowered : Resolved.Lowers i.context.ids resolved core
  typing : Resolved.HasType i.context resolved type
private def atom (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Atom i s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : i.names.lookup? name.value with
      | some localId =>
          match typed : i.context.lookup? localId, indexed : Resolved.LocalScope.index? i.context.ids localId with
          | some t,some n => return ⟨.var localId,.var n,t,by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _,_ => throw (IO.userError "original row")
      | _ => throw (IO.userError "original name")
  | _ => throw (IO.userError "not an atom")
private structure Child (i : LocalTypeInputs) (s : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationElaborates i.names i.context s core type
  typing : LocalComputationHasType i.names i.context s type
private def child (i : LocalTypeInputs) (s : Syntax.Expr) : IO (Child i s) := do
  match shape : s with
  | ⟨span,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (span.contains fn.span && span.contains argsSpan && argsSpan.contains arg.span && decide (fn.span.endByte ≤ argsSpan.startByte)) "call original order/spans"
      let f ← atom i fn; let a ← atom i arg
      match ft : f.type with
      | .function input output =>
          if same : a.type = input then return ⟨.apply f.core a.core,output,
            by rw [shape]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
            by rw [shape]; exact .application (.call (f.resolution.reflects_type (ft ▸ f.typing)) (a.resolution.reflects_type (same ▸ a.typing)))⟩
          else throw (IO.userError "argument type")
      | _ => throw (IO.userError "callee type")
  | _ =>
      let a ← atom i s
      return ⟨a.core,a.type,.pure a.resolution a.lowered a.typing,.pure (a.resolution.reflects_type a.typing)⟩
private structure Static (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  elaboration : LocalComputationReturnTreeElaborates ts owner i b core type
  typing : LocalComputationReturnTreeHasType ts owner i b type
private def statics (ts : TypeNameTable) (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static ts i b) := do
  for statement in b.value do check (b.span.contains statement.span) "original statement span"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,.unit,by rw [shape]; exact .bare,by rw [shape]; exact .bare⟩
  | ⟨_,[⟨rs,.returnStmt (some s)⟩]⟩ =>
      check (rs.contains s.span) "original return span"; let c ← child i s
      have _ := c.elaboration.core_fragment
      return ⟨c.core,c.type,by rw [shape]; exact .expression c.elaboration,by rw [shape]; exact .expression c.typing⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← statics ts i ⟨inner,statements⟩
      return ⟨c.core,c.type,by rw [shape]; exact .block c.elaboration,by rw [shape]; exact .block c.typing⟩
  | ⟨bs,⟨ls,.letDecl name annotation (some init)⟩::rest⟩ =>
      check (ls.contains name.span && ls.contains init.span) "original binding order/spans"
      if unused : name.value ∉ i.names.map Prod.fst then
        let c ← child i init; let tail ← statics ts (i.bindFresh owner name.value c.type) ⟨bs,rest⟩
        match ann : annotation with
        | none => return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .inferred unused c.elaboration tail.elaboration,
            by rw [shape,ann]; exact .inferred unused c.typing tail.typing⟩
        | some annotationSource =>
            check (ls.contains annotationSource.span) "original annotation span"
            match written : annotationSource with
            | ⟨_,.named name none⟩ =>
                if lookup : ts.lookup? (qualifiedTypeNameKey name) = some c.type then
                  have m : StructuralTypeDenotes ts annotationSource c.type := by rw [written]; exact .named (TypeNameTable.lookup?_iff.mp lookup)
                  return ⟨.letE c.core tail.core,tail.type,by rw [shape,ann]; exact .binding m unused c.elaboration tail.elaboration,
                    by rw [shape,ann]; exact .binding m unused c.typing tail.typing⟩
                else throw (IO.userError "annotation meaning")
            | _ => throw (IO.userError "annotation shape")
      else throw (IO.userError "shadow")
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← child i s; let tail ← statics ts i ⟨bs,rest⟩
      return ⟨.letE c.core (tail.core.weakenAt 0),tail.type,by rw [shape]; exact .discard c.elaboration tail.elaboration,
        by rw [shape]; exact .discard c.typing tail.typing⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← child i guard; let a ← statics ts i yes; let d ← statics ts i no
      if ct : c.type = .bool then
        if same : d.type = a.type then return ⟨.ifE c.core a.core d.core,a.type,
          by rw [shape]; exact .conditional (ct ▸ c.elaboration) a.elaboration (same ▸ d.elaboration),
          by rw [shape]; exact .conditional (ct ▸ c.typing) a.typing (same ▸ d.typing)⟩
        else throw (IO.userError "both arm types")
      else throw (IO.userError "Bool guard")
  | _ => throw (IO.userError "outside static fixture")
termination_by sizeOf b
private structure AtomCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  evidence : ∀ store, LocalExpressionEvaluatesWithCost table e store s value store 1
private def atomCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (AtomCost table e s) := do
  match shape : s with
  | ⟨_,.identifier name⟩ =>
      match named : table.lookup? name.value with
      | some localId =>
          match found : e.lookup? localId with
          | some v => return ⟨v,fun _ => by rw [shape]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _ => throw (IO.userError "missing actual")
      | _ => throw (IO.userError "missing raw name")
  | _ => throw (IO.userError "raw atom shape")
private structure ChildCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalComputationEvaluatesWithCost table e store s value store cost
private def childCost (table : LocalNameTable) (e : Resolved.Environment) (s : Syntax.Expr) : IO (ChildCost table e s) := do
  match shape : s with
  | ⟨_,.call fn ⟨_,[arg]⟩⟩ =>
      let f ← atomCost table e fn; let a ← atomCost table e arg
      match closure : f.value with
      | .closure _ _ (.var n) captured =>
          match found : (a.value::captured)[n]? with
          | some value => return ⟨value,6,fun store => by rw [shape]; exact .application (.call (closure ▸ f.evidence store) (a.evidence store) (.cons (.var found) .refl))⟩
          | _ => throw (IO.userError "actual capture missing")
      | .closure _ _ (.bool choice) _ => return ⟨.bool choice,6,fun store => by rw [shape]; exact .application (.call (closure ▸ f.evidence store) (a.evidence store) (.cons .bool .refl))⟩
      | _ => throw (IO.userError "outside actual body fixture")
  | _ => let a ← atomCost table e s; return ⟨a.value,1,fun store => .pure (a.evidence store)⟩
private structure Cost (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) where
  value : Core.Value
  cost : Nat
  evidence : ∀ store, LocalComputationReturnTreeEvaluatesWithCost owner table e store b value store cost
private def costs (table : LocalNameTable) (e : Resolved.Environment) (b : Syntax.Block) : IO (Cost table e b) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ => return ⟨.unit,1,fun _ => by rw [shape]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some s)⟩]⟩ =>
      let c ← childCost table e s; return ⟨c.value,c.cost,fun store => by rw [shape]; exact .expression (c.evidence store)⟩
  | ⟨_,[⟨inner,.block statements⟩]⟩ =>
      let c ← costs table e ⟨inner,statements⟩; return ⟨c.value,c.cost,fun store => by rw [shape]; exact .block (c.evidence store)⟩
  | ⟨bs,⟨_,.letDecl name annotation (some init)⟩::rest⟩ =>
      let c ← childCost table e init; let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      let tail ← costs ((name.value,fresh)::table) ((fresh,c.value)::e) ⟨bs,rest⟩
      match ann : annotation with
      | none => return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape,ann]; exact .inferred (c.evidence store) (tail.evidence store)⟩
      | some _ => return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape,ann]; exact .binding (c.evidence store) (tail.evidence store)⟩
  | ⟨bs,⟨_,.expression s true⟩::rest⟩ =>
      let c ← childCost table e s; let tail ← costs table e ⟨bs,rest⟩
      return ⟨tail.value,c.cost+tail.cost+2,fun store => by rw [shape]; exact .discard (c.evidence store) (tail.evidence store)⟩
  | ⟨_,[⟨_,.ifThen guard yes (some no)⟩]⟩ =>
      let c ← childCost table e guard
      match selected : c.value with
      | .bool true => let a ← costs table e yes; return ⟨a.value,c.cost+a.cost+2,fun store => by rw [shape]; exact .ifTrue (selected ▸ c.evidence store) (a.evidence store)⟩
      | .bool false => let a ← costs table e no; return ⟨a.value,c.cost+a.cost+2,fun store => by rw [shape]; exact .ifFalse (selected ▸ c.evidence store) (a.evidence store)⟩
      | _ => throw (IO.userError "raw Bool guard")
  | _ => throw (IO.userError "outside raw fixture")
termination_by sizeOf b
private def staticCheck (a b : Core.Ty) (text : String) (core : Core.Expr) (type : Core.Ty) (mixed : Bool) : IO Unit := do
  let source ← parsed text; let i := inputs a b; let p ← statics (types a b) i source
  have _ := elaborateLocalComputationReturnTree?_iff.mp (elaborateLocalComputationReturnTree?_iff.mpr p.elaboration)
  have _ := localComputationReturnTreeHasType_iff_elaborates.mp p.typing
  have _ := localComputationReturnTreeHasType_iff_elaborates.mpr ⟨p.core,p.elaboration⟩
  have _ := p.elaboration.core_hasType
  check (decide (p.core=core ∧ p.type=type ∧ elaborateLocalComputationReturnTree? (types a b) owner i source=some (core,type) ∧
    elaborateTypedLetReturnTree? (types a b) owner i source=(if mixed then none else some (core,type)) ∧
    (i.bindFresh owner "r" b).names.lookup? "r"=some (id 16) ∧ i.names.lookup? "f"=some foreign)) "independent Core/type/fresh/old boundary"
private def exercise (argument : TypedRuntimeArgument) (choice : Bool) (text : String) (core : Core.Expr) (type : Core.Ty)
    (value : Core.Value) (cost : Nat)
    (manual : ∀ store k, Core.Steps cost ⟨.eval core (env argument.type argument.value choice).values,k,store⟩ ⟨.ret value,k,store⟩) : IO Unit := do
  let source ← parsed text; let i := inputs argument.type argument.type; let e := env argument.type argument.value choice
  let p ← statics (types argument.type argument.type) i source; let r ← costs i.names e source
  if fixed : p.core=core ∧ p.type=type ∧ r.value=value ∧ r.cost=cost then
    have elaboration : LocalComputationReturnTreeElaborates (types argument.type argument.type) owner i source core type := by simpa only [fixed.1,fixed.2.1] using p.elaboration
    check (decide (elaborateLocalComputationReturnTree? (types argument.type argument.type) owner i source=some (core,type))) "actual caller exact checking"
    have ids : e.ids=i.context.ids := rfl
    have fragment := elaboration.core_fragment
    have _ := fragment.weakenAt 0
    for store in [[],[Core.Value.bool true,.unit]] do
      have counted : LocalComputationReturnTreeEvaluatesWithCost owner i.names e store source value store cost := by simpa only [fixed.2.2.1,fixed.2.2.2] using r.evidence store
      have raw := localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨cost,counted⟩
      have _ := localComputationReturnTreeEvaluates_iff_exists_cost.mp raw
      have original := (elaboration.evaluates_iff ids).mp raw
      have _ := (elaboration.evaluates_iff ids).mpr original
      have _ := counted.deterministic ((elaboration.evaluatesWithCost_iff_steps ids).mpr (manual store []))
      have _ := (elaboration.evaluatesWithCost_iff_steps ids).mp counted
      let pending := [Core.Frame.letBody .unit []]
      have _ := counted.toStepsWithContinuation elaboration ids pending
      let inserted := Core.Value.closure .bool .word (.var 99) [.unit]
      have changed := (fragment.evaluates_insert_iff [] e.values inserted).mpr original
      have _ := (fragment.evaluates_insert_iff [] e.values inserted).mp changed
      have pair : ∀ k, Core.Steps cost ⟨.eval core e.values,k,store⟩ ⟨.ret value,k,store⟩ ∧
          Core.Steps cost ⟨.eval (core.weakenAt 0) (inserted::e.values),k,store⟩ ⟨.ret value,k,store⟩ := by
        obtain ⟨n,paths⟩ := fragment.insertion_paths [] e.values inserted original
        have same := ((manual store []).final_unique (paths []).1).1
        exact same.symm ▸ paths
      for shifted in [false,true] do
        let start := Core.State.initial (if shifted then core.weakenAt 0 else core) (if shifted then inserted::e.values else e.values) store
        have path : Core.Steps cost start (.final value store) := by cases shifted; exact (pair []).1; exact (pair []).2
        for fuel in List.range (cost+2) do
          match outcome : Core.runStateful fuel start with
          | .done v s => check (decide (cost≤fuel ∧ v=value ∧ s=store)) "fixed cost/value/store"
          | .outOfFuel cp =>
              have _ := path.residual_of_outOfFuel outcome
              have _ := Core.runStateful_resume outcome (cost-fuel)
              check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value store ∧ Core.runStateful 1 cp=Core.runStateful (fuel+1) start)) "genuine own checkpoint/resume"
          | .fault _ _ => throw (IO.userError "manual successful path faulted")
      check (decide (Core.runStateful cost ⟨.eval core e.values,pending,store⟩=.outOfFuel ⟨.ret value,pending,store⟩)) "pending endpoint is not completion"
  else throw (IO.userError "independent expected result")
private theorem invoke {e : Core.Environment} {s : Core.Store} {k : List Core.Frame} {f x : Nat}
    {a b : Core.Ty} {body : Core.Expr} {captured : Core.Environment} {argument value : Core.Value}
    (fn : e[f]?=some (.closure a b body captured)) (arg : e[x]?=some argument)
    (path : Core.Steps 1 ⟨.eval body (argument::captured),k,s⟩ ⟨.ret value,k,s⟩) :
    Core.Steps 6 ⟨.eval (call f x) e,k,s⟩ ⟨.ret value,k,s⟩ :=
  .cons .enterApply (.cons (.var fn) (.cons .beginArgument (.cons (.var arg) (.cons .invokeClosure path))))
private def wrap : Nat → String → String | 0,s => s | n+1,s => "{" ++ wrap n s ++ "}"
end ParsedLocalComputationReturnTree
open ParsedLocalComputationReturnTree
def frontendParsedLocalComputationReturnTreeTests : IO Unit := do
  let bound := Core.Expr.letE (call 1 0) (.var 0)
  let higher := Core.Expr.letE (call 3 0) (call 0 1)
  let discards := Core.Expr.letE (call 1 0) (.letE (call 2 1) (call 3 2))
  let branches := Core.Expr.ifE (call 2 0) bound (call 1 0)
  have p : LocalComputationFragment (.var 0) := .pure .var
  have a : LocalComputationFragment (call 1 0) := .application .var .var
  have _ : LocalComputationFragment branches := .ifE (.application .var .var) (.letE a p) a
  let conditional := "if(g(x)){{let r:B=f(x);return r;}}else{return f(x);}"
  for a in [Core.Ty.unit,.word,.namedData ⟨7⟩,.function (.namedData ⟨8⟩) (.namedData ⟨9⟩)] do
    for b in [Core.Ty.unit,.cell .word,.namedData ⟨10⟩] do
      for (text,core,type,mixed) in [("return;",.unit,.unit,false),("return x;",.var 0,a,false),
          ("return f(x);",call 1 0,b,true),("let r=f(x);return r;",bound,b,true),("let r:B=f(x);return r;",bound,b,true),
          ("let h=maker(x);return h(x);",higher,b,true),("f(x);f(x);return f(x);",discards,b,true),(conditional,branches,b,true)] do
        for depth in [0,2,7] do staticCheck a b (wrap depth text) core type mixed
  let bare ← parsed "return;"
  match shape : bare with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      have old : TypedLetReturnTreeElaborates [] owner (inputs .unit .unit) bare .unit .unit := by rw [shape]; exact .single .bare
      have _ := old.toLocalComputationReturnTree
  | _ => throw (IO.userError "bare original shape")
  for argument in [TypedRuntimeArgument.mk .unit .unit .unit,⟨.word,.word (Core.Word.ofNatModulo 17),.word⟩,
      ⟨.cell .word,.cellRef .word 999,.cellRef⟩,⟨.function (.namedData ⟨9⟩) (.namedData ⟨9⟩),
        .closure (.namedData ⟨9⟩) (.namedData ⟨9⟩) (.var 0) [],.closure .nil (.var rfl)⟩] do
    for choice in [false,true] do
      exercise argument choice "return;" .unit .unit .unit 1 (fun _ _ => .cons .unit .refl)
      exercise argument choice "return x;" (.var 0) argument.type argument.value 1 (fun _ _ => .cons (.var rfl) .refl)
      for text in ["let r=f(x);return r;","let r:B=f(x);return r;"] do
        exercise argument choice (wrap 2 text) bound argument.type argument.value 9 (fun _ _ =>
          CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl))
      exercise argument choice "let h=maker(x);return h(x);" higher argument.type argument.value 14 (fun _ _ =>
        CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (invoke rfl rfl (.cons (.var rfl) .refl)))
      exercise argument choice "f(x);f(x);return f(x);" discards argument.type argument.value 22 (fun _ _ =>
        CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl))
          (CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (invoke rfl rfl (.cons (.var rfl) .refl))))
      exercise argument choice conditional branches argument.type argument.value (if choice then 17 else 14) (by
        intro s k; cases choice
        · exact CostStepComposition.ifFalse (invoke rfl rfl (.cons .bool .refl)) (invoke rfl rfl (.cons (.var rfl) .refl))
        · exact CostStepComposition.ifTrue (invoke rfl rfl (.cons .bool .refl))
            (CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons (.var rfl) .refl)))
  for text in ["", "f(x);", "let r:B;return r;", "let x=f(x);return x;", "let r=r;return r;", "let r:Unknown=f(x);return r;",
      "let r=f(f(x));return r;", "let r=(f(x));return r;", "return x + f(x);", "{return x;}return x;",
      "if(g(x)){return x;}", "if(g(x)){return x;}else{return f(x);}return x;", "return x;f(x);"] do
    let source ← parsed text
    check (decide (elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) source=none)) "whole rejection boundary"
  let arithmetic ← parsed "let r=f(x);return r + 1;"
  let arithmeticCore := Core.Expr.letE (call 1 0) (.binary .wordAdd (.var 0) (.word (Core.Word.ofNatModulo 1)))
  have arithmeticPath (s k) : Core.Steps 13 ⟨.eval arithmeticCore (env .word (.word (Core.Word.ofNatModulo 17)) true).values,k,s⟩ ⟨.ret (.word (Core.Word.ofNatModulo 18)),k,s⟩ :=
    CostStepComposition.letE (invoke rfl rfl (.cons (.var rfl) .refl)) (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons .word (.cons (.applyBinary rfl) .refl)))))
  let start := Core.State.initial arithmeticCore (env .word (.word (Core.Word.ofNatModulo 17)) true).values []
  check (decide (elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) arithmetic=some (arithmeticCore,.word) ∧ Core.runStateful 13 start=.done (.word (Core.Word.ofNatModulo 18)) [])) "call result feeds pure addition"
  match cp : Core.runStateful 12 start with
  | .outOfFuel state => have _ := (arithmeticPath [] []).residual_of_outOfFuel cp; check (decide (Core.runStateful 1 state=.done (.word (Core.Word.ofNatModulo 18)) [])) "arithmetic genuine residual"
  | _ => throw (IO.userError "arithmetic premature endpoint")
  let source ← parsed "if(g(x)){return x;}else{let r:Unknown=f(x);return r;}"
  let r ← costs (inputs .word .word).names (env .word (.word (Core.Word.ofNatModulo 17)) true) source
  have _ := localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨r.cost,r.evidence []⟩
  check (decide (r.value=.word (Core.Word.ofNatModulo 17) ∧ r.cost=9 ∧
    elaborateLocalComputationReturnTree? (types .word .word) owner (inputs .word .word) source=none)) "selected raw versus whole unknown arm"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalComputationReturnTreeEntries
/-! Original functions supply parameters, not a new whole-function endpoint.
Source certificates and explicit Core transition scripts have separate fixed expectations. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace MixedComputationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MixedActual",by decide⟩],by decide⟩⟩,31⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def app (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def parsed (text : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main,"mixed-actual.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original function did not parse")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.body.span) "complete original bytes"
  return source
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) :
    IO (Σ type, PLift (StructuralTypeDenotes types source type)) := do
  match atSource : source with
  | ⟨_,.named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type,⟨by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
      | none => throw (IO.userError "original annotation missing")
  | _ => throw (IO.userError "outside named fixture")
private structure Parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (types : TypeNameTable) (s : LocalTypeInputs) (a : LocalInputs)
    (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters types s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning types annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters types (s.bindFresh owner name.value arg.type)
            (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,
            by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate original parameter")
      else throw (IO.userError "original argument type mismatch")
  | _,_ => throw (IO.userError "original parameter arity")
private structure Path (core : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval core env,k,s⟩ ⟨.ret value,k,final⟩
-- A bounded fixture script constructs transitions; it never calls the machine runner.
private def path : (fuel : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual script depth")
  | n+1,e,env,s => do
    match original : e with
    | .var i =>
        match found : env[i]? with
        | some v => return ⟨v,s,1,fun _ => by rw [original]; exact .cons (.var found) .refl⟩
        | none => throw (IO.userError "manual var missing")
    | .unit => return ⟨.unit,s,1,fun _ => by rw [original]; exact .cons .unit .refl⟩
    | .bool b => return ⟨.bool b,s,1,fun _ => by rw [original]; exact .cons .bool .refl⟩
    | .letE head tail =>
        let a ← path n head env s; let b ← path n tail (a.value::env) a.final
        return ⟨b.value,b.final,a.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.letE (a.evidence _) (b.evidence _)⟩
    | .apply fn arg =>
        let f ← path n fn env s; let a ← path n arg env f.final
        match fv : f.value with
        | .closure _ _ body captured =>
            let b ← path n body (a.value::captured) a.final
            return ⟨b.value,b.final,f.cost+a.cost+b.cost+3,fun _ => by rw [original]; exact CostStepComposition.apply (fv ▸ f.evidence _) (a.evidence _) (b.evidence [])⟩
        | _ => throw (IO.userError "manual callee shape")
    | .ifE condition yes no =>
        let c ← path n condition env s
        match cv : c.value with
        | .bool true =>
            let b ← path n yes env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifTrue (cv ▸ c.evidence _) (b.evidence _)⟩
        | .bool false =>
            let b ← path n no env c.final
            return ⟨b.value,b.final,c.cost+b.cost+2,fun _ => by rw [original]; exact CostStepComposition.ifFalse (cv ▸ c.evidence _) (b.evidence _)⟩
        | _ => throw (IO.userError "manual guard shape")
    | .loadCell (.var i) =>
        match found : env[i]? with
        | some (.cellRef t l) =>
            match read : s.read? l with
            | some v => return ⟨v,s,3,fun _ => by rw [original]; exact .cons .enterLoadCell (.cons (.var found) (.cons (.applyLoadCell read) .refl))⟩
            | none => throw (IO.userError "manual load missing")
        | _ => throw (IO.userError "manual reference shape")
    | .newCell t (.var i) =>
        match found : env[i]? with
        | some v => return ⟨.cellRef t s.length,s++[v],3,fun _ => by rw [original]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
        | none => throw (IO.userError "manual allocation value")
    | .storeCell (.var i) (.var j) =>
        match ref : env[i]?, val : env[j]? with
        | some (.cellRef t l),some v =>
            match read : s.read? l, write : s.write? l v with
            | some _,some final => return ⟨.unit,final,5,fun _ => by rw [original]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell write) .refl))))⟩
            | _,_ => throw (IO.userError "manual write missing")
        | _,_ => throw (IO.userError "manual write shape")
    | _ => throw (IO.userError "outside explicit Core script")
private structure Leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  id : Resolved.LocalId
  index : Nat
  type : Core.Ty
  value : Core.Value
  resolution : ResolvesLocalExpression s.names source (.var id)
  lowered : Resolved.Lowers s.context.ids (.var id) (.var index)
  typing : Resolved.HasType s.context (.var id) type
  raw : LocalExpressionEvaluatesWithCost s.names env store source value store 1
private def leaf (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Leaf s env store source) := do
  match original : source with
  | ⟨_,.identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.context.ids id, actual : env.lookup? id with
          | some t,some i,some v => return ⟨id,i,t,v,by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed),.var (Resolved.LocalScope.lookup?_iff.mp typed),
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp actual)⟩
          | _,_,_ => throw (IO.userError "independent original row missing")
      | none => throw (IO.userError "independent original name missing")
  | _ => throw (IO.userError "fixture leaf is not identifier")
private structure Child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationElaborates s.names s.context source core type
  raw : LocalComputationEvaluatesWithCost s.names env store source value final cost
private def child (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) : IO (Child s env store source) := do
  match original : source with
  | ⟨_,.call fn ⟨argsSpan,[arg]⟩⟩ =>
      check (source.span.contains fn.span && source.span.contains argsSpan && argsSpan.contains arg.span) "original call child spans"
      let f ← leaf s env store fn; let a ← leaf s env store arg
      match ft : f.type, fv : f.value with
      | .function input output,.closure _ _ body captured =>
          if same : a.type=input then
            let b ← path 100 body (a.value::captured) store
            return ⟨.apply (.var f.index) (.var a.index),output,b.value,b.final,b.cost+5,
              by rw [original]; exact .application (.call f.resolution f.lowered (ft ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)),
              by rw [original,←(show 1+1+b.cost+3=b.cost+5 by omega)]; exact .application (.call (fv ▸ f.raw) a.raw (b.evidence []))⟩
          else throw (IO.userError "static argument differs")
      | _,_ => throw (IO.userError "static or actual Function differs")
  | _ =>
      let a ← leaf s env store source
      return ⟨.var a.index,a.type,a.value,store,1,.pure a.resolution a.lowered a.typing,.pure a.raw⟩
private structure Tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  final : Core.Store
  cost : Nat
  elaboration : LocalComputationReturnTreeElaborates types owner s source core type
  raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source value final cost
private def tree (types : TypeNameTable) (s : LocalTypeInputs) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Block) : IO (Tree types s env store source) := do
  match original : source with
  | ⟨_,[⟨_,.returnStmt none⟩]⟩ =>
      have old : TypedLetReturnTreeElaborates types owner s source .unit .unit := by rw [original]; exact .single .bare
      have _ := old.toLocalComputationReturnTree
      return ⟨.unit,.unit,.unit,store,1,by rw [original]; exact .bare,by rw [original]; exact .bare⟩
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ =>
      let a ← child s env store e
      have _ := a.elaboration.core_fragment
      return ⟨a.core,a.type,a.value,a.final,a.cost,by rw [original]; exact .expression a.elaboration,by rw [original]; exact .expression a.raw⟩
  | ⟨_,[⟨span,.block statements⟩]⟩ =>
      let b ← tree types s env store ⟨span,statements⟩
      return ⟨b.core,b.type,b.value,b.final,b.cost,by rw [original]; exact .block b.elaboration,by rw [original]; exact .block b.raw⟩
  | ⟨span,⟨_,.letDecl name annotation (some e)⟩::rest⟩ =>
      let a ← child s env store e
      if unused : name.value ∉ s.names.map Prod.fst then
        let id := Resolved.freshLocalId owner s.ids
        let b ← tree types (s.bindFresh owner name.value a.type) ((id,a.value)::env) a.final ⟨span,rest⟩
        have raw : LocalComputationReturnTreeEvaluatesWithCost owner s.names env store source b.value b.final (a.cost+b.cost+2) := by
          rw [original]; cases annotation <;> first | exact .inferred a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw) | exact .binding a.raw (by simpa only [LocalTypeInputs.bindFresh_names,LocalTypeInputs.names_ids] using b.raw)
        match annotationAt : annotation with
        | none => return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .inferred unused a.elaboration b.elaboration,raw⟩
        | some t =>
            let m ← meaning types t
            if same : m.1=a.type then return ⟨.letE a.core b.core,b.type,b.value,b.final,a.cost+b.cost+2,by rw [original,annotationAt]; exact .binding (same ▸ m.2.down) unused a.elaboration b.elaboration,raw⟩
            else throw (IO.userError "original binding annotation differs")
      else throw (IO.userError "shadowing is still excluded")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ =>
      let a ← child s env store e; let b ← tree types s env a.final ⟨span,rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0),b.type,b.value,b.final,a.cost+b.cost+2,by rw [original]; exact .discard a.elaboration b.elaboration,by rw [original]; exact .discard a.raw b.raw⟩
  | ⟨_,[⟨_,.ifThen e yes (some no)⟩]⟩ =>
      let c ← child s env store e
      if ct : c.type=.bool then
        let a ← tree types s env c.final yes; let b ← tree types s env c.final no
        if same : b.type=a.type then
          have el : LocalComputationReturnTreeElaborates types owner s source (.ifE c.core a.core b.core) a.type := by rw [original]; exact .conditional (ct ▸ c.elaboration) a.elaboration (same ▸ b.elaboration)
          match cv : c.value with
          | .bool true => return ⟨.ifE c.core a.core b.core,a.type,a.value,a.final,c.cost+a.cost+2,el,by rw [original]; exact .ifTrue (cv ▸ c.raw) a.raw⟩
          | .bool false => return ⟨.ifE c.core a.core b.core,a.type,b.value,b.final,c.cost+b.cost+2,el,by rw [original]; exact .ifFalse (cv ▸ c.raw) b.raw⟩
          | _ => throw (IO.userError "actual guard differs")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "static guard differs")
  | _ => throw (IO.userError "outside original mixed body fixture")
termination_by sizeOf source
private def verify (body : String) (f g x : TypedRuntimeArgument) (output : Core.Ty)
    (core : Core.Expr) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let types : TypeNameTable := [(["F"],f.type),(["G"],g.type),(["X"],x.type),(["R"],output),(["Cell"],.cell .word)]
  let source ← parsed ("function mixed(f:F,g:G,x:X) returns(R){"++body++"}"); let args := [f,g,x]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements args
  let inputs := ps.actual
  have _ := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  have _ := RuntimeParametersBind.argument_values ps.bound
  check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value))=
    [("x",⟨owner,2⟩,x.type,x.value),("g",⟨owner,1⟩,g.type,g.value),("f",⟨owner,0⟩,f.type,f.value)])) "original one-time actual rows"
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.1=output then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧
            source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have _ : RuntimeFunctionHeader types source.value.signature output :=
            ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same ▸ m.2.down)⟩
          pure ()
        else throw (IO.userError "original header policy")
      else throw (IO.userError "original return meaning")
  | _ => throw (IO.userError "original singleton return clause")
  let b ← tree types inputs.toTypeInputs inputs.environment s source.value.body
  let manual ← path 100 core [x.value,g.value,f.value] s
  check (decide (b.core=core ∧ b.type=output ∧ b.value=value ∧ b.final=final ∧ b.cost=cost ∧
    manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "fixed Core/type/value/store/cost expectations"
  have checked := elaborateLocalComputationReturnTree?_iff.mpr b.elaboration
  have _ := elaborateLocalComputationReturnTree?_iff.mp checked
  have typing := localComputationReturnTreeHasType_iff_elaborates.mpr ⟨_,b.elaboration⟩
  have _ := localComputationReturnTreeHasType_iff_elaborates.mp typing
  have _ := b.elaboration.core_hasType
  have ids : inputs.environment.ids=inputs.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using inputs.sameIds
  have raw := localComputationReturnTreeEvaluates_iff_exists_cost.mpr ⟨_,b.raw⟩
  have _ := localComputationReturnTreeEvaluates_iff_exists_cost.mp raw
  have evaluated := (b.elaboration.evaluates_iff ids).mp raw
  have _ := (b.elaboration.evaluates_iff ids).mpr evaluated
  have closed := b.raw.toStepsWithContinuation b.elaboration ids []
  have _ := b.raw.deterministic ((b.elaboration.evaluatesWithCost_iff_steps ids).mpr closed)
  have _ := (b.elaboration.evaluatesWithCost_iff_steps ids).mp b.raw
  let fragment := b.elaboration.core_fragment
  have _ := fragment.weakenAt 0
  have _ := (fragment.evaluates_insert_iff [] inputs.environment.values (.cellRef .bool 999)).mpr evaluated
  have _ := fragment.insertion_paths [] inputs.environment.values (.cellRef .bool 999) evaluated
  have _ := b.raw.toStepsWithContinuation b.elaboration ids [.letBody .unit []]
  check (decide (compileRuntimeFunction? types owner source=none ∧ compileRuntimeApplicationFunction? types owner source=none)) "no new whole-function acceptance"
  for fuel in List.range (cost+2) do
    check (decide (runRuntimeFunction? types owner source args fuel s=none ∧ runRuntimeApplicationFunction? types owner source args fuel s=none)) "old whole endpoints"
    match exhausted : Core.runStateful fuel (.initial core [x.value,g.value,f.value] s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact actual completion"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel exhausted
        have _ := Core.runStateful_resume exhausted (cost-fuel)
        check (decide (fuel<cost ∧ Core.runStateful (cost-fuel) cp=.done value final ∧
          Core.runStateful 2 cp=Core.runStateful (fuel+2) (.initial core [x.value,g.value,f.value] s))) "genuine residual and full resume"
    | .fault _ _ => throw (IO.userError "independent successful paths faulted")
private def reader : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],
  .closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def delay : Nat → Core.Expr | 0 => .var 0 | n+1 => .letE (.var 0) (delay n)
private theorem delayTyped (n : Nat) (ctx : Core.Context) (found : ctx[0]?=some .word) : Core.HasType ctx (delay n) .word := by
  induction n generalizing ctx with | zero => exact .var found | succ n ih => exact .letE (.var found) (ih _ rfl)
end MixedComputationEntries
open MixedComputationEntries
def frontendParsedLocalComputationReturnTreeEntryTests : IO Unit := do
  let x : TypedRuntimeArgument := ⟨.word,w 14,.word⟩
  for old in [3,23] do
    verify "f(x);return g(x);" writer reader x .word (.letE (app 2 0) (app 2 1)) [w old] [w 14] (w 14) 25
    verify "f(x);{g(x);return x;}" writer reader x .word (.letE (app 2 0) (.letE (app 2 1) (.var 2))) [w old] [w 14] (w 14) 28
    verify "f(x);return g;" writer reader x reader.type (.letE (app 2 0) (.var 2)) [w old] [w 14] reader.value 18
    let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word),.closure .word (.cell .word) (.newCell .word (.var 0)) [],.closure .nil (.newCell (.var rfl))⟩
    let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word,.closure (.cell .word) .word (.loadCell (.var 0)) [],.closure .nil (.loadCell (.var rfl))⟩
    for annotation in ["",":Cell"] do
      verify ("let p"++annotation++"=f(x);return g(p);") alloc load x .word (.letE (app 2 0) (app 2 0)) [w old] [w old,w 14] (w 14) 18
    for choice in [false,true] do
      let guard : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.storeCell (.var 1) (.var 0)) (.bool choice)) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) .bool)⟩
      verify "if(f(x)){return g(x);}else{return x;}" guard reader x .word (.ifE (app 2 0) (app 1 0) (.var 0)) [w old] [w 14] (w 14) (if choice then 23 else 16)
    let maker : TypedRuntimeArgument := ⟨.function .word reader.type,.closure .word reader.type (.var 1) [reader.value],.closure (.cons reader.valueTyped .nil) (.var rfl)⟩
    verify "let h=f(x);return h(x);" maker reader x .word (.letE (app 2 0) (app 0 1)) [w old] [w old] (w old) 16
  for n in [0,2,5,13] do
    let f : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (delay n) [],.closure .nil (delayTyped n _ rfl)⟩
    verify "let y=f(x);return y;" f reader x .word (.letE (app 2 0) (.var 0)) [] [] (w 14) (3*n+9)
  verify "f(x);return;" writer reader x .unit (.letE (app 2 0) .unit) [w 3] [w 14] .unit 18
  verify "let p=f(x);return p;" reader reader x .word (.letE (app 2 0) (.var 0)) [.bool true] [.bool true] (.bool true) 11
  let source ← parsed "function mixed(f:F,g:G,x:X) returns(R){let p=f(x);return p;}"
  let types : TypeNameTable := [(["F"],reader.type),(["G"],reader.type),(["X"],.word),(["R"],.word)]
  let ps ← parameters types .empty .empty source.value.signature.parameters.elements [reader,reader,x]
  let env := [x.value,reader.value,reader.value]; let core := Core.Expr.letE (app 2 0) (.var 0)
  let cp : Core.State := ⟨.ret reader.value,[.applyArgument (.var 0) env,.letBody (.var 0) env],[]⟩
  let fault := Core.StatefulRunResult.fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply,.letBody (.var 0) env],[]⟩
  check (decide (elaborateLocalComputationReturnTree? types owner ps.actual.toTypeInputs source.value.body=some (core,.word) ∧ Core.runStateful 3 (.initial core env [])=.outOfFuel cp ∧ Core.runStateful 8 (.initial core env [])=fault ∧ Core.runStateful 5 cp=fault)) "whole accepted body retains genuine missing-store fault"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalFunctionApplicationEntries
/-! Original whole declarations still fail the old entry profile. Their root
call has independent static provenance; actual closure paths are Core-only. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace LocalFunctionApplicationEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"CallEntry", by decide⟩], by decide⟩⟩, 19⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "local-function-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "complete declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩)) "complete original declaration range changed"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match original : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [original]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "missing independent annotation meaning")
  | _ => throw (IO.userError "outside fixture annotation grammar")
private structure Declared (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def declare (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) : IO (Declared types initial params) := do
  match original : params with
  | [] => return ⟨initial, by rw [original]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← declare types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [original]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate original parameter")
  | _ => throw (IO.userError "unsupported original parameter")
private structure Bound (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  inputs : LocalInputs
  evidence : RuntimeParametersBindFrom types owner initial params args inputs
private def bindArgs (types : TypeNameTable) (initial : LocalInputs) (params : List Syntax.FunctionParameter)
    (args : List TypedRuntimeArgument) : IO (Bound types initial params args) := do
  match original : params, actual : args with
  | [], [] => return ⟨initial, by rw [original, actual]; exact .nil⟩
  | ⟨_, .typed none name annotation⟩ :: rest, argument :: remaining =>
      let m ← meaning types annotation
      if same : m.type = argument.type then
        if unused : name.value ∉ initial.names.map Prod.fst then
          let tail ← bindArgs types (initial.bindFresh owner name.value argument.type argument.value argument.valueTyped) rest remaining
          return ⟨tail.inputs, by rw [original, actual]; exact .cons (same ▸ m.evidence) unused tail.evidence⟩
        else throw (IO.userError "duplicate actual parameter")
      else throw (IO.userError "actual argument type differs")
  | _, _ => throw (IO.userError "actual argument count differs")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers (Resolved.LocalScope.ids s.context) resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? (Resolved.LocalScope.ids s.context) id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "original typed row missing")
      | none => throw (IO.userError "original local name missing")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, by rw [original]; exact .unit, .unit, .unit⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [original]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | _ => throw (IO.userError "outside independent pure children")
termination_by sizeOf source
private structure Application (s : LocalTypeInputs) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates s.names s.context source core type
private def application (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Application s source) := do
  match original : source with
  | ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩ =>
      check (span.contains callee.span && span.contains argumentsSpan && argumentsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argumentsSpan.startByte)) "original one-argument ranges/order changed"
      let f ← expression s callee; let a ← expression s argument
      match shape : f.type with
      | .function parameterType resultType =>
          if same : a.type = parameterType then
            return ⟨.apply f.core a.core, resultType, by
              rw [original]; exact .call f.resolution f.lowered (shape ▸ f.typing) a.resolution a.lowered (same ▸ a.typing)⟩
          else throw (IO.userError "original argument type differs")
      | _ => throw (IO.userError "original callee is not Function")
  | _ => throw (IO.userError "not exactly one original call argument")
private def table (input output : Core.Ty) : TypeNameTable :=
  [(["F"], .function input output), (["A"], input), (["R"], output), (["Word"], .word), (["Bool"], .bool)]
private def content := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def staticCase (types : TypeNameTable) (text : String) (expected : Core.Expr) (result : Core.Ty)
    (names : List String) (annotations : List Core.Ty) : IO (Syntax.FunctionDecl × LocalTypeInputs) := do
  let source ← parsed text
  let ps ← declare types .empty source.value.signature.parameters.elements
  have _ := RuntimeParametersDeclare.complete ps.evidence
  check (decide (ps.inputs.names = (names.zipIdx.map (fun (name, n) => (name, ⟨owner, n⟩))).reverse ∧
    ps.inputs.context.values = annotations.reverse)) "original static parameter layout changed"
  let ⟨_, [⟨returnSpan, .returnStmt (some returned)⟩]⟩ := source.value.body | throw (IO.userError "not original singleton return")
  check (source.value.body.span.contains returnSpan && returnSpan.contains returned.span) "original return range changed"
  let a ← application ps.inputs returned
  have accepted := a.evidence.complete
  have _ := elaborateLocalFunctionApplication?_sound accepted
  have _ := a.evidence.hasType
  have _ := a.evidence.core_hasType
  have _ := a.evidence.result_unique (elaborateLocalFunctionApplication?_sound accepted)
  have wrong : ¬ LocalFunctionApplicationElaborates ps.inputs.names ps.inputs.context returned
      (.letE .unit (expected.weakenAt 0)) result := by intro evidence; cases evidence
  check (decide (a.core = expected ∧ a.type = result ∧
    elaborateLocalFunctionApplication? ps.inputs.names ps.inputs.context returned = some (expected, result) ∧
    elaborateLocalExpression? ps.inputs.names ps.inputs.context returned = none)) "independent exact call or old pure rejection changed"
  check (decide (Core.infer? ps.inputs.context.values (.letE .unit (expected.weakenAt 0)) = some result))
    "wrong-Core rejection ceased to be a same-typed contrast"
  have _ := wrong
  match clause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [annotation]⟩⟩ =>
      let m ← meaning types annotation
      if same : m.type = result then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          have _ : RuntimeFunctionHeader types source.value.signature result := ⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [clause]; exact .single (same ▸ m.evidence)⟩
          pure ()
        else throw (IO.userError "fixture header is not independently valid")
      else throw (IO.userError "fixture header disagrees")
  | _ => throw (IO.userError "fixture header shape changed")
  check ((compileRuntimeFunction? types owner source).isNone) "new root adapter leaked into old whole compiler"
  return (source, ps.inputs)
private def actualCase (types : TypeNameTable) (text : String) (expected : Core.Expr) (result : Core.Ty)
    (names : List String) (args : List TypedRuntimeArgument) : IO Core.Environment := do
  let (source, statics) ← staticCase types text expected result names (args.map (·.type))
  let actual ← bindArgs types .empty source.value.signature.parameters.elements args
  have _ := RuntimeParametersBind.complete actual.evidence
  have _ := RuntimeParametersBind.erase_values actual.evidence
  check (decide (actual.inputs.names = statics.names ∧ actual.inputs.toTypeInputs.context.values = statics.context.values ∧
    actual.inputs.environment.values = (args.map (·.value)).reverse))
    "same original parameter records did not retain actual values once"
  for fuel in List.range 13 do
    for store in [[], [w 91]] do
      check ((prepareRuntimeFunction? types owner source args).isNone && (runRuntimeFunction? types owner source args fuel store).isNone)
        "static root call was incorrectly integrated into old entry preparation/execution"
  return actual.inputs.environment.values
private theorem callPath {env captured : Core.Environment} {s t : Core.Store} {f a b : Core.Expr}
    {input output : Core.Ty} {v result : Core.Value} {fc ac bc : Nat} (k : List Core.Frame)
    (fp : ∀ k, Core.Steps fc ⟨.eval f env, k, s⟩ ⟨.ret (.closure input output b captured), k, s⟩)
    (ap : ∀ k, Core.Steps ac ⟨.eval a env, k, s⟩ ⟨.ret v, k, s⟩)
    (bp : ∀ k, Core.Steps bc ⟨.eval b (v :: captured), k, s⟩ ⟨.ret result, k, t⟩) :
    Core.Steps (fc + ac + bc + 3) ⟨.eval (.apply f a) env, k, s⟩ ⟨.ret result, k, t⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterApply
    ((fp _).trans (.cons .beginArgument ((ap _).trans (.cons .invokeClosure (bp k)))))
private def runPath (core : Core.Expr) (env : Core.Environment) (s t : Core.Store) (result : Core.Value) (cost : Nat)
    (path : Core.Steps cost (.initial core env s) (.final result t)) : IO Unit := do
  have _ := path.runStateful_done_iff (fuel := cost)
  for fuel in List.range (cost + 3) do
    check (match Core.runStateful fuel (.initial core env s) with
      | .done value final => decide (cost ≤ fuel ∧ value = result ∧ final = t)
      | .outOfFuel _ => decide (fuel < cost)
      | .fault .. => false) "independent Core-only path threshold/value/store changed"
  for spent in List.range cost do
    match stopped : Core.runStateful spent (.initial core env s) with
    | .outOfFuel checkpoint =>
        have _ := path.residual_of_outOfFuel stopped
        have _ := Core.runStateful_resume stopped (cost - spent)
        check (decide (Core.runStateful (cost - spent) checkpoint = .done result t)) "genuine call residual changed"
    | _ => throw (IO.userError "genuine suspended call missing")
private def closure (type : Core.Ty) : TypedRuntimeArgument :=
  ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
private def identityCases : IO Unit := do
  for argument in [(⟨.word, w 9, .word⟩ : TypedRuntimeArgument), ⟨.unit, .unit, .unit⟩,
      ⟨.cell .word, .cellRef .word 700, .cellRef⟩, closure .word] do
    let f := closure argument.type
    let env ← actualCase (table argument.type argument.type) content (.apply (.var 1) (.var 0)) argument.type ["f", "x"] [f, argument]
    for s in [[], [w 91]] do
      if same : env = [argument.value, f.value] then
        have p (k) : Core.Steps 6 ⟨.eval (.apply (.var 1) (.var 0)) env, k, s⟩ ⟨.ret argument.value, k, s⟩ := by
          subst env
          exact callPath k (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
        runPath _ env s s argument.value 6 (p [])
        check (decide (Core.runStateful 2 (.initial (.apply (.var 1) (.var 0)) env s) =
          .outOfFuel ⟨.ret f.value, [.applyArgument (.var 0) env], s⟩ ∧
          Core.runStateful 4 (.initial (.apply (.var 1) (.var 0)) env s) =
          .outOfFuel ⟨.ret argument.value, [.applyClosure argument.type argument.type (.var 0) []], s⟩)) "caller/captured call frames changed"
        have _ := p [.unaryApply .wordNot]
        let k : List Core.Frame := [.unaryApply .wordNot]
        check (match Core.runStateful 6 ⟨.eval (.apply (.var 1) (.var 0)) env, k, s⟩ with
          | .outOfFuel endpoint => decide (argument.type = .word ∧ endpoint = ⟨.ret argument.value, k, s⟩)
          | .fault error endpoint => decide (error = .invalidUnaryOperand .wordNot argument.value ∧ endpoint = ⟨.ret argument.value, k, s⟩)
          | _ => false) "arbitrary continuation endpoint was mistaken for completion or unconditional exhaustion"
      else throw (IO.userError "original actual order differs")
private def delayed : Nat → Core.Expr | 0 => .word (Core.Word.ofNatModulo 7) | n + 1 => .letE .unit (delayed n)
private theorem delayedTyped (n : Nat) (ctx : Core.Context) : Core.HasType ctx (delayed n) .word := by
  induction n generalizing ctx with
  | zero => exact .word
  | succ n ih => exact .letE .unit (ih _)
private theorem delayedPath (n : Nat) (env : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (delayed n) env, k, s⟩ ⟨.ret (w 7), k, s⟩ := by
  induction n generalizing env with
  | zero => exact .cons .word .refl
  | succ n ih => simpa [delayed, Nat.mul_succ, Nat.add_assoc] using Core.Steps.cons .enterLet (.cons .unit (.cons .bindLet (ih (.unit :: env))))
private def capturedAndCosts : IO Unit := do
  for x in [9, 14] do
    let captured : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (.var 1) [w 7],
      .closure (.cons .word .nil) (.var rfl)⟩
    let _ ← actualCase (table .word .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [captured, ⟨.word, w x, .word⟩]
    for s in [[], [w 91]] do
      runPath (.apply (.var 1) (.var 0)) [w x, captured.value] s s (w 7) 6
        (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl))
      check (decide (Core.runStateful 4 (.initial (.apply (.var 1) (.var 0)) [w x, captured.value] s) =
        .outOfFuel ⟨.ret (w x), [.applyClosure .word .word (.var 1) [w 7]], s⟩)) "caller value replaced lexical capture"
    for n in [0, 1, 4, 9] do
      let f : TypedRuntimeArgument := ⟨.function .word .word, .closure .word .word (delayed n) [], .closure .nil (delayedTyped n _)⟩
      let _ ← actualCase (table .word .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [f, ⟨.word, w x, .word⟩]
      have p : Core.Steps (3 * n + 6) (.initial (.apply (.var 1) (.var 0)) [w x, f.value] []) (.final (w 7) []) := by
        have raw := callPath (env := [w x, f.value]) (f := .var 1) (a := .var 0) []
          (fun _ => Core.Steps.cons (.var rfl) .refl) (fun _ => Core.Steps.cons (.var rfl) .refl) (delayedPath n [w x] [])
        have amount : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
        exact amount ▸ raw
      runPath _ _ [] [] (w 7) _ p
private def unitAndProduct : IO Unit := do
  let _ ← actualCase (table .unit .unit) "function invoke(f:F) returns(R){return f(());}"
    (.apply (.var 0) .unit) .unit ["f"] [closure .unit]
  let _ ← actualCase (table (.product .word .bool) (.product .word .bool)) "function invoke(f:F,x:Word,y:Bool) returns(R){return f((x,y));}"
    (.apply (.var 2) (.pair (.var 1) (.var 0))) (.product .word .bool) ["f", "x", "y"] [closure (.product .word .bool), ⟨.word, w 9, .word⟩, ⟨.bool, .bool true, .bool⟩]
  for s in [[], [w 91]] do
    runPath (.apply (.var 0) .unit) [(closure .unit).value] s s .unit 6
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons .unit .refl) (fun _ => .cons (.var rfl) .refl))
    runPath (.apply (.var 2) (.pair (.var 1) (.var 0))) [.bool true, w 9, (closure (.product .word .bool)).value] s s (.pair (w 9) (.bool true)) 10
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl) (.cons .applyPair .refl)))))
        (fun _ => .cons (.var rfl) .refl))
private def storeBoundaries : IO Unit := do
  let load : TypedRuntimeArgument := ⟨.function (.cell .word) .word, .closure (.cell .word) .word (.loadCell (.var 0)) [],
    .closure .nil (.loadCell (.var rfl))⟩
  let env ← actualCase (table (.cell .word) .word) content (.apply (.var 1) (.var 0)) .word ["f", "x"] [load, ⟨.cell .word, .cellRef .word 0, .cellRef⟩]
  check (decide (Core.runStateful 7 (.initial (.apply (.var 1) (.var 0)) env []) =
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩)) "structural typing falsely guaranteed allocated cells"
  runPath (.apply (.var 1) (.var 0)) [.cellRef .word 0, load.value] [w 23] [w 23] (w 23) 8
    (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))
  let alloc : TypedRuntimeArgument := ⟨.function .word (.cell .word), .closure .word (.cell .word) (.newCell .word (.var 0)) [],
    .closure .nil (.newCell (.var rfl))⟩
  let _ ← actualCase (table .word (.cell .word)) content (.apply (.var 1) (.var 0)) (.cell .word) ["f", "x"] [alloc, ⟨.word, w 9, .word⟩]
  for s in [[], [w 91]] do
    runPath (.apply (.var 1) (.var 0)) [w 9, alloc.value] s (s ++ [w 9]) (.cellRef .word s.length) 8
      (callPath [] (fun _ => .cons (.var rfl) .refl) (fun _ => .cons (.var rfl) .refl)
        (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))))
end LocalFunctionApplicationEntries
open LocalFunctionApplicationEntries
def frontendParsedLocalFunctionApplicationEntryTests : IO Unit := do
  identityCases; capturedAndCosts; unitAndProduct; storeBoundaries
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨17⟩))] do
    let _ ← staticCase (table type type) content (.apply (.var 1) (.var 0)) type ["f", "x"] [.function type type, type]
    pure ()
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedLocalFunctionApplications
/-! Original single-argument calls have independent child resolution, lowering
and typing. Nominal static contexts supply no values; this is not a runner or
an extension of the old pure expression or runtime-entry profiles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedLocalFunctionApplications
private def check (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"LocalCalls", by decide⟩], by decide⟩⟩, 43⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{ owner with declarationIndex := 99 },999⟩
private def names : LocalNameTable := [("f",id 7), ("c",foreign), ("x",id 2), ("g",id 1),
  ("y",id 3), ("unitFn",id 4), ("pairFn",id 5), ("manyFn",id 6),
  ("notFn",id 0), ("ghost",id 123), ("f",id 0)]
private def context (parameter result : Core.Ty) : Resolved.Context :=
  [(id 88,.unit), (id 7,.function parameter result), (foreign,.bool), (id 2,parameter),
    (id 1,.function parameter result), (id 3,parameter), (id 4,.function .unit result),
    (id 5,.function (.product parameter parameter) result),
    (id 6,.function (.product parameter (.product parameter parameter)) result),
    (id 0,.word), (id 7,.bool)]
private def parsed? (content : String) : IO (Option Syntax.Expr) := do
  let file : Syntax.SourceFile := ⟨⟨.main,"local-function-applications.sol"⟩,content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.expression (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      check (decide (source.span = ⟨file.id,0,content.utf8ByteSize⟩)) "complete original expression span changed"
      return some source
  | .reject _ _ => return none
  | .invariant _ => throw (IO.userError "expression parser invariant")
private def parsed (content : String) : IO Syntax.Expr := do
  let some source ← parsed? content | throw (IO.userError s!"complete call fixture did not parse: {content}")
  return source
private structure Child (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def child (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Child ctx source) := do
  match atSource : source with
  | ⟨_,.identifier name⟩ =>
      match named : names.lookup? name.value with
      | none => throw (IO.userError "independent child name absent")
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId,.var index,type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _,_ => throw (IO.userError "independent child context row absent")
  | ⟨_,.group inner⟩ =>
      let a ← child ctx inner
      return ⟨a.resolved,a.core,a.type,by rw [atSource]; exact .group a.resolution,a.lowered,a.typing⟩
  | ⟨_,.tuple ⟨_,[]⟩⟩ => return ⟨.unit,.unit,.unit,by rw [atSource]; exact .unit,.unit,.unit⟩
  | ⟨_,.tuple ⟨_,[left,right]⟩⟩ =>
      let a ← child ctx left; let b ← child ctx right
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨span,.tuple ⟨tupleSpan,first :: second :: third :: rest⟩⟩ =>
      let a ← child ctx first; let b ← child ctx ⟨span,.tuple ⟨tupleSpan,second :: third :: rest⟩⟩
      return ⟨.pair a.resolved b.resolved,.pair a.core b.core,.product a.type b.type,
        by rw [atSource]; exact .many a.resolution b.resolution,.pair a.lowered b.lowered,.pair a.typing b.typing⟩
  | ⟨_,.binary left ⟨_,.subtract⟩ right⟩ =>
      let a ← child ctx left; let b ← child ctx right
      if ta : a.type = .word then
        if tb : b.type = .word then
          return ⟨.binary .wordSub a.resolved b.resolved,.binary .wordSub a.core b.core,.word,
            by rw [atSource]; exact .subtract a.resolution b.resolution,
            .binary a.lowered b.lowered,.binary
              (show Resolved.HasType ctx a.resolved .word from ta ▸ a.typing)
              (show Resolved.HasType ctx b.resolved .word from tb ▸ b.typing)⟩
        else throw (IO.userError "right subtraction type mismatch")
      else throw (IO.userError "left subtraction type mismatch")
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child ctx condition; let a ← child ctx yes; let b ← child ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
            by rw [atSource]; exact .conditional c.resolution a.resolution b.resolution,
            .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole conditional arms disagree")
      else throw (IO.userError "conditional guard is not Bool")
  | _ => throw (IO.userError "outside independent pure child certificate")
termination_by sizeOf source
private structure Application (ctx : Resolved.Context) (source : Syntax.Expr) where
  core : Core.Expr
  type : Core.Ty
  evidence : LocalFunctionApplicationElaborates names ctx source core type
  typing : LocalFunctionApplicationHasType names ctx source type
private def application (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Application ctx source) := do
  match atSource : source with
  | ⟨_,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argumentsSpan &&
        argumentsSpan.contains argument.span && decide (callee.span.endByte ≤ argumentsSpan.startByte ∧
          argumentsSpan.startByte < argument.span.startByte ∧ argument.span.endByte < argumentsSpan.endByte))
        "original call children, delimiter ranges or written order changed"
      let f ← child ctx callee; let a ← child ctx argument
      match atType : f.type with
      | .function parameter result =>
          if same : a.type = parameter then
            let ft : Resolved.HasType ctx f.resolved (.function parameter result) := atType ▸ f.typing
            let argumentTyped : Resolved.HasType ctx a.resolved parameter := same ▸ a.typing
            return ⟨.apply f.core a.core,result,
              by rw [atSource]; exact .call f.resolution f.lowered ft a.resolution a.lowered argumentTyped,
              by rw [atSource]; exact .call (f.resolution.reflects_type ft) (a.resolution.reflects_type argumentTyped)⟩
          else throw (IO.userError "original singleton argument type mismatch")
      | _ => throw (IO.userError "callee is not a known Function")
  | _ => throw (IO.userError "not exactly one original root argument")
private def accepted (parameter result : Core.Ty) (text : String) (expected : Core.Expr) : IO Unit := do
  let source ← parsed text
  let ctx := context parameter result
  let original ← application ctx source
  have accepted := original.evidence.complete
  have _ := original.evidence.hasType
  have _ := original.evidence.core_hasType
  have _ := original.typing.elaborates_exact
  have _ := localFunctionApplicationHasType_iff_elaborates.mp original.typing
  have _ := (elaborateLocalFunctionApplication?_sound accepted).result_unique original.evidence
  have _ := original.typing.type_unique original.evidence.hasType
  have _ := elaborateLocalFunctionApplication?_iff.mp accepted
  have _ := elaborateLocalFunctionApplication?_core_hasType accepted
  match atSource : source with
  | ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ =>
      have shaped : elaborateLocalFunctionApplication? names ctx
          ⟨span,.call callee ⟨argumentsSpan,[argument]⟩⟩ = some (original.core,original.type) := by
        simpa only [atSource] using accepted
      have _ := elaborateLocalFunctionApplication?_children.mp shaped
      pure ()
  | _ => throw (IO.userError "independently accepted source lost its root call")
  check (decide (original.core = expected ∧ original.type = result ∧
    elaborateLocalFunctionApplication? names ctx source = some (expected,result) ∧
    Core.infer? ctx.values expected = some result ∧ elaborateLocalExpression? names ctx source = none))
    s!"original exact Core/type changed or the old pure profile gained calls: {text}"
  let wrong := Core.Expr.letE .unit (expected.weakenAt 0)
  check (decide (Core.infer? ctx.values wrong = some result)) "wrong provenance was not independently equally typed"
  if different : wrong ≠ original.core then
    have _ : ¬ LocalFunctionApplicationElaborates names ctx source wrong original.type :=
      fun other => different (other.result_unique original.evidence).1
    pure ()
  else throw (IO.userError "wrong-Core comparison collapsed")
private def rejected (parameter result : Core.Ty) (text : String) : IO Unit := do
  let source ← parsed text
  let ctx := context parameter result
  have _ := elaborateLocalFunctionApplication?_eq_none_iff (table := names) (context := ctx) (source := source)
  check (decide (elaborateLocalFunctionApplication? names ctx source = none ∧
    elaborateLocalExpression? names ctx source = none)) s!"unsupported whole application accepted: {text}"
private def firstMatch : IO Unit := do
  let source ← parsed "f(x)"
  let ctx := context .word .bool
  let original ← application ctx source
  let wrong := Core.Expr.apply (.var 4) (.var 3)
  check (decide (names.lookup? "f" = some (id 7) ∧ ctx.lookup? (id 7) = some (.function .word .bool) ∧
    Resolved.LocalScope.index? ctx.ids (id 7) = some 1 ∧ original.core = .apply (.var 1) (.var 3) ∧
    Core.infer? ctx.values wrong = some .bool)) "duplicate first-match or sparse positional lowering changed"
  if different : wrong ≠ original.core then
    have _ : ¬ LocalFunctionApplicationElaborates names ctx source wrong original.type :=
      fun other => different (other.result_unique original.evidence).1
    pure ()
  else throw (IO.userError "different function identity lost exact provenance")
  check (decide (elaborateLocalFunctionApplication? (("f",id 0) :: names) ctx source = none ∧
    elaborateLocalFunctionApplication? names ((id 7,.word) :: ctx) source = none))
    "changed first-match name/type was ignored despite retaining all old rows"
end ParsedLocalFunctionApplications
open ParsedLocalFunctionApplications

def frontendParsedLocalFunctionApplicationTests : IO Unit := do
  for (parameter,result) in [(Core.Ty.word,.bool), (.unit,.word), (.bool,.function .word .word),
      (.namedData ⟨91⟩,.namedData ⟨92⟩), (.word,.namedData ⟨91⟩),
      (.namedData ⟨91⟩,.function (.namedData ⟨92⟩) (.namedData ⟨93⟩)),
      (.cell .word,.product .word .bool), (.function .word .word,.unit),
      (.product .word .bool,.cell .bool)] do
    for text in ["f(x)", "(f)(x)", "((f))(((x)))", "f /* call */ ( /* arg */ x )"] do
      accepted parameter result text (.apply (.var 1) (.var 3))
    accepted parameter result "(c ? f : g)(x)" (.apply (.ifE (.var 2) (.var 1) (.var 4)) (.var 3))
    accepted parameter result "f(c ? x : y)" (.apply (.var 1) (.ifE (.var 2) (.var 3) (.var 5)))
    accepted parameter result "(c ? (f) : g)(c ? x : (y))"
      (.apply (.ifE (.var 2) (.var 1) (.var 4)) (.ifE (.var 2) (.var 3) (.var 5)))
    accepted parameter result "unitFn(())" (.apply (.var 6) .unit)
    accepted parameter result "pairFn((x,y))" (.apply (.var 7) (.pair (.var 3) (.var 5)))
    accepted parameter result "manyFn((x,y,x))" (.apply (.var 8) (.pair (.var 3) (.pair (.var 5) (.var 3))))
  for count in [1,3,8,24] do
    let grouped := (List.range count).foldl (fun inner _ => "(" ++ inner ++ ")") "x"
    accepted .word .bool ("f(" ++ grouped ++ ")") (.apply (.var 1) (.var 3))
  accepted .word .bool "f(x - y)" (.apply (.var 1) (.binary .wordSub (.var 3) (.var 5)))
  firstMatch
  let spaced ← parsed "f /* call */ ( /* arg */ x )"
  match spaced.value with
  | .call callee ⟨span,[argument]⟩ =>
      check (decide (callee.span.startByte = 0 ∧ callee.span.endByte = 1 ∧
        span.startByte = "f /* call */ ".utf8ByteSize ∧
        argument.span.startByte = "f /* call */ ( /* arg */ ".utf8ByteSize ∧
        argument.span.endByte = "f /* call */ ( /* arg */ x".utf8ByteSize)) "exact original byte offsets were recreated"
  | _ => throw (IO.userError "original comment-separated argument changed shape")
  have _ (id : Core.DataTypeId) : ¬ ∃ value, Core.ValueHasType value (.namedData id) := by
    rintro ⟨value,typed⟩; cases typed with
    | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found
  for text in ["f()", "f(x,y)", "f(x,y,x)", "pairFn(x,y)", "unitFn()", "unitFn(x)",
      "manyFn(((x,y),x))", "manyFn((x,y,x,()))", "notFn(x)", "x(x)", "f(c)",
      "missing(x)", "f(missing)", "ghost(x)", "f(ghost)", "(c ? f : missing)(x)",
      "(c ? f : notFn)(x)", "f((0 == 0) ? x : missing)", "f(c ? x : c)",
      "f(g(x))", "f(x)(y)", "(f(x))(y)", "(f(x))", "c ? f(x) : f(y)",
      "f.field(x)", "x.method(y)", "Pkg.f(x)", "f(x.field)",
      "(lam(z: Word){return z;})(x)", "f(lam(z: Word){return z;})"] do rejected .word .bool text
  for text in ["f(", "f(x", "f(x,)", "f(x,,y)", "f(x) trailing"] do
    check (← parsed? text).isNone "malformed or incomplete call acquired static meaning"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedFuelBounds
/-! A source-computed budget is shared by actual typed argument cases. The
budget is sufficient, not exact; rejected sources still do not execute. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)

private def parsed? (content : String) : IO (Option Syntax.FunctionDecl) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "fuel-bounds.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"SourceBudget", by decide⟩], by decide⟩⟩, 20⟩
private def types : TypeNameTable :=
  [(["Word"], .word), (["Bool"], .bool), (["Cell"], .cell .word),
    (["Fn"], .function .bool .bool), (["Opaque"], .namedData ⟨91⟩)]
private def word (value : Nat) := Core.Word.ofNatModulo value
private def wordArg (value : Nat) : TypedRuntimeArgument := ⟨.word, .word (word value), .word⟩
private def boolArg (value : Bool) : TypedRuntimeArgument := ⟨.bool, .bool value, .bool⟩
private def stores : List Core.Store := [[], [.word (word 7), .bool false, .cellRef .word 40]]

private def accepted (content : String) (parameterTypes : List Core.Ty)
    (expectedCore : Core.Expr) (returnType : Core.Ty) (expectedBound : Nat) :
    IO (Syntax.FunctionDecl × CompiledRuntimeFunction) := do
  let some declaration ← parsed? content | throw (IO.userError s!"{content}: incomplete declaration")
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (bound == expectedBound) s!"{content}: wrong source-only fuel bound {bound}"
  match declaration.value.body.value with
  | [⟨_, .returnStmt (some source)⟩] =>
      assertTrue (localExpressionFuelBound source == bound) "return wrapper charged extra fuel"
  | [⟨_, .returnStmt none⟩] => assertTrue (bound == 1) "bare return must cost one"
  | _ => throw (IO.userError "accepted fixture is not a singleton return")
  let some compiled := compileRuntimeFunction? types owner declaration
    | throw (IO.userError s!"{content}: compilation failed")
  assertTrue (decide (compiled.core = expectedCore ∧ compiled.returnType = returnType ∧
    compiled.inputs.context.values = parameterTypes.reverse)) "wrong exact static compilation"
  assertTrue (decide (Core.infer? compiled.inputs.context.values compiled.core = some returnType))
    "actual open Core failed typing"
  return (declaration, compiled)

private def runCase (declaration : Syntax.FunctionDecl) (arguments : List TypedRuntimeArgument)
    (fuel : Nat) (initialStore : Core.Store) : Option (Core.Ty × Core.StatefulRunResult) :=
  runRuntimeFunction? types owner declaration arguments fuel initialStore

private def completed (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) (value : Core.Value) (cost : Nat) : IO Unit := do
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (decide (0 < cost ∧ cost ≤ bound)) "path cost exceeded its source bound"
  assertTrue (decide (arguments.map (·.type) = compiled.inputs.context.values.reverse))
    "completion case did not pass the exact argument guard"
  for initialStore in stores do
    let initial := Core.State.initial compiled.core (arguments.reverse.map (·.value)) initialStore
    for fuel in List.range (bound + 3) do
      let observed := runCase declaration arguments fuel initialStore
      assertTrue (decide (observed = some (compiled.returnType, Core.runStateful fuel initial)))
        s!"runtime entry changed its actual compiled execution at fuel {fuel}"
      assertTrue (match observed with
        | some (type, .done result finalStore) =>
            decide (cost ≤ fuel ∧ type = compiled.returnType ∧ result = value ∧ finalStore = initialStore)
        | some (type, .outOfFuel suspended) =>
            decide (fuel < cost ∧ type = compiled.returnType ∧ suspended.store = initialStore)
        | _ => false) s!"wrong value, unchanged store, or exact path cost at fuel {fuel}"
      if bound ≤ fuel then
        assertTrue (decide (observed = some (compiled.returnType, .done value initialStore)))
          "source budget was insufficient for an actual matching argument case"
    if cost < bound then
      assertTrue (decide (runCase declaration arguments (bound - 1) initialStore =
        some (compiled.returnType, .done value initialStore))) "conservative budget became an exact cost"

private def rejectedArguments (declaration : Syntax.FunctionDecl) (compiled : CompiledRuntimeFunction)
    (arguments : List TypedRuntimeArgument) : IO Unit := do
  let bound := returnBodyFuelBound declaration.value.body
  assertTrue (decide (arguments.map (·.type) ≠ compiled.inputs.context.values.reverse))
    "rejection case accidentally satisfied the exact argument guard"
  assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
    "source bound bypassed preparation's actual argument guard"
  for initialStore in stores do
    for fuel in [0, bound, bound + 10] do
      assertTrue (runCase declaration arguments fuel initialStore).isNone
        "increasing the source budget bypassed the argument guard"

private def strictOperations :
    List (String × Core.BinaryOp × (Core.Word → Core.Word → Core.Word)) :=
  [("+", .wordAdd, Core.Word.add), ("-", .wordSub, Core.Word.sub),
    ("*", .wordMul, Core.Word.mul), ("/", .wordDiv, Core.Word.udiv), ("%", .wordMod, Core.Word.umod),
    ("&", .wordAnd, Core.Word.bitAnd),
    ("|", .wordOr, Core.Word.bitOr), ("^", .wordXor, Core.Word.bitXor)]

def frontendParsedFuelBoundTests : IO Unit := do
  let (bare, bareCompiled) ← accepted "function bare() { return; }" [] .unit .unit 1
  completed bare bareCompiled [] .unit 1
  rejectedArguments bare bareCompiled [boolArg false]
  for spelling in ["7", "0007", "0x0007", "(((7)))", "/* text adds no Core steps */ (0000007)"] do
    let (declaration, compiled) ← accepted
      ("function literal() returns (Word) { return " ++ spelling ++ "; }")
      [] (.word (word 7)) .word 1
    completed declaration compiled [] (.word (word 7)) 1
  for (symbol, operator, operation) in strictOperations do
    let (declaration, compiled) ← accepted
      ("function strict(x: Word, y: Word) returns (Word) { return ((x)) " ++ symbol ++ " y; }")
      [.word, .word] (.binary operator (.var 1) (.var 0)) .word 5
    for left in [0, 1, 7, 2 ^ 256 - 1] do
      for right in [0, 1, 9] do
        completed declaration compiled [wordArg left, wordArg right]
          (.word (operation (word left) (word right))) 5
  let (mask, maskCompiled) ← accepted
    "function mask(x: Word) returns (Word) { return ~(x); }"
    [.word] (.unary .wordNot (.var 0)) .word 3
  for value in [0, 1, 170, 2 ^ 256 - 1] do
    completed mask maskCompiled [wordArg value] (.word (word value).bitNot) 3
  let (greater, greaterCompiled) ← accepted
    "function greater(x: Word, y: Word) returns (Bool) { return x > y; }"
    [.word, .word] (.binary .wordGt (.var 1) (.var 0)) .bool 5
  for left in [0, 1, 2 ^ 255, 2 ^ 256 - 1] do
    for right in [0, 1, 2 ^ 256 - 1] do
      completed greater greaterCompiled [wordArg left, wordArg right]
        (.bool (decide (word left > word right))) 5
  let literal := fun value => Core.Expr.word (word value)
  let (precedence, precedenceCompiled) ← accepted
    "function precedence() returns (Bool) { return 1 | 2 ^ 3 & 4 + 5 * 2 > 2; }"
    [] (.binary .wordGt (.binary .wordOr (literal 1)
      (.binary .wordXor (literal 2) (.binary .wordAnd (literal 3)
        (.binary .wordAdd (literal 4) (.binary .wordMul (literal 5) (literal 2)))))) (literal 2))
    .bool 25
  completed precedence precedenceCompiled [] (.bool false) 25
  for (symbol, expectedCore) in [("&&", Core.Expr.ifE (.var 0)
      (.unary .boolNot (.var 0)) (.bool false)),
      ("||", Core.Expr.ifE (.var 0) (.bool true) (.unary .boolNot (.var 0)))] do
    let (declaration, compiled) ← accepted
      ("function short(c: Bool) returns (Bool) { return c " ++ symbol ++ " !c; }")
      [.bool] expectedCore .bool 6
    for choice in [false, true] do
      let isAnd := symbol == "&&"
      completed declaration compiled [boolArg choice] (.bool (!isAnd))
        (if choice == isAnd then 6 else 4)
  let (branch, branchCompiled) ← accepted
    "function branch(c: Bool, x: Word, y: Word) returns (Word) { return c ? x * y : x; }"
    [.bool, .word, .word] (.ifE (.var 2) (.binary .wordMul (.var 1) (.var 0)) (.var 1)) .word 8
  for choice in [false, true] do
    for left in [0, 7, 2 ^ 256 - 1] do
      completed branch branchCompiled [boolArg choice, wordArg left, wordArg 9]
        (.word (if choice then (word left).mul (word 9) else word left)) (if choice then 8 else 4)
  for arguments in [[], [boolArg false, wordArg 7], [wordArg 7, boolArg true, wordArg 9],
      [boolArg true, wordArg 7, boolArg false], [boolArg true, wordArg 7, wordArg 9, wordArg 1]] do
    rejectedArguments branch branchCompiled arguments
  let (arithmetic, arithmeticCompiled) ← accepted
    "function arithmetic(x: Word, y: Word) returns (Word) { return x * y > y ? x - y : x; }"
    [.word, .word] (.ifE (.binary .wordGt (.binary .wordMul (.var 1) (.var 0)) (.var 0))
      (.binary .wordSub (.var 1) (.var 0)) (.var 1)) .word 16
  for left in [0, 1, 7, 2 ^ 256 - 1] do
    for right in [0, 1, 9] do
      let selected := decide ((word left).mul (word right) > word right)
      completed arithmetic arithmeticCompiled [wordArg left, wordArg right]
        (.word (if selected then (word left).sub (word right) else word left)) (if selected then 16 else 12)
  let identity : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let cell : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  for (name, argument) in [("Fn", identity), ("Cell", cell)] do
    let (declaration, compiled) ← accepted
      (s!"function identity(x: {name}) returns ({name})" ++ " { return x; }")
      [argument.type] (.var 0) argument.type 1
    completed declaration compiled [argument] argument.value 1
  let (nominal, nominalCompiled) ← accepted
    "function nominal(x: Opaque) returns (Opaque) { return x; }"
    [.namedData ⟨91⟩] (.var 0) (.namedData ⟨91⟩) 1
  for arguments in [[], [boolArg false], [wordArg 0], [cell], [identity]] do
    rejectedArguments nominal nominalCompiled arguments
  let (division, divisionCompiled) ← accepted
    "function division(x: Word) returns (Word) { return x / x; }"
    [.word] (.binary .wordDiv (.var 0) (.var 0)) .word 5
  let (selectedDivision, selectedDivisionCompiled) ← accepted
    "function selected(c: Bool, x: Word) returns (Word) { return c ? x : x / x; }"
    [.bool, .word] (.ifE (.var 1) (.var 0) (.binary .wordDiv (.var 0) (.var 0))) .word 8
  for input in [0, 1, 7, Core.Word.maximum.val] do
    let quotient := word (if input == 0 then 0 else 1)
    completed division divisionCompiled [wordArg input] (.word quotient) 5
    for choice in [false, true] do
      completed selectedDivision selectedDivisionCompiled [boolArg choice, wordArg input]
        (.word (if choice then word input else quotient)) (if choice then 4 else 8)
  -- Bool || Word remains rejected even though its division now has bound five.
  for (content, expectedBound) in [
      ("function empty() {}", 0), ("function multiple() { return; return; }", 0),
      ("function call(x: Word) returns (Word) { return x(x); }", 0),
      ("function missing() returns (Word) { return missing; }", 1),
      ("function string() returns (Word) { return \"7\"; }", 1),
      (s!"function overflow() returns (Word)" ++ " { return " ++ s!"{Core.wordModulus};" ++ " }", 1),
      ("function skipped(c: Bool) returns (Bool) { return c && missing; }", 4),
      ("function skipped(c: Bool, x: Word) returns (Bool) { return c || x / x; }", 8),
      ("function skipped(c: Bool, x: Word) returns (Word) { return c ? x : x(c); }", 4),
      ("function wrong(c: Bool, x: Word) returns (Word) { return c ? x : c; }", 4),
      ("function wrong(x: Word) returns (Word) { return x > 0; }", 5)] do
    let some declaration ← parsed? content | throw (IO.userError "whole-rejection fixture failed parsing")
    assertTrue (returnBodyFuelBound declaration.value.body == expectedBound)
      "rejected syntax lost its numerical bound or zero placeholder"
    assertTrue (compileRuntimeFunction? types owner declaration).isNone "numeric budget certified acceptance"
    for arguments in [[], [boolArg false], [boolArg true], [wordArg 7],
        [boolArg false, wordArg 7], [boolArg true, wordArg 7], [boolArg false, boolArg true]] do
      assertTrue (prepareRuntimeFunction? types owner declaration arguments).isNone
        "a numeric budget bypassed whole preparation"
      for initialStore in stores do
        for fuel in [0, expectedBound, expectedBound + 20] do
          assertTrue (runCase declaration arguments fuel initialStore).isNone
            "an ample budget bypassed whole declaration rejection"
  for content in ["", "function incomplete()", "function f() { return;",
      "function f() { return; } trailing", "function f() { return; } /*"] do
    assertTrue (← parsed? content).isNone "incomplete input entered source budget tests"

end Tests
end
