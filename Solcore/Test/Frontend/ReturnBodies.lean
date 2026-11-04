import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.LocalApplication
import Solcore.Frontend.ReturnBody
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.ConditionalReturnBody
import Solcore.Frontend.RuntimeFunction
import Solcore.Frontend.TypedLetReturnBody
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RuntimeApplicationFunction
import Solcore.Frontend.RuntimeParameterDeclarations
import Solcore.Core.LocalFragment
import Solcore.Frontend.RuntimeParameters
import Solcore.Core.BitwiseLogic

/-!
# Return body tests

Return bodies, conditional returns, discarded statements and application insertion.
-/

section
-- leanmerge: from Solcore.Test.FrontendApplicationInsertionProperties
/-! Independent actual paths separate caller insertion from closure captures.
Neither arbitrary inserted values nor successful paths supply runtime typing. -/
set_option autoImplicit false
namespace Tests.FrontendApplicationInsertion
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Insertion", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 2⟩
private def names : LocalNameTable := [("f", fid), ("x", aid), ("f", gid)]
private def context : Resolved.Context := [(aid, .word), (fid, .function .word .word), (gid, .unit), (fid, .unit)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "application-insertion.sol"⟩, 249, 4⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def source : Syntax.Expr := ⟨span, .call (ref "f") ⟨span, [ref "x"]⟩⟩
private def core : Core.Expr := .apply (.var 1) (.var 0)
private theorem original : LocalFunctionApplicationElaborates names context source core .word :=
  .call (.identifier .head) (.var (.tail (by decide) .head)) (.var (.tail (by decide) .head))
    (.identifier (.tail (by decide) .head)) (.var .head) (.var .head)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def closure (n : Nat) (captured : Core.Value) : Core.Value := .closure .unit .unit (delay n 1) [captured]
private def environment (n : Nat) (argument captured : Core.Value) : Resolved.Environment :=
  [(aid, argument), (fid, closure n captured), (gid, .unit), (fid, .bool false)]
private def values (n : Nat) (argument captured : Core.Value) : Core.Environment := (environment n argument captured).values
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
private theorem raw (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    LocalFunctionApplicationEvaluates names (environment n argument captured) store source captured store :=
  .call (.identifier .head (.tail (by decide) .head)) (.identifier (.tail (by decide) .head) .head)
    (bodyRaw n 1 argument [captured] captured store rfl)
private theorem evaluated (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    Core.Evaluates (values n argument captured) store core captured store :=
  .apply (.var rfl) (.var rfl) (bodyRaw n 1 argument [captured] captured store rfl)
private theorem costed (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    LocalFunctionApplicationEvaluatesWithCost names (environment n argument captured) store source captured store (3 * n + 6) := by
  have count : 3 * n + 6 = 1 + 1 + (3 * n + 1) + 3 := by omega
  rw [count]
  exact .call (.identifier .head (.tail (by decide) .head)) (.identifier (.tail (by decide) .head) .head)
    (bodyPath n 1 argument [captured] captured store [] rfl)
private theorem manual (n : Nat) (argument captured : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 6) ⟨.eval core (values n argument captured), k, store⟩ ⟨.ret captured, k, store⟩ := by
  have path := CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (bodyPath n 1 argument [captured] captured store [] rfl)
      (function := (.var 1 : Core.Expr)) (argument := (.var 0 : Core.Expr))
      (environment := values n argument captured) (parameterType := .unit) (resultType := .unit) (continuation := k)
  have count : 3 * n + 6 = 1 + 1 + (3 * n + 1) + 3 := by omega
  rw [count]; exact path

theorem sparse_original_source_and_actual_untyped_capture_have_independent_paths
    (n : Nat) (argument captured : Core.Value) (store : Core.Store) :
    LocalFunctionApplicationElaborates names context source core .word ∧
    LocalFunctionApplicationEvaluates names (environment n argument captured) store source captured store ∧
    LocalFunctionApplicationEvaluatesWithCost names (environment n argument captured) store source captured store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (values n argument captured), k, store⟩ ⟨.ret captured, k, store⟩ :=
  ⟨original, raw n argument captured store, costed n argument captured store, manual n argument captured store⟩

theorem paired_cost_is_chosen_once_before_all_continuations
    (n : Nat) (argument captured inserted : Core.Value) (store : Core.Store)
    (leading suffix : Core.Environment) (split : leading ++ suffix = values n argument captured) :
    ∃ cost, cost = 3 * n + 6 ∧ ∀ k,
      Core.Steps cost ⟨.eval core (leading ++ suffix), k, store⟩ ⟨.ret captured, k, store⟩ ∧
      Core.Steps cost ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret captured, k, store⟩ := by
  obtain ⟨cost, paths⟩ := original.core_insertion_paths leading suffix inserted (split ▸ evaluated n argument captured store)
  have same := ((paths []).1.final_unique (split ▸ manual n argument captured store [])).1
  exact ⟨cost, same, paths⟩

theorem raw_insertion_and_reflection_keep_literal_values_and_both_stores
    (n : Nat) (argument captured inserted : Core.Value) (store : Core.Store)
    (leading suffix : Core.Environment) (split : leading ++ suffix = values n argument captured) :
    Core.Evaluates (leading ++ inserted :: suffix) store (core.weakenAt leading.length) captured store ∧
    Core.Evaluates (leading ++ suffix) store core captured store := by
  have added := (original.core_evaluates_insert_iff leading suffix inserted).mpr (split ▸ evaluated n argument captured store)
  exact ⟨added, (original.core_evaluates_insert_iff leading suffix inserted).mp added⟩

theorem known_closed_cost_transports_and_reflects_before_any_pending_frames
    (n : Nat) (argument captured inserted : Core.Value) (store : Core.Store)
    (leading suffix : Core.Environment) (split : leading ++ suffix = values n argument captured) (k : List Core.Frame) :
    Core.Steps (3 * n + 6) ⟨.eval (core.weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret captured, k, store⟩ ∧
    Core.Steps (3 * n + 6) ⟨.eval core (leading ++ suffix), k, store⟩ ⟨.ret captured, k, store⟩ ∧
    (Core.Steps (3 * n + 6) (.initial (core.weakenAt leading.length) (leading ++ inserted :: suffix) store) (.final captured store) ↔
      Core.Steps (3 * n + 6) (.initial core (leading ++ suffix) store) (.final captured store)) := by
  have closed : Core.Steps (3 * n + 6) (.initial core (leading ++ suffix) store) (.final captured store) := split ▸ manual n argument captured store []
  have insertedPath := (original.core_steps_insert_iff leading suffix inserted).mpr closed
  have recovered := (original.core_steps_insert_iff leading suffix inserted).mp insertedPath
  exact ⟨original.core_steps_insert leading suffix inserted recovered k,
    original.core_steps_reflect_insert leading suffix inserted insertedPath k,
    original.core_steps_insert_iff leading suffix inserted⟩

theorem inserted_types_need_no_actual_inhabitants_or_source_context_equality
    (a b inserted : Core.Ty) (definitions : Core.DataEnvironment) :
    Core.HasType [a, inserted, .function a b] (core.weakenAt 1) b definitions ∧
    Core.HasType [a, .function a b] core b definitions := by
  have added := (original.core_hasType_insert_iff [a] [.function a b] inserted).mpr
    (show Core.HasType [a, .function a b] core b definitions from .apply (.var rfl) (.var rfl))
  exact ⟨added, (original.core_hasType_insert_iff [a] [.function a b] inserted).mp added⟩

private def insertedValues (cut n : Nat) (argument captured inserted : Core.Value) : Core.Environment :=
  (values n argument captured).take cut ++ inserted :: (values n argument captured).drop cut
private def before (n : Nat) (argument captured : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (values n argument captured), [.applyClosure .unit .unit (delay n 1) [captured]], store⟩
private def after (cut n : Nat) (argument captured inserted : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval ((Core.Expr.var 0).weakenAt cut) (insertedValues cut n argument captured inserted),
    [.applyClosure .unit .unit (delay n 1) [captured]], store⟩
private def invoked (n : Nat) (argument captured : Core.Value) (store : Core.Store) : Core.State :=
  ⟨.eval (delay n 1) [argument, captured], [], store⟩
private theorem insertedPath (cut n : Nat) (argument captured inserted : Core.Value) (store : Core.Store) (small : cut < 3) :
    Core.Steps (3 * n + 6) (.initial (core.weakenAt cut) (insertedValues cut n argument captured inserted) store) (.final captured store) := by
  have length : ((values n argument captured).take cut).length = cut := by simp [values, environment, Resolved.LocalScope.values]; omega
  have path := original.core_steps_insert ((values n argument captured).take cut) ((values n argument captured).drop cut) inserted
    (by simpa only [List.take_append_drop, Core.State.initial, Core.State.final] using manual n argument captured store []) []
  simpa only [length, Core.State.initial, Core.State.final, insertedValues] using path

theorem each_prefix_has_a_distinct_caller_checkpoint_but_the_same_actual_invocation
    (cut n : Nat) (argument captured inserted : Core.Value) (store : Core.Store) (small : cut < 3) :
    Core.runStateful 3 (.initial core (values n argument captured) store) = .outOfFuel (before n argument captured store) ∧
    Core.runStateful 3 (.initial (core.weakenAt cut) (insertedValues cut n argument captured inserted) store) = .outOfFuel (after cut n argument captured inserted store) ∧
    before n argument captured store ≠ after cut n argument captured inserted store ∧
    Core.runStateful 5 (.initial core (values n argument captured) store) = .outOfFuel (invoked n argument captured store) ∧
    Core.runStateful 5 (.initial (core.weakenAt cut) (insertedValues cut n argument captured inserted) store) = .outOfFuel (invoked n argument captured store) := by
  have options : cut = 0 ∨ cut = 1 ∨ cut = 2 := by omega
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rcases options with rfl | rfl | rfl <;> simp only [core, after, Core.Expr.weakenAt] <;> rfl
  · intro same
    have lengths := congrArg (fun s : Core.State => match s.control with | .eval _ env => env.length | _ => 0) same
    rcases options with rfl | rfl | rfl <;> change 4 = 5 at lengths <;> cases lengths
  · cases n <;> rfl
  · rcases options with rfl | rfl | rfl <;> cases n <;> simp only [core, Core.Expr.weakenAt] <;> rfl

theorem each_genuine_checkpoint_retains_its_own_residual_and_full_resumption
    (cut n additional : Nat) (argument captured inserted : Core.Value) (store : Core.Store) (small : cut < 3) :
    Core.Steps (3 * n + 3) (before n argument captured store) (.final captured store) ∧
    Core.Steps (3 * n + 3) (after cut n argument captured inserted store) (.final captured store) ∧
    Core.runStateful additional (before n argument captured store) = Core.runStateful (3 + additional) (.initial core (values n argument captured) store) ∧
    Core.runStateful additional (after cut n argument captured inserted store) =
      Core.runStateful (3 + additional) (.initial (core.weakenAt cut) (insertedValues cut n argument captured inserted) store) := by
  have stops := each_prefix_has_a_distinct_caller_checkpoint_but_the_same_actual_invocation cut n argument captured inserted store small
  have remain : 3 * n + 6 - 3 = 3 * n + 3 := by omega
  refine ⟨?_, ?_, Core.runStateful_resume stops.1 additional, Core.runStateful_resume stops.2.1 additional⟩
  · simpa only [remain] using ((manual n argument captured store []).residual_of_outOfFuel stops.1).2
  · simpa only [remain] using ((insertedPath cut n argument captured inserted store small).residual_of_outOfFuel stops.2.1).2

theorem every_closed_fuel_threshold_agrees_without_equal_saved_states
    (cut n fuel : Nat) (argument captured inserted : Core.Value) (store : Core.Store) (small : cut < 3) :
    (Core.runStateful fuel (.initial core (values n argument captured) store) = .done captured store ↔ 3 * n + 6 ≤ fuel) ∧
    (Core.runStateful fuel (.initial (core.weakenAt cut) (insertedValues cut n argument captured inserted) store) = .done captured store ↔ 3 * n + 6 ≤ fuel) :=
  ⟨(manual n argument captured store []).runStateful_done_iff,
    (insertedPath cut n argument captured inserted store small).runStateful_done_iff⟩

theorem a_retained_continuation_endpoint_may_fault_immediately (inserted : Core.Value) (store : Core.Store) :
    Core.Steps 6 ⟨.eval (core.weakenAt 0) (inserted :: values 0 .unit .unit), [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ :=
  ⟨original.core_steps_insert [] (values 0 .unit .unit) inserted (manual 0 .unit .unit store []) _, rfl⟩

private def constructsClosure : Core.Expr :=
  .apply (.lambda .unit (.function .unit .unit) (.lambda .unit .unit (.var 0))) .unit
private def resultClosure (extra : Core.Environment) : Core.Value := .closure .unit .unit (.var 0) (.unit :: extra)
theorem closure_construction_outside_the_child_profile_breaks_literal_result_insertion (store : Core.Store) :
    Core.HasType [] constructsClosure (.function .unit .unit) ∧
    Core.HasType [.bool] (constructsClosure.weakenAt 0) (.function .unit .unit) ∧
    Core.Steps 6 (.initial constructsClosure [] store) (.final (resultClosure []) store) ∧
    Core.Steps 6 (.initial (constructsClosure.weakenAt 0) [.bool true] store) (.final (resultClosure [.bool true]) store) ∧
    resultClosure [] ≠ resultClosure [.bool true] ∧
    ¬ ∃ table context source type, LocalFunctionApplicationElaborates table context source constructsClosure type := by
  refine ⟨.apply (.lambda .unit (.function .unit .unit) (.lambda .unit .unit (.var rfl))) .unit, ?_,
    .cons .enterApply (.cons .lambda (.cons .beginArgument (.cons .unit (.cons .invokeClosure (.cons .lambda .refl))))), ?_, ?_, ?_⟩
  · simp only [constructsClosure, Core.Expr.weakenAt]
    exact .apply (.lambda .unit (.function .unit .unit) (.lambda .unit .unit (.var rfl))) .unit
  · simp only [constructsClosure, Core.Expr.weakenAt]
    exact .cons .enterApply (.cons .lambda (.cons .beginArgument (.cons .unit (.cons .invokeClosure (.cons .lambda .refl)))))
  · intro same
    have captured := Core.Value.closure.inj same
    cases captured.2.2.2
  · rintro ⟨table, context, source, type, claimed⟩
    cases claimed with
    | call _ lowered _ _ _ _ => cases lowered.localFragment

end Tests.FrontendApplicationInsertion
end

section
-- leanmerge: from Solcore.Test.FrontendApplicationReturnBodyProperties
/-! The original singleton return contributes no machine action. Static
provenance, actual closure paths and runtime-world assumptions stay separate. -/
set_option autoImplicit false
namespace Tests.FrontendApplicationReturnBody
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ApplicationReturn", by decide⟩], by decide⟩⟩, 8⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def gid : Resolved.LocalId := ⟨owner, 91⟩
private def cid : Resolved.LocalId := ⟨owner, 1234⟩
private def aid : Resolved.LocalId := ⟨{ owner with declarationIndex := 4 }, 999⟩
private def names : LocalNameTable := [("x", aid), ("f", fid), ("f", gid), ("c", cid)]
private def context (a b : Core.Ty) : Resolved.Context := [(aid, a), (fid, .function a b), (gid, .function a b), (cid, .bool)]
private def bundle (a b : Core.Ty) (f x : Core.Value)
    (ft : Core.ValueHasType f (.function a b)) (xt : Core.ValueHasType x a) : LocalInputs :=
  ⟨[⟨"x", aid, a, x, xt⟩, ⟨"f", fid, .function a b, f, ft⟩, ⟨"f", gid, .function a b, f, ft⟩,
      ⟨"c", cid, .bool, .bool true, .bool⟩], by change ([aid, fid, gid, cid] : List Resolved.LocalId).Nodup; decide⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "application-return.sol"⟩, 31, 4⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def call (s t : Syntax.SourceSpan) : Syntax.Expr := ⟨s, .call (ref s "f") ⟨t, [ref t "x"]⟩⟩
private def wrap (b r : Syntax.SourceSpan) (source : Syntax.Expr) : Syntax.Block := ⟨b, [⟨r, .returnStmt (some source)⟩]⟩
private def body : Syntax.Block := wrap span span (call span span)
private def core : Core.Expr := .apply (.var 1) (.var 0)
private theorem runBody (actual : LocalInputs) (fuel : Nat) (store : Core.Store) :
    actual.runApplicationReturnBody? fuel body store = actual.runApplication? fuel (call span span) store :=
  actual.runApplicationReturnBody?_return fuel span span (call span span) store
private theorem child (a b : Core.Ty) (s t : Syntax.SourceSpan) :
    LocalFunctionApplicationElaborates names (context a b) (call s t) core b :=
  .call (parameterType := a) (.identifier (.tail (by change "x" ≠ "f"; decide) .head))
    (.var (.tail (by change aid ≠ fid; decide) .head)) (.var (.tail (by change aid ≠ fid; decide) .head))
    (.identifier .head) (.var .head) (.var .head)
private theorem whole (a b : Core.Ty) (bs rs s t : Syntax.SourceSpan) :
    LocalApplicationReturnBodyElaborates names (context a b) (wrap bs rs (call s t)) core b := .application (child a b s t)
private theorem callCost (a b : Core.Ty) (closureBody : Core.Expr) (captured : Core.Environment) (x value : Core.Value)
    (ft : Core.ValueHasType (.closure a b closureBody captured) (.function a b)) (xt : Core.ValueHasType x a)
    (store final : Core.Store) (cost : Nat)
    (path : Core.Steps cost (.initial closureBody (x :: captured) store) (.final value final)) :
    LocalFunctionApplicationEvaluatesWithCost (bundle a b (.closure a b closureBody captured) x ft xt).names
      (bundle a b (.closure a b closureBody captured) x ft xt).environment store (call span span) value final (1 + 1 + cost + 3) :=
  .call (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (by change aid ≠ fid; decide) .head)) (.identifier .head .head) path

theorem arbitrary_spans_and_types_retain_independent_original_provenance (a b : Core.Ty) (bs rs s t : Syntax.SourceSpan) :
    elaborateLocalApplicationReturnBody? names (context a b) (wrap bs rs (call s t)) = some (core, b) ∧
    LocalApplicationReturnBodyElaborates names (context a b) (wrap bs rs (call s t)) core b ∧
    LocalApplicationReturnBodyHasType names (context a b) (wrap bs rs (call s t)) b ∧
    Core.HasType (context a b).values core b ∧
    ∃ c, LocalApplicationReturnBodyElaborates names (context a b) (wrap bs rs (call s t)) c b := by
  have original := whole a b bs rs s t
  have typed : LocalApplicationReturnBodyHasType names (context a b) (wrap bs rs (call s t)) b := .application (child a b s t).hasType
  exact ⟨elaborateLocalApplicationReturnBody?_iff.mpr original, elaborateLocalApplicationReturnBody?_sound original.complete,
    localApplicationReturnBodyHasType_iff_elaborates.mpr ⟨core, original⟩, original.core_hasType, typed.elaborates_exact⟩

theorem a_same_typed_other_function_is_not_the_original_body (a b : Core.Ty)
    {other : Core.Ty} (candidate : LocalApplicationReturnBodyHasType names (context a b) body other) :
    b = other ∧ Core.HasType (context a b).values core b ∧
    Core.HasType (context a b).values (.apply (.var 2) (.var 0)) b ∧
    ¬ LocalApplicationReturnBodyElaborates names (context a b) body (.apply (.var 2) (.var 0)) b := by
  have original := whole a b span span span span
  refine ⟨original.hasType.type_unique candidate, elaborateLocalApplicationReturnBody?_core_hasType original.complete,
    .apply (.var rfl) (.var rfl), ?_⟩
  intro other
  have impossible := (original.result_unique other).1
  cases impossible

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
private theorem counted (n : Nat) (store : Core.Store) : LocalFunctionApplicationEvaluatesWithCost
    (inputs n).names (inputs n).environment store (call span span) .unit store (3 * n + 6) := by
  have actual := callCost .unit .unit (delay n 1) [.unit] .unit .unit (delayedTyped n) .unit store store (3 * n + 1) (delayPath n 1 [.unit] store [] rfl)
  have costs : 1 + 1 + (3 * n + 1) + 3 = 3 * n + 6 := by omega
  exact costs ▸ actual
private theorem raw (n : Nat) (store : Core.Store) : LocalApplicationReturnBodyEvaluates
    (inputs n).names (inputs n).environment store body .unit store :=
  .application (.call (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (by change aid ≠ fid; decide) .head)) (.identifier .head .head)
    (Core.steps_from_initial_sound (delayPath n 1 [.unit] store [] rfl)))
private theorem bodyCost (n : Nat) (store : Core.Store) : LocalApplicationReturnBodyEvaluatesWithCost
    (inputs n).names (inputs n).environment store body .unit store (3 * n + 6) := .application (counted n store)

theorem independent_body_cost_is_the_actual_child_cost (n : Nat) (store : Core.Store)
    {value : Core.Value} {final : Core.Store} {cost : Nat}
    (candidate : LocalApplicationReturnBodyEvaluatesWithCost (inputs n).names (inputs n).environment store body value final cost) :
    value = .unit ∧ final = store ∧ cost = 3 * n + 6 ∧
    LocalApplicationReturnBodyEvaluates (inputs n).names (inputs n).environment store body value final ∧
    ∃ actual, LocalApplicationReturnBodyEvaluatesWithCost (inputs n).names (inputs n).environment store body .unit store actual := by
  have same := candidate.deterministic (bodyCost n store)
  have erased := candidate.erase
  have values := erased.deterministic (raw n store)
  exact ⟨values.1, values.2, same.2.2, erased,
    localApplicationReturnBodyEvaluates_iff_exists_cost.mp ((localApplicationReturnBodyEvaluates_iff_exists_cost).mpr ((raw n store).exists_cost))⟩

theorem original_core_correspondence_keeps_the_cost_before_all_continuations (n : Nat) (store : Core.Store) :
    Core.Evaluates (inputs n).environment.values store core .unit store ∧
    LocalApplicationReturnBodyEvaluatesWithCost (inputs n).names (inputs n).environment store body .unit store (3 * n + 6) ∧
    ∀ k, Core.Steps (3 * n + 6) ⟨.eval core (inputs n).environment.values, k, store⟩ ⟨.ret .unit, k, store⟩ := by
  have e : LocalApplicationReturnBodyElaborates (inputs n).names (inputs n).context body core .unit := whole .unit .unit span span span span
  have closed := (e.evaluatesWithCost_iff_steps (inputs n).sameIds).mp (bodyCost n store)
  exact ⟨(e.evaluates_iff (inputs n).sameIds).mp (raw n store),
    (e.evaluatesWithCost_iff_steps (inputs n).sameIds).mpr closed,
    (bodyCost n store).toStepsWithContinuation e (inputs n).sameIds⟩

theorem wrapper_preserves_full_options_even_for_rejected_children (actual : LocalInputs) (bs rs : Syntax.SourceSpan)
    (source : Syntax.Expr) (fuel : Nat) (store : Core.Store) :
    actual.checkApplicationReturnBody? (wrap bs rs source) = actual.checkApplication? source ∧
    actual.runApplicationReturnBody? fuel (wrap bs rs source) store = actual.runApplication? fuel source store :=
  ⟨actual.checkApplicationReturnBody?_return bs rs source, actual.runApplicationReturnBody?_return fuel bs rs source store⟩

theorem body_completion_reflects_typing_and_independent_cost (n : Nat) (store : Core.Store) :
    (inputs n).checkApplicationReturnBody? body = some (core, .unit) ∧
    LocalApplicationReturnBodyHasType (inputs n).names (inputs n).context body .unit ∧
    ∃ cost, LocalApplicationReturnBodyEvaluatesWithCost (inputs n).names (inputs n).environment store body .unit store cost ∧ cost ≤ 3 * n + 6 := by
  have e : LocalApplicationReturnBodyElaborates (inputs n).names (inputs n).context body core .unit := whole .unit .unit span span span span
  have checked := LocalInputs.checkApplicationReturnBody?_iff_elaborates.mpr e
  have done := LocalInputs.runApplicationReturnBody?_eq_some_iff.mpr
    ⟨core, checked, ((original_core_correspondence_keeps_the_cost_before_all_continuations n store).2.2 []).runStateful_done_iff.mpr (Nat.le_refl _)⟩
  exact ⟨checked, LocalInputs.runApplicationReturnBody?_done_iff_typed_cost.mp done⟩

theorem child_fuel_and_unbounded_actual_cost_transfer_without_extra_return_steps (n fuel : Nat) (store : Core.Store) :
    ((inputs n).runApplicationReturnBody? fuel body store = some (.unit, .done .unit store) ↔ 3 * n + 6 ≤ fuel) ∧
    ((∃ cp, (inputs n).runApplicationReturnBody? fuel body store = some (.unit, .outOfFuel cp)) ↔ fuel < 3 * n + 6) := by
  rw [runBody]
  exact ⟨LocalInputs.runApplication?_done_iff_of_cost (inputs := inputs n) (child .unit .unit span span).hasType (counted n store),
    LocalInputs.runApplication?_outOfFuel_iff_of_cost (inputs := inputs n) (child .unit .unit span span).hasType (counted n store)⟩

private def checkpoint (n : Nat) (store : Core.Store) : Core.State :=
  ⟨.eval (.var 0) (inputs n).environment.values, [.applyClosure .unit .unit (delay n 1) [.unit]], store⟩
theorem body_and_child_have_the_identical_genuine_checkpoint_and_resumption (n additional : Nat) (store : Core.Store) :
    (inputs n).runApplicationReturnBody? 3 body store = some (.unit, .outOfFuel (checkpoint n store)) ∧
    (inputs n).runApplication? 3 (call span span) store = some (.unit, .outOfFuel (checkpoint n store)) ∧
    Core.Steps (3 * n + 3) (checkpoint n store) (.final .unit store) ∧
    (inputs n).runApplicationReturnBody? (3 + additional) body store = some (.unit, Core.runStateful additional (checkpoint n store)) := by
  have stopped : (inputs n).runApplication? 3 (call span span) store = some (.unit, .outOfFuel (checkpoint n store)) :=
    LocalInputs.runApplication?_eq_some_iff.mpr ⟨core, (child .unit .unit span span).complete, rfl⟩
  have remaining : 3 * n + 6 - 3 = 3 * n + 3 := by omega
  refine ⟨?_, stopped, ?_, ?_⟩
  · exact ((inputs n).runApplicationReturnBody?_return 3 span span (call span span) store).trans stopped
  · simpa only [remaining] using (LocalInputs.runApplication?_residual_of_outOfFuel (counted n store) stopped).2
  · exact ((inputs n).runApplicationReturnBody?_return _ span span (call span span) store).trans (LocalInputs.runApplication?_resume stopped additional)

private def reader : Core.Value := .closure .unit .word (.loadCell (.var 1)) [.cellRef .word 0]
private theorem readerTyped : Core.ValueHasType reader (.function .unit .word) := .closure (.cons .cellRef .nil) (.loadCell (.var rfl))
private def readerInputs : LocalInputs := bundle .unit .word reader .unit readerTyped .unit
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private theorem readerCost (v : Core.Value) : LocalFunctionApplicationEvaluatesWithCost readerInputs.names readerInputs.environment [v] (call span span) v [v] 8 :=
  callCost .unit .word (.loadCell (.var 1)) [.cellRef .word 0] .unit v readerTyped .unit [v] [v] 3
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
private theorem readerRuntime : Core.RuntimeEnvironmentHasTypes [.word] readerInputs.environment.values readerInputs.context.values := by
  have f : Core.RuntimeValueHasType [.word] reader (.function .unit .word) := .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))
  exact .cons .unit (.cons f (.cons f (.cons .bool .nil)))
theorem runtime_world_laws_transport_through_full_result_equality (n fuel : Nat) (error : Core.MachineFault) (fault : Core.State) :
    readerInputs.runApplicationReturnBody? 8 body [w n] = some (.word, .done (w n) [w n]) ∧
    (∃ world, Core.WorldExtends [.word] world ∧ Core.RuntimeStoreHasTypes world [w n] ∧ Core.RuntimeValueHasType world (w n) .word) ∧
    readerInputs.runApplicationReturnBody? fuel body [w n] ≠ some (.word, .fault error fault) := by
  have st : Core.StoreHasTypes [.word] [w n] := Core.StoreHasTypes.nil.allocate .word .word
  obtain ⟨_, final, v, cost, _, _, _, actual, thresholds⟩ := LocalInputs.runApplication?_runtime_has_exact_cost (inputs := readerInputs) (child .unit .word span span).hasType readerRuntime st ⟨w n, [w n], (readerCost (w n)).erase⟩
  obtain ⟨rfl, rfl, rfl⟩ := actual.deterministic (readerCost (w n))
  have done := (thresholds 8).1.mpr (Nat.le_refl _)
  exact ⟨(readerInputs.runApplicationReturnBody?_return 8 span span (call span span) [w n]).trans done,
    (LocalInputs.runApplication?_runtime_done_sound readerRuntime st done).2,
    by rw [runBody]
       exact LocalInputs.runApplication?_runtime_never_faults readerRuntime st (call span span) fuel .word error fault⟩

theorem missing_cells_and_wrong_payloads_are_not_hidden_by_return :
    readerInputs.runApplicationReturnBody? 7 body [] = some (.word, .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0), [.loadCellApply], []⟩) ∧
    readerInputs.runApplicationReturnBody? 8 body [.bool true] = some (.word, .done (.bool true) [.bool true]) := by
  constructor
  · exact LocalInputs.runApplicationReturnBody?_eq_some_iff.mpr ⟨core, (whole .unit .word span span span span).complete, rfl⟩
  · rw [runBody]
    exact (LocalInputs.runApplication?_done_iff_of_cost (inputs := readerInputs) (child .unit .word span span).hasType (readerCost (.bool true))).mpr (Nat.le_refl 8)

private def allocator : Core.Value := .closure .word (.cell .word) (.newCell .word (.var 0)) []
private def allocatorInputs : LocalInputs := bundle .word (.cell .word) allocator (w 7) (.closure .nil (.newCell (.var rfl))) .word
theorem return_keeps_the_actual_allocation_effect (store : Core.Store) :
    LocalApplicationReturnBodyEvaluatesWithCost allocatorInputs.names allocatorInputs.environment store body (.cellRef .word store.length) (store ++ [w 7]) 8 ∧
    allocatorInputs.runApplicationReturnBody? 8 body store = some (.cell .word, .done (.cellRef .word store.length) (store ++ [w 7])) := by
  have actual : LocalFunctionApplicationEvaluatesWithCost allocatorInputs.names allocatorInputs.environment store (call span span)
      (.cellRef .word store.length) (store ++ [w 7]) 8 :=
    callCost .word (.cell .word) (.newCell .word (.var 0)) [] (w 7) (.cellRef .word store.length) (.closure .nil (.newCell (.var rfl))) .word store (store ++ [w 7]) 3
      (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
  refine ⟨.application actual, ?_⟩
  rw [runBody]
  exact (LocalInputs.runApplication?_done_iff_of_cost (inputs := allocatorInputs) (child .word (.cell .word) span span).hasType actual).mpr (Nat.le_refl 8)

private def rejected : Syntax.Expr := ⟨span, .call ⟨span, .conditional (ref span "c") span (ref span "f") span (ref span "missing")⟩ ⟨span, [ref span "x"]⟩⟩
theorem unselected_unknown_child_still_rejects_the_whole_body (fuel : Nat) (store : Core.Store) :
    LocalApplicationReturnBodyEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (wrap span span rejected) (w 23) [w 23] 11 ∧
    readerInputs.runApplicationReturnBody? fuel (wrap span span rejected) store = none := by
  have missing : readerInputs.checkApplicationReturnBody? (wrap span span rejected) = none := by
    simp [LocalInputs.checkApplicationReturnBody?, elaborateLocalApplicationReturnBody?, wrap, rejected, elaborateLocalFunctionApplication?,
      elaborateLocalExpression?, resolveLocalExpression?, readerInputs, bundle, LocalInputs.names, ref, LocalNameTable.lookup?]
  refine ⟨?_, (LocalInputs.runApplicationReturnBody?_eq_none_iff fuel store).mpr missing⟩
  have guard : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "c") (.bool true) [w 23] 1 :=
    .identifier (.tail (by decide) (.tail (by decide) (.tail (by decide) .head))) (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))
  have f : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "f") reader [w 23] 1 := .identifier (.tail (by decide) .head) (.tail (by decide) .head)
  have x : LocalExpressionEvaluatesWithCost readerInputs.names readerInputs.environment [w 23] (ref span "x") .unit [w 23] 1 := .identifier .head .head
  exact .application (.call (.ifTrue guard f) x (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))

theorem unsupported_return_shapes_keep_their_old_profiles (actual : LocalInputs) (a b : Syntax.SourceSpan) :
    (¬ ∃ type, LocalApplicationReturnBodyHasType actual.names actual.context ⟨a, []⟩ type) ∧
    actual.checkApplicationReturnBody? ⟨a, [⟨b, .returnStmt none⟩]⟩ = none ∧
    actual.checkApplicationReturnBody? (wrap a b ⟨a, .tuple ⟨b, []⟩⟩) = none ∧
    actual.checkApplicationReturnBody? ⟨a, [⟨b, .returnStmt (some (call a b))⟩, ⟨b, .returnStmt none⟩]⟩ = none ∧
    actual.checkReturnBody? ⟨a, [⟨b, .returnStmt none⟩]⟩ = some (.unit, .unit) :=
  ⟨elaborateLocalApplicationReturnBody?_eq_none_iff.mp rfl, rfl, rfl, rfl, rfl⟩

end Tests.FrontendApplicationReturnBody
end

section
-- leanmerge: from Solcore.Test.FrontendConditionalReturnBodyProperties
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
      TypedLetReturnBodyElaborates.returnTree <| .terminal <| .conditional (.identifier .head) (.var .head) (.var .head) (.single .bare) (.single .bare)⟩
  exact ⟨rfl, compilation.header, compilation.parameters, compilation.complete⟩

end Tests.FrontendConditionalReturnBody
end

section
-- leanmerge: from Solcore.Test.FrontendDiscardStatementProperties
/-! Original discard statements retain source scopes. Hidden Core binders
retain strict work without introducing source names or runtime parameters. -/
set_option autoImplicit false
namespace Tests.FrontendDiscardStatement
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Discard", by decide⟩], by decide⟩⟩, 0⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "discard.sol"⟩, 17, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def discard (expression : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .expression expression true⟩ :: tail.value⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Payload"⟩, []⟩⟩⟩ none⟩
private def types (type : Core.Ty) : TypeNameTable := [(["Payload"], type)]
private def mixed : Bool → List String → String → Syntax.Block
  | _, [], previous => returned previous
  | flag, name :: rest, previous => discard (ref previous)
      ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if flag then some annotation else none)
        (some (ref previous))⟩ :: (mixed (!flag) rest name).value⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .letE (.var 0) (.letE (.var 1) (core n))
private def seed (type : Core.Ty) := LocalTypeInputs.empty.bindFresh owner "seed" type
private theorem stable (n cutoff : Nat) (positive : 0 < cutoff) : (core n).weakenAt cutoff = core n := by
  induction n generalizing cutoff with
  | zero => simp [core, Core.Expr.weakenAt, Nat.not_le.mpr positive]
  | succ n ih =>
      simp only [core, Core.Expr.weakenAt]
      rw [if_neg (by omega), if_neg (by omega), ih (cutoff + 1 + 1) (by omega)]
private theorem eta (flag : Bool) (names : List String) (previous : String) :
    (⟨span, (mixed flag names previous).value⟩ : Syntax.Block) = mixed flag names previous := by cases names <;> rfl
private theorem elaborated (flag : Bool) (names : List String) (previous : String) (type : Core.Ty)
    (initial : LocalTypeInputs) (resolved : Resolved.Expr) (distinct : names.Nodup)
    (fresh : ∀ name ∈ names, name ∉ initial.names.map Prod.fst)
    (resolution : ResolvesLocalExpression initial.names (ref previous) resolved)
    (lowered : Resolved.Lowers initial.ids resolved (.var 0)) (typed : Resolved.HasType initial.context resolved type) :
    TypedLetReturnTreeElaborates (types type) owner initial (mixed flag names previous) (core names.length) type := by
  induction names generalizing flag previous initial resolved with
  | nil =>
      simp only [mixed, List.length_nil, core]
      exact .single (.expression resolution (by simpa only [LocalTypeInputs.context_ids] using lowered) typed)
  | cons name rest ih =>
      have parts := List.nodup_cons.mp distinct
      have tail := ih (!flag) name (initial.bindFresh owner name type) _ parts.2 (by
        intro next member
        simp only [LocalTypeInputs.bindFresh_names, List.map_cons, List.mem_cons, not_or]
        exact ⟨fun same => parts.1 (same ▸ member), fresh next (List.mem_cons_of_mem name member)⟩)
        (.identifier .head) (.var .head) (.var .head)
      have bound : TypedLetReturnTreeElaborates (types type) owner initial
          ⟨span, ⟨span, .letDecl ⟨span, name⟩ (if flag then some annotation else none) (some (ref previous))⟩ ::
            (mixed (!flag) rest name).value⟩ (.letE (.var 0) (core rest.length)) type := by
        cases flag
        · exact .inferred (fresh name (by simp)) resolution lowered typed (by simpa only [eta] using tail)
        · exact .binding (.named .head) (fresh name (by simp)) resolution lowered typed (by simpa only [eta] using tail)
      have full : TypedLetReturnTreeElaborates (types type) owner initial (mixed flag (name :: rest) previous)
          (.letE (.var 0) ((Core.Expr.letE (.var 0) (core rest.length)).weakenAt 0)) type :=
        .discard resolution lowered typed bound
      simpa [core, Core.Expr.weakenAt, stable] using full
private theorem seedElab (flag : Bool) (names : List String) (type : Core.Ty)
    (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (mixed flag names "seed") (core names.length) type := by
  apply elaborated flag names "seed" type (seed type) _ distinct
  · intro name member
    change name ∉ ["seed"]
    simpa only [List.mem_singleton] using (show name ≠ "seed" from fun same => fresh (same ▸ member))
  · exact .identifier .head
  · exact .var .head
  · exact .var .head
private theorem counted (flag : Bool) (names : List String) (previous : String)
    (table : LocalNameTable) (environment : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table environment store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost owner table environment store (mixed flag names previous) value store (6*names.length+1) := by
  induction names generalizing flag previous table environment with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
      let fresh := Resolved.freshLocalId owner (table.map Prod.snd)
      have tail := ih (!flag) name ((name, fresh) :: table) ((fresh, value) :: environment) (.identifier .head .head)
      have arithmetic : 1 + (1 + (6*rest.length+1) + 2) + 2 = 6*(name :: rest).length+1 := by simp; omega
      rw [← arithmetic]
      cases flag
      · exact .discard head (.inferred head (by simpa only [eta] using tail))
      · exact .discard head (.binding head (by simpa only [eta] using tail))
private theorem path (n : Nat) (value : Core.Value) (tail : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (6*n+1) ⟨.eval (core n) (value :: tail), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing tail k with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have steps := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet
        (.cons .enterLet (.cons (.var (index := 1) rfl) (.cons .bindLet (ih (value :: value :: tail) k))))))
      simpa [core, Nat.mul_add, Nat.add_assoc] using steps

theorem arbitrary_mixed_prefixes_keep_original_annotations_and_exact_core
    (flag : Bool) (names : List String) (type : Core.Ty) (distinct : names.Nodup) (fresh : "seed" ∉ names) :
    TypedLetReturnTreeElaborates (types type) owner (seed type) (mixed flag names "seed") (core names.length) type ∧
    TypedLetReturnTreeHasType (types type) owner (seed type) (mixed flag names "seed") type ∧
    elaborateTypedLetReturnTree? (types type) owner (seed type) (mixed flag names "seed") = some (core names.length, type) :=
  ⟨seedElab flag names type distinct fresh, (seedElab flag names type distinct fresh).hasType,
    (seedElab flag names type distinct fresh).complete⟩

theorem raw_duplicate_names_still_evaluate_every_discard
    (flag : Bool) (names : List String) (value : Core.Value) (store : Core.Store) (k : List Core.Frame) :
    TypedLetReturnTreeEvaluatesWithCost owner [("seed", id 0)] [(id 0, value)] store (mixed flag names "seed") value store (6*names.length+1) ∧
    evaluateTypedLetReturnTreeWithCost? owner [("seed", id 0)] [(id 0, value)] (mixed flag names "seed") = some (value, 6*names.length+1) ∧
    Core.Steps (6*names.length+1) ⟨.eval (core names.length) [value], k, store⟩ ⟨.ret value, k, store⟩ := by
  have evaluation := counted flag names "seed" [("seed", id 0)] [(id 0, value)] value store (.identifier .head .head)
  exact ⟨evaluation, evaluateTypedLetReturnTreeWithCost?_complete evaluation, path _ value [] store k⟩

theorem nominal_static_types_need_no_discardable_runtime_inhabitant (nominal : Core.DataTypeId) :
    elaborateTypedLetReturnTree? (types (.namedData nominal)) owner (seed (.namedData nominal))
      (mixed false ["x", "y"] "seed") = some (core 2, .namedData nominal) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨(seedElab false ["x", "y"] _ (by decide) (by decide)).complete, ?_⟩
  rintro ⟨value, typed⟩
  cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

theorem actual_cells_and_closures_are_discarded_without_inspection
    (location : Core.Location) (word : Core.Word) (store : Core.Store) (k : List Core.Frame) :
    Core.ValueHasType (.cellRef .word location) (.cell .word) ∧
    Core.ValueHasType (.closure .bool .word (.var 1) [.word word]) (.function .bool .word) ∧
    Core.Steps 7 ⟨.eval (core 1) [.cellRef .word location], k, store⟩ ⟨.ret (.cellRef .word location), k, store⟩ ∧
    Core.Steps 7 ⟨.eval (core 1) [.closure .bool .word (.var 1) [.word word]], k, store⟩
      ⟨.ret (.closure .bool .word (.var 1) [.word word]), k, store⟩ :=
  ⟨.cellRef, .closure (.cons .word .nil) (.var rfl), path 1 _ [] store k, path 1 _ [] store k⟩

private def sparse : LocalTypeInputs := ⟨[⟨"x", id 7, .word⟩, ⟨"y", ⟨other, 99⟩, .word⟩, ⟨"x", id 2, .word⟩], by decide⟩
private def actual (left right shadow : Core.Word) : LocalInputs :=
  ⟨[⟨"x", id 7, .word, .word left, .word⟩, ⟨"y", ⟨other, 99⟩, .word, .word right, .word⟩,
    ⟨"x", id 2, .word, .word shadow, .word⟩], by change [id 7, ⟨other, 99⟩, id 2].Nodup; decide⟩
private def subtraction : Syntax.Expr := ⟨span, .binary (ref "x") ⟨span, .subtract⟩ (ref "y")⟩
private def strict := discard subtraction (returned "x")
private def strictCore : Core.Expr := .letE (.binary .wordSub (.var 0) (.var 1)) (.var 1)
private theorem strictElab : TypedLetReturnTreeElaborates [] owner sparse strict strictCore .word := by
  simpa [strict, discard, strictCore, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.discard (types := []) (owner := owner) (blockSpan := span) (statementSpan := span)
    (inputs := sparse) (expression := subtraction) (rest := (returned "x").value) (tailCore := .var 0)
    (.subtract (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.binary (.var .head) (.var (.tail (by decide) .head))) (.binary (.var .head) (.var (.tail (by decide) .head)))
    (.single (.expression (.identifier .head) (.var .head) (.var .head))))
private theorem strictCost (left right shadow : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment store strict (.word left) store 8 :=
  .discard (expression := subtraction) (discardedValue := .word (left.sub right)) (expressionCost := 5) (tailCost := 1)
    (.subtract (leftValue := left) (rightValue := right) (leftCost := 1) (rightCost := 1)
      (.identifier .head .head) (.identifier (.tail (by decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
    (.single (.expression (.identifier .head .head)))
private theorem strictPath (left right shadow : Core.Word) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval strictCore [.word left, .word right, .word shadow], k, store⟩ ⟨.ret (.word left), k, store⟩ :=
  CostStepComposition.letE (CostStepComposition.binary (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl)
    (.cons (.var rfl) .refl)

theorem strict_noncommutative_work_keeps_first_matches_and_all_fuel
    (left right shadow : Core.Word) (store : Core.Store) (fuel : Nat) :
    ¬ (sparse.names.map Prod.fst).Nodup ∧
    elaborateTypedLetReturnTree? [] owner sparse strict = some (strictCore, .word) ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment store strict (.word left) store 8 ∧
    (Core.runStateful fuel (Core.State.initial strictCore [.word left, .word right, .word shadow] store) = .done (.word left) store ↔ 8 ≤ fuel) :=
  ⟨by decide, strictElab.complete, strictCost left right shadow store, (strictPath left right shadow store []).runStateful_done_iff⟩

theorem discarded_type_and_tail_keep_the_same_source_inputs :
    ∃ expressionType expressionCore tailCore,
      elaborateLocalExpression? sparse.names sparse.context subtraction = some (expressionCore, expressionType) ∧
      elaborateTypedLetReturnTree? [] owner sparse (returned "x") = some (tailCore, .word) ∧
      strictCore = .letE expressionCore (tailCore.weakenAt 0) :=
  elaborateTypedLetReturnTree?_discard_children strictElab.complete

theorem a_hidden_binder_is_not_a_source_binding_or_an_unweakened_tail :
    Resolved.freshLocalId owner sparse.ids = id 8 ∧
    ¬ TypedLetReturnTreeElaborates [] owner sparse strict (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0)) .word ∧
    Core.runStateful 8 (Core.State.initial (.letE (.binary .wordSub (.var 0) (.var 1)) (.var 0))
      [.word (Core.Word.ofNatModulo 5), .word (Core.Word.ofNatModulo 2)]) = .done (.word (Core.Word.ofNatModulo 3)) [] := by
  refine ⟨rfl, ?_, rfl⟩
  intro wrong
  cases (wrong.result_unique strictElab).1

private def checkpoint (left right shadow : Core.Word) (store : Core.Store) : Core.State :=
  ⟨.ret (.word (left.sub right)), [.letBody (.var 1) [.word left, .word right, .word shadow]], store⟩
theorem genuine_discard_checkpoints_resume_the_original_tail
    (left right shadow : Core.Word) (store : Core.Store) (additional : Nat) :
    (actual left right shadow).runTypedLetReturnTree? [] owner 6 strict store = some (.word, .outOfFuel (checkpoint left right shadow store)) ∧
    Core.Steps 2 (checkpoint left right shadow store) (Core.State.final (.word left) store) ∧
    (actual left right shadow).runTypedLetReturnTree? [] owner (6 + additional) strict store =
      some (.word, Core.runStateful additional (checkpoint left right shadow store)) ∧
    Core.runStateful 0 ⟨(checkpoint left right shadow store).control, [], store⟩ = .done (.word (left.sub right)) store := by
  have exhausted : (actual left right shadow).runTypedLetReturnTree? [] owner 6 strict store =
      some (.word, .outOfFuel (checkpoint left right shadow store)) :=
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨strictCore, strictElab.complete, rfl⟩
  exact ⟨exhausted, .cons .bindLet (.cons (.var rfl) .refl), LocalInputs.runTypedLetReturnTree?_resume exhausted additional, rfl⟩

theorem product_results_need_not_be_unit_to_be_discarded (left right shadow : Core.Word) (store : Core.Store) :
    TypedLetReturnTreeElaborates [] owner sparse
      (discard ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩ (returned "x")) (.letE (.pair (.var 0) (.var 1)) (.var 1)) .word ∧
    TypedLetReturnTreeEvaluates owner sparse.names (actual left right shadow).environment store
      (discard ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩ (returned "x")) (.word left) store := by
  refine ⟨?_, .discard (.pair (.identifier .head .head)
    (.identifier (.tail (by decide) .head) (.tail (by change id 7 ≠ ⟨other, 99⟩; decide) .head)))
    (.single (.expression (.identifier .head .head)))⟩
  simpa [discard, Core.Expr.weakenAt] using
    (TypedLetReturnTreeElaborates.discard (types := []) (owner := owner) (blockSpan := span) (statementSpan := span)
    (inputs := sparse) (tailCore := .var 0) (discardedType := .product .word .word)
    (expression := ⟨span, .tuple ⟨span, [ref "x", ref "y"]⟩⟩) (rest := (returned "x").value)
    (.pair (.identifier .head) (.identifier (.tail (by decide) .head)))
    (.pair (.var .head) (.var (.tail (by decide) .head))) (.pair (.var .head) (.var (.tail (by decide) .head)))
    (.single (.expression (.identifier .head) (.var .head) (.var .head))))

theorem owner_store_and_raw_lookup_transport_have_distinct_premises
    (mapping : Resolved.DeclarationId → Resolved.DeclarationId) (injective : Function.Injective mapping)
    (left right shadow : Core.Word) (store replacement : Core.Store) (fuel : Nat)
    (rightOwner : Resolved.DeclarationId) (table : LocalNameTable) (environment : Resolved.Environment)
    (agreement : ∀ name, (sparse.names.lookup? name).bind (actual left right shadow).environment.lookup? = (table.lookup? name).bind environment.lookup?) :
    ((actual left right shadow).mapIds (ownerLocalIdMap mapping) (ownerLocalIdMap_injective mapping injective)).runTypedLetReturnTree?
      [] (mapping owner) fuel strict store = (actual left right shadow).runTypedLetReturnTree? [] owner fuel strict store ∧
    TypedLetReturnTreeEvaluatesWithCost owner sparse.names (actual left right shadow).environment replacement strict (.word left) replacement 8 ∧
    evaluateTypedLetReturnTreeWithCost? rightOwner table environment strict = some (.word left, 8) := by
  refine ⟨LocalInputs.runTypedLetReturnTree?_mapOwner _ mapping injective [] owner fuel strict store,
    (strictCost left right shadow store).change_store replacement, ?_⟩
  rw [← evaluateTypedLetReturnTreeWithCost?_congr_lookup owner rightOwner sparse.names table _ environment agreement strict]
  exact evaluateTypedLetReturnTreeWithCost?_complete (strictCost left right shadow store)

theorem missing_expression_or_required_shape_is_not_silently_discarded
    (value : Core.Value) (store finalStore : Core.Store) :
    elaborateTypedLetReturnTree? [] owner sparse (discard (ref "missing") (returned "x")) = none ∧
    ¬ TypedLetReturnTreeEvaluates owner sparse.names [] store (discard (ref "missing") (returned "x")) value finalStore ∧
    elaborateTypedLetReturnTree? [] owner sparse ⟨span, ⟨span, .expression subtraction false⟩ :: (returned "x").value⟩ = none ∧
    elaborateTypedLetReturnTree? [] owner sparse ⟨span, [⟨span, .expression subtraction true⟩]⟩ = none ∧
    elaborateTypedLetReturnBody? [] owner sparse strict = none := by
  have missingLookup : sparse.names.lookup? "missing" = none := rfl
  have missing : elaborateLocalExpression? sparse.names sparse.context (ref "missing") = none := by
    simp [elaborateLocalExpression?, resolveLocalExpression?, ref, missingLookup]
  have noTail : elaborateTypedLetReturnTree? [] owner sparse ⟨span, [⟨span, .expression subtraction true⟩]⟩ = none := by
    apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | discard _ tail => cases tail with
      | single child => cases child
  refine ⟨by simp [discard, elaborateTypedLetReturnTree?, missing], ?_, by simp only [elaborateTypedLetReturnTree?],
    noTail,
    by simp [strict, discard, elaborateTypedLetReturnBody?, elaborateTerminalReturnTree?]⟩
  intro evaluation
  cases evaluation with
  | single child => cases child
  | discard expression _ =>
      cases expression with
      | identifier named _ =>
          have impossible := LocalNameTable.lookup?_iff.mpr named
          change none = some _ at impossible
          cases impossible

private def one := discard (ref "seed") (returned "seed")
private def branch (otherwise : Syntax.Block) : Syntax.Block :=
  ⟨span, [⟨span, .ifThen (ref "seed") one (some otherwise)⟩]⟩
theorem branch_costs_are_selected_but_whole_checking_keeps_both_arms (choice : Bool) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost owner (seed .bool).names [(id 0, .bool choice)] store
      (branch (returned "seed")) (.bool choice) store (if choice then 7 else 4) ∧
    elaborateTypedLetReturnTree? [] owner (seed .bool) (branch (returned "seed")) =
      some (.ifE (.var 0) (.letE (.var 0) (.var 1)) (.var 0), .bool) ∧
    TypedLetReturnTreeEvaluates owner (seed .bool).names [(id 0, .bool true)] store
      (branch (discard (ref "missing") (returned "seed"))) (.bool true) store ∧
    elaborateTypedLetReturnTree? [] owner (seed .bool) (branch (discard (ref "missing") (returned "seed"))) = none := by
  have leaf : ReturnBodyElaborates (seed .bool).names (seed .bool).context (returned "seed") (.var 0) .bool :=
    .expression (.identifier .head) (.var .head) (.var .head)
  have first : TypedLetReturnTreeElaborates [] owner (seed .bool) one (.letE (.var 0) ((Core.Expr.var 0).weakenAt 0)) .bool :=
    .discard (inputs := seed .bool) (expression := ref "seed") (rest := (returned "seed").value) (tailCore := .var 0)
      (.identifier .head) (.var .head) (.var .head) (.single leaf)
  have original : TypedLetReturnTreeElaborates [] owner (seed .bool) (branch (returned "seed"))
      (.ifE (.var 0) (.letE (.var 0) ((Core.Expr.var 0).weakenAt 0)) (.var 0)) .bool :=
    .conditional (.identifier .head) (.var .head) (.var .head) first (.single leaf)
  refine ⟨?_, by simpa [Core.Expr.weakenAt] using original.complete,
    .ifTrue (.identifier .head .head) (.discard (.identifier .head .head) (.single (.expression (.identifier .head .head)))), ?_⟩
  · cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact .ifFalse (condition := ref "seed") (thenBody := one) (conditionCost := 1) (branchCost := 1)
        (.identifier .head .head) (.single (.expression (.identifier .head .head)))
    · exact .ifTrue (condition := ref "seed") (elseBody := returned "seed") (conditionCost := 1) (branchCost := 4)
        (.identifier .head .head) (.discard (expression := ref "seed") (expressionCost := 1) (tailCost := 1)
          (.identifier .head .head) (.single (.expression (.identifier .head .head))))
  · apply elaborateTypedLetReturnTree?_eq_none_iff.mpr
    rintro ⟨_, typing⟩
    cases typing with
    | single child => cases child
    | conditional _ _ other =>
        cases other with
        | single child => cases child
        | discard expression _ =>
            cases expression with
            | identifier named _ =>
                have impossible := LocalNameTable.lookup?_iff.mpr named
                change none = some _ at impossible
                cases impossible

end Tests.FrontendDiscardStatement
end

section
-- leanmerge: from Solcore.Test.FrontendParsedApplicationInsertion
/-! Parsed source provenance is independent of the static and runtime insertion
contexts. Nominal checking supplies no actual values; the small runtime grid
uses explicit identity closures and manually counted child transitions. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationInsertion
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Insertion", by decide⟩], by decide⟩⟩, 49⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def foreign : Resolved.LocalId := ⟨{ owner with declarationIndex := 77 }, 301⟩
private def names : LocalNameTable := [("f", id 7), ("c", foreign), ("x", id 2), ("g", id 19), ("y", id 3), ("f", id 80)]
private def context (input output : Core.Ty) : Resolved.Context :=
  [(id 90, .unit), (id 7, .function input output), (foreign, .bool), (id 2, input),
    (id 19, .function input output), (id 3, input), (id 7, .bool)]
private def fnCore (conditional : Bool) : Core.Expr :=
  if conditional then .ifE (.var 2) (.var 1) (.var 4) else .var 1
private def argCore (conditional : Bool) : Core.Expr :=
  if conditional then .ifE (.var 2) (.var 3) (.var 5) else .var 3
private def target (fc ac : Bool) := Core.Expr.apply (fnCore fc) (argCore ac)
private def childCost (conditional : Bool) : Nat := if conditional then 4 else 1
private def cost (fc ac : Bool) := childCost fc + childCost ac + 1 + 3
private def parsed (text : String) : IO Syntax.Expr := do
  let file : Syntax.SourceFile := ⟨⟨.main, "application-insertion.sol"⟩, text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.expression (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError s!"expression did not parse: {text}")
  check (tokens.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, text.utf8ByteSize⟩)) "original expression span or diagnostics changed"
  return source
private structure Child (ctx : Resolved.Context) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression names source resolved
  lowered : Resolved.Lowers ctx.ids resolved core
  typing : Resolved.HasType ctx resolved type
private def child (ctx : Resolved.Context) (source : Syntax.Expr) : IO (Child ctx source) := do
  match original : source with
  | ⟨_, .identifier name⟩ =>
      match named : names.lookup? name.value with
      | some localId =>
          match found : ctx.lookup? localId, indexed : Resolved.LocalScope.index? ctx.ids localId with
          | some type, some index => return ⟨.var localId, .var index, type,
              by rw [original]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp found)⟩
          | _, _ => throw (IO.userError "original context row absent")
      | none => throw (IO.userError "original name absent")
  | ⟨_, .group inner⟩ =>
      let a ← child ctx inner
      return ⟨a.resolved, a.core, a.type, by rw [original]; exact .group a.resolution, a.lowered, a.typing⟩
  | ⟨_, .conditional condition _ yes _ no⟩ =>
      let c ← child ctx condition; let a ← child ctx yes; let b ← child ctx no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,
          .ifE c.core a.core b.core, a.type, by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered, .ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole arm types differ")
      else throw (IO.userError "guard not Bool")
  | _ => throw (IO.userError "outside independent child fixture")
termination_by sizeOf source
private structure Certified (input output : Core.Ty) (fc ac : Bool) where
  source : Syntax.Expr
  evidence : LocalFunctionApplicationElaborates names (context input output) source (target fc ac) output
private theorem manualTyping (input output : Core.Ty) (fc ac : Bool) (definitions : Core.DataEnvironment) :
    Core.HasType (context input output).values (target fc ac) output definitions := by
  cases fc <;> cases ac <;>
    exact .apply (by first | exact .var rfl | exact .ifE (.var rfl) (.var rfl) (.var rfl))
      (by first | exact .var rfl | exact .ifE (.var rfl) (.var rfl) (.var rfl))
private def staticCheck (input output : Core.Ty) (fc ac : Bool) (text : String) : IO (Certified input output fc ac) := do
  let source ← parsed text; let ctx := context input output
  match original : source with
  | ⟨_, .call callee ⟨argsSpan, [argument]⟩⟩ =>
      check (source.span.contains callee.span && source.span.contains argsSpan && argsSpan.contains argument.span &&
        decide (callee.span.endByte ≤ argsSpan.startByte ∧ argsSpan.startByte < argument.span.startByte ∧
          argument.span.endByte < argsSpan.endByte)) "original delimiter/order changed"
      let f ← child ctx callee; let a ← child ctx argument
      if expected : f.type = .function input output ∧ a.type = input ∧
          f.core = fnCore fc ∧ a.core = argCore ac then
        have evidence : LocalFunctionApplicationElaborates names ctx source (target fc ac) output := by
          rw [original]
          simpa only [target, expected.2.2.1, expected.2.2.2] using
            LocalFunctionApplicationElaborates.call f.resolution f.lowered (expected.1 ▸ f.typing)
              a.resolution a.lowered (expected.2.1 ▸ a.typing)
        check (decide (elaborateLocalFunctionApplication? names ctx source = some (target fc ac, output) ∧
          elaborateLocalExpression? names ctx source = none ∧ names.lookup? "f" = some (id 7) ∧
          ctx.lookup? (id 7) = some (.function input output))) "exact original static provenance/first match changed"
        for cutoff in List.range 8 do
          let leading := ctx.values.take cutoff; let suffix := ctx.values.drop cutoff
          for inserted in [Core.Ty.unit, .word, .namedData ⟨999⟩, .function (.namedData ⟨2⟩) (.namedData ⟨3⟩)] do
            have typing (definitions) : Core.HasType (leading ++ suffix) (target fc ac) output definitions := by
              simpa only [leading, suffix, List.take_append_drop] using manualTyping input output fc ac definitions
            have lifted (definitions) := (evidence.core_hasType_insert_iff leading suffix inserted).mpr (typing definitions)
            have _ (definitions) := (evidence.core_hasType_insert_iff leading suffix inserted).mp (lifted definitions)
            have _ (requestedType definitions) := evidence.core_hasType_insert_iff leading suffix inserted
              (requestedType := requestedType) (definitions := definitions)
            check (decide (Core.infer? (leading ++ inserted :: suffix) ((target fc ac).weakenAt leading.length) = some output))
              "type insertion changed the independent assigned result"
        return ⟨source, evidence⟩
      else throw (IO.userError "independent expected child Core/type differs")
  | _ => throw (IO.userError "original root is not one-argument call")
private def identity (type : Core.Ty) : Core.Value := .closure type type (.var 0) [.bool true]
private def values (type : Core.Ty) (x y : Core.Value) (choice : Bool) : Core.Environment :=
  [.unit, identity type, .bool choice, x, identity type, y, .bool false]
private def result (x y : Core.Value) (choice ac : Bool) := if ac && !choice then y else x
private theorem manualEvaluation (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool) (store : Core.Store) :
    Core.Evaluates (values type x y choice) store (target fc ac) (result x y choice ac) store := by
  have fn : Core.Evaluates (values type x y choice) store (fnCore fc) (identity type) store := by
    cases fc <;> cases choice <;> first | exact .var rfl | exact .ifTrue (.var rfl) (.var rfl) | exact .ifFalse (.var rfl) (.var rfl)
  have arg : Core.Evaluates (values type x y choice) store (argCore ac) (result x y choice ac) store := by
    cases ac <;> cases choice <;> first | exact .var rfl | exact .ifTrue (.var rfl) (.var rfl) | exact .ifFalse (.var rfl) (.var rfl)
  exact .apply fn arg (.var rfl)
private theorem manualPath (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (cost fc ac) ⟨.eval (target fc ac) (values type x y choice), k, store⟩
      ⟨.ret (result x y choice ac), k, store⟩ := by
  have fn (frames) : Core.Steps (childCost fc) ⟨.eval (fnCore fc) (values type x y choice), frames, store⟩
      ⟨.ret (identity type), frames, store⟩ := by
    cases fc <;> cases choice <;>
      first | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
  have arg (frames) : Core.Steps (childCost ac) ⟨.eval (argCore ac) (values type x y choice), frames, store⟩
      ⟨.ret (result x y choice ac), frames, store⟩ := by
    cases ac <;> cases choice <;>
      first | exact .cons (.var rfl) .refl
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons (.var rfl) .refl)))
            | exact .cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons (.var rfl) .refl)))
  exact CostStepComposition.apply (fn _) (arg _) (.cons (.var rfl) .refl)
private def actualSmoke (type : Core.Ty) (x y : Core.Value) (choice fc ac : Bool) (text : String) : IO Unit := do
  let original ← staticCheck type type fc ac text
  let env := values type x y choice; let expected := result x y choice ac
  for store in [[], [.word (Core.Word.ofNatModulo 71), .bool true]] do
    for cutoff in List.range 8 do
      let leading := env.take cutoff; let suffix := env.drop cutoff
      have same : leading ++ suffix = env := List.take_append_drop cutoff env
      have raw : Core.Evaluates (leading ++ suffix) store (target fc ac) expected store := by
        simpa only [same] using manualEvaluation type x y choice fc ac store
      have path : Core.Steps (cost fc ac) (.initial (target fc ac) (leading ++ suffix) store) (.final expected store) := by
        simpa only [same, Core.State.initial, Core.State.final, env, expected] using manualPath type x y choice fc ac store []
      for inserted in [Core.Value.bool true, .cellRef .word 93, .closure .word .bool (.var 19) [.cellRef .bool 31], .unit] do
        have lifted := (original.evidence.core_evaluates_insert_iff leading suffix inserted).mpr raw
        have _ := (original.evidence.core_evaluates_insert_iff leading suffix inserted).mp lifted
        have paired : ∃ n, n = cost fc ac ∧ ∀ k,
            Core.Steps n ⟨.eval (target fc ac) (leading ++ suffix), k, store⟩ ⟨.ret expected, k, store⟩ ∧
            Core.Steps n ⟨.eval ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩
              ⟨.ret expected, k, store⟩ := by
          obtain ⟨n, paths⟩ := original.evidence.core_insertion_paths leading suffix inserted raw
          exact ⟨n, (path.final_unique (paths []).1).1.symm, paths⟩
        have _ := paired
        have insertedPath := original.evidence.core_steps_insert leading suffix inserted path []
        have _ := original.evidence.core_steps_reflect_insert leading suffix inserted insertedPath []
        have _ := (original.evidence.core_steps_insert_iff leading suffix inserted).mpr path
        have _ := (original.evidence.core_steps_insert_iff leading suffix inserted).mp insertedPath
        let pending : List Core.Frame := [.letBody .unit []]
        have _ := original.evidence.core_steps_insert leading suffix inserted path pending
        have _ := original.evidence.core_steps_reflect_insert leading suffix inserted insertedPath pending
        check (decide (leading ++ suffix = env ∧
          Core.runStateful (cost fc ac) (.initial ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix) store) =
            .done expected store)) "actual insertion changed literal value/store/cost"
        check (decide (Core.runStateful (cost fc ac)
          ⟨.eval ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix), pending, store⟩ =
            .outOfFuel ⟨.ret expected, pending, store⟩)) "retained continuation endpoint was mistaken for closed completion"
        for fuel in List.range (cost fc ac + 2) do
          have _ := insertedPath.runStateful_done_iff (fuel := fuel)
          match Core.runStateful fuel (.initial ((target fc ac).weakenAt leading.length) (leading ++ inserted :: suffix) store) with
          | .done value finalStore => check (decide (cost fc ac ≤ fuel ∧ value = expected ∧ finalStore = store)) "wrong inserted completion"
          | .outOfFuel _ => check (decide (fuel < cost fc ac)) "wrong inserted exhaustion threshold"
          | .fault _ _ => throw (IO.userError "unused inserted value was executed")
end ParsedApplicationInsertion
open ParsedApplicationInsertion
def frontendParsedApplicationInsertionTests : IO Unit := do
  let fixtures := [(false, false, "f(x)"), (false, false, "((f))(((x)))"),
    (true, false, "(c ? f : g)(x)"), (false, true, "f(c ? x : y)"),
    (true, true, "(c ? (f) : g)(c ? x : (y))"), (false, false, "f /* call */ ( /* arg */ x )")]
  for input in [Core.Ty.unit, .word, .namedData ⟨7⟩, .function (.namedData ⟨2⟩) (.namedData ⟨3⟩)] do
    for output in [Core.Ty.unit, .bool, .namedData ⟨8⟩, .cell .word] do
      for (fc, ac, text) in fixtures do
        let _ ← staticCheck input output fc ac text
  for choice in [false, true] do
    for (fc, ac, text) in fixtures do
      actualSmoke .unit .unit .unit choice fc ac text
      actualSmoke .word (.word (Core.Word.ofNatModulo 9)) (.word (Core.Word.ofNatModulo 14)) choice fc ac text
  for text in ["(lam(z: Word){return z;})(x)", "f(f(x))", "(f(x))"] do
    let source ← parsed text
    check (decide (elaborateLocalFunctionApplication? names (context .word .word) source = none ∧
      elaborateLocalExpression? names (context .word .word) source = none)) "outside child/root profile acquired insertion provenance"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedApplicationInsertionEntries
/-! Original whole-entry records are retained; only the Core caller gains a slot.
Independent actual paths fix costs and effects before insertion is used. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationInsertionEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
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
private structure Original (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : body = ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩)⟩]⟩
private def original (body : Syntax.Block) : IO (Original body) := do
  match shape : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨s, .call f ⟨args, [x]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains s && s.contains f.span && s.contains args && args.contains x.span &&
        decide (f.span.endByte ≤ args.startByte)) "original return/call spans changed"
      return ⟨bs, rs, s, args, f, x, shape⟩
  | _ => throw (IO.userError "not original singleton return-call")
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
      have path := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: rest) k)))
      have count : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [count]; exact path
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
private def observe (start : Core.State) (value : Core.Value) (final : Core.Store) (cost : Nat)
    (path : Core.Steps cost start (.final value final)) : IO Unit := do
  for fuel in List.range (cost+3) do
    have _ := path.runStateful_done_iff (fuel := fuel)
    match exhausted : Core.runStateful fuel start with
    | .done actual store => check (decide (cost ≤ fuel ∧ actual = value ∧ store = final)) "exact completed result"
    | .outOfFuel cp =>
        have _ := path.residual_of_outOfFuel exhausted
        check (decide (fuel < cost ∧ Core.runStateful (cost-fuel) cp = .done value final)) "each side's genuine residual"
        for additional in [0,1,cost-fuel,cost+2] do
          have _ := Core.runStateful_resume exhausted additional
          have _ := path.resumed_done_iff (additional := additional) exhausted
          check (decide (Core.runStateful additional cp = Core.runStateful (fuel+additional) start)) "full-result own-state resumption"
        if 1 < cost-fuel then
          match next : Core.runStateful 1 cp with
          | .outOfFuel nextCp =>
              have _ := Core.runStateful_resume next (cost-fuel-1)
              check (decide (Core.runStateful (cost-fuel-1) nextCp = .done value final)) "three real chunks"
          | _ => throw (IO.userError "intermediate checkpoint missing")
    | .fault _ _ => throw (IO.userError "manual successful path faulted")
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (closureTyped : Core.ValueHasType (.closure argument.type output body captured) (.function argument.type output))
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured),k,s⟩ ⟨.ret value,k,t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output,.closure argument.type output body captured,closureTyped⟩
  let args := [f,argument]; let types := [(["F"],f.type),(["A"],argument.type),(["R"],output)]
  let source ← parsed text; let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual; let h ← header types source output; let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span,.call o.callee ⟨o.argumentsSpan,[o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if children : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (children.1 ▸ fn.typing) arg.resolution arg.lowered (children.2.1 ▸ arg.typing)
      simpa only [target,expression,children.2.2.1,children.2.2.2] using e
    have whole : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    let prepared : PreparedRuntimeFunction := ⟨inputs,target,output⟩
    have preparation : RuntimeApplicationFunctionPrepares types owner source args prepared := ⟨h.down,ps.bound,whole⟩
    have erased := preparation.compiles.parameters.result_unique ps.declared
    have _ := preparation.compiles.complete
    have _ := preparation.complete
    check (decide (inputs.bindings.map (fun b => (b.name,b.id,b.type,b.value)) =
      [("x",⟨owner,1⟩,argument.type,argument.value),("f",⟨owner,0⟩,f.type,f.value)])) "unchanged parameter-only actual record"
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have raw : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost+5) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    let caller := [argument.value,f.value]; let context := [argument.type,f.type]
    have manual (k) : Core.Steps (bodyCost+5) ⟨.eval target caller,k,s⟩ ⟨.ret value,k,t⟩ :=
      .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have rows : inputs.environment.values = caller := by
      simpa [caller,args,LocalInputs.environment,Resolved.LocalScope.values,List.map_map,Function.comp_def] using
        RuntimeParametersBind.argument_values ps.bound
    have _ := raw.deterministic ((child.evaluatesWithCost_iff_steps inputs.sameIds).mpr (by rw [rows]; exact manual []))
    have typed : Core.HasType context target output := .apply (.var rfl) (.var rfl)
    let cost := bodyCost+5
    for fuel in List.range (cost+3) do
      have _ := preparation.run_eq_body fuel s
      check (decide (runRuntimeApplicationFunction? types owner source args fuel s =
        some (output,Core.runStateful fuel (.initial target caller s)))) "original entry execution was rebuilt"
    let opaqueValue : Core.Value := .closure .unit .word (.var 1) [.word (Core.Word.ofNatModulo 99)]
    for (leading,suffix,leftTypes,rightTypes,expected,argumentIndex) in [
        ([],caller,[],context,Core.Expr.apply (.var 2) (.var 1),1),
        ([argument.value],[f.value],[argument.type],[f.type],Core.Expr.apply (.var 2) (.var 0),0),
        (caller,[],context,[],target,0)] do
      if sameCaller : leading ++ suffix = caller then
        if sameContext : leftTypes ++ rightTypes = context then
          check (decide (target.weakenAt leading.length = expected ∧ leading.length = leftTypes.length)) "independent shifted Core or cutoff"
          have originalPath : Core.Steps cost (.initial target (leading++suffix) s) (.final value t) := by
            simpa only [sameCaller,cost,Core.State.initial,Core.State.final] using manual []
          have originalEval := Core.steps_from_initial_sound originalPath
          for insertedType in [Core.Ty.namedData ⟨999⟩,.function (.namedData ⟨7⟩) (.namedData ⟨8⟩)] do
            have oldTyping : Core.HasType (leftTypes++rightTypes) target output := by rw [sameContext]; exact typed
            have newTyping := (child.core_hasType_insert_iff leftTypes rightTypes insertedType).mpr oldTyping
            have _ := (child.core_hasType_insert_iff leftTypes rightTypes insertedType).mp newTyping
          for inserted in [w 91,Core.Value.cellRef .word 999,opaqueValue] do
            have changedEval := (child.core_evaluates_insert_iff leading suffix inserted).mpr originalEval
            have _ := (child.core_evaluates_insert_iff leading suffix inserted).mp changedEval
            have _ := child.core_insertion_paths leading suffix inserted originalEval
            have changedPath := child.core_steps_insert leading suffix inserted originalPath []
            have _ := child.core_steps_reflect_insert leading suffix inserted changedPath [.letBody .unit []]
            have _ := (child.core_steps_insert_iff leading suffix inserted).mp changedPath
            have _ := (child.core_steps_insert_iff leading suffix inserted).mpr originalPath
            let oldStart := Core.State.initial target (leading++suffix) s
            let newCaller := leading ++ inserted :: suffix
            let newStart := Core.State.initial (target.weakenAt leading.length) newCaller s
            observe oldStart value t cost originalPath
            observe newStart value t cost changedPath
            let oldCp : Core.State := ⟨.eval (.var 0) caller,[.applyClosure argument.type output body captured],s⟩
            let newCp : Core.State := ⟨.eval (.var argumentIndex) newCaller,[.applyClosure argument.type output body captured],s⟩
            check (decide (Core.runStateful 3 oldStart = .outOfFuel oldCp ∧ Core.runStateful 3 newStart = .outOfFuel newCp ∧
              oldCp ≠ newCp)) "distinct saved caller checkpoints were identified"
            let entered : Core.State := ⟨.eval body (argument.value::captured),[],s⟩
            check (decide (Core.runStateful 5 oldStart = .outOfFuel entered ∧ Core.runStateful 5 newStart = .outOfFuel entered))
              "same actual body/captures did not rejoin"
        else throw (IO.userError "typing context was silently changed")
      else throw (IO.userError "caller decomposition was silently changed")
  else throw (IO.userError "independent original call changed")
end ParsedApplicationInsertionEntries
open ParsedApplicationInsertionEntries
def frontendParsedApplicationInsertionEntryTests : IO Unit := do
  for n in [0,2,5] do
    execute ⟨.word,w 14,.word⟩ .word (delayed n) [] [] [] (w 14) (3*n+1)
      (.closure .nil (delayedTyped n .word [])) (delayedPath n (w 14) [] [])
  for current in [3,17] do
    execute ⟨.word,w 14,.word⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [w current] [w current] (w current) 3
      (.closure (.cons .cellRef .nil) (.loadCell (.var rfl)))
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word,w 14,.word⟩ (.cell .word) (.newCell .word (.var 0)) [] [w current] [w current,w 14] (.cellRef .word 1) 3
      (.closure .nil (.newCell (.var rfl))) (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word,w 14,.word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [w current] [w 14] (w 14) 10
      (.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl))))
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩,.product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type,.closure type type (.var 0) [],.closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] a.value 1 (.closure .nil (.var rfl)) (fun _ => .cons (.var rfl) .refl)
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedApplicationReturnBodies
/-! Original complete blocks and independent child/body witnesses retain the
same Core, actual stores, costs and saved states as their return-call child. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedApplicationReturnBodies
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ApplicationRunner",by decide⟩],by decide⟩⟩,19⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def foreign : Resolved.LocalId := ⟨{owner with declarationIndex := 3},999⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def inputs (output : Core.Ty) (f shadow : Core.Value)
    (ft : Core.ValueHasType f (.function .word output)) (gt : Core.ValueHasType shadow (.function .word output)) (x : Nat) : LocalInputs :=
  ⟨[⟨"x",id 2,.word,w x,.word⟩,⟨"f",id 7,.function .word output,f,ft⟩,
    ⟨"g",id 91,.function .word output,shadow,gt⟩,⟨"c",foreign,.bool,.bool true,.bool⟩],by
      change [id 2,id 7,id 91,foreign].Nodup; decide⟩
private def parsed (text : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main,"application-runner.sol"⟩,text⟩
  let .ok tokens := Syntax.Lexer.lex file | throw (IO.userError "lexing failed")
  let .ok source next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file tokens)
    | throw (IO.userError "original block did not parse")
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
  | ⟨_,.conditional condition _ yes _ no⟩ =>
      let c ← child s condition; let a ← child s yes; let b ← child s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then return ⟨.ifE c.resolved a.resolved b.resolved,.ifE c.core a.core b.core,a.type,
          by rw [original]; exact .conditional c.resolution a.resolution b.resolution,
          .ifE c.lowered a.lowered b.lowered,.ifE (ct ▸ c.typing) a.typing (bt ▸ b.typing)⟩
        else throw (IO.userError "whole branch types differ")
      else throw (IO.userError "guard is not Bool")
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
private structure Returned (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  source : Syntax.Expr
  shape : body = ⟨blockSpan,[⟨returnSpan,.returnStmt (some source)⟩]⟩
private def returned (body : Syntax.Block) : IO (Returned body) := do
  match original : body with
  | ⟨b,[⟨r,.returnStmt (some source)⟩]⟩ =>
      check (b.contains r && r.contains source.span && decide (b.startByte < r.startByte ∧ source.span.endByte < r.endByte))
        "original body/return/child spans changed"
      return ⟨b,r,source,original⟩
  | _ => throw (IO.userError "not original singleton expression return")
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def verify (s : LocalInputs) (text : String) (core : Core.Expr) (type : Core.Ty) (value : Core.Value)
    (cost : Nat) (store final : Core.Store) : IO Unit := do
  let body ← parsed text; let r ← returned body
  let original ← application s r.source; let actual ← counted s store r.source
  if staticEq : original.core = core ∧ original.type = type then
    if actualEq : actual.value = value ∧ actual.final = final ∧ actual.cost = cost then
      have child : LocalFunctionApplicationElaborates s.names s.context r.source core type := by simpa only [staticEq.1,staticEq.2] using original.evidence
      have e : LocalFunctionApplicationEvaluatesWithCost s.names s.environment store r.source value final cost := by
        simpa only [actualEq.1,actualEq.2.1,actualEq.2.2] using actual.evidence
      have elaboration : LocalApplicationReturnBodyElaborates s.names s.context body core type := by rw [r.shape]; exact .application child
      have typing : LocalApplicationReturnBodyHasType s.names s.context body type := by rw [r.shape]; exact .application child.hasType
      have rawBody : LocalApplicationReturnBodyEvaluates s.names s.environment store body value final := by rw [r.shape]; exact .application e.erase
      have costed : LocalApplicationReturnBodyEvaluatesWithCost s.names s.environment store body value final cost := by rw [r.shape]; exact .application e
      have checkEq : s.checkApplicationReturnBody? body = s.checkApplication? r.source := by
        exact (congrArg s.checkApplicationReturnBody? r.shape).trans (s.checkApplicationReturnBody?_return _ _ _)
      have runEq (fuel) : s.runApplicationReturnBody? fuel body store = s.runApplication? fuel r.source store := by
        exact (congrArg (fun b => s.runApplicationReturnBody? fuel b store) r.shape).trans (s.runApplicationReturnBody?_return _ _ _ _ _)
      have checked := LocalInputs.checkApplicationReturnBody?_iff_elaborates.mpr elaboration
      have _ := elaborateLocalApplicationReturnBody?_sound elaboration.complete
      have _ := elaborateLocalApplicationReturnBody?_iff.mp elaboration.complete
      have _ := elaboration.hasType
      have _ := localApplicationReturnBodyHasType_iff_elaborates.mpr ⟨core,elaboration⟩
      have _ := elaboration.result_unique (elaborateLocalApplicationReturnBody?_sound elaboration.complete)
      have _ := typing.type_unique elaboration.hasType
      have _ := elaborateLocalApplicationReturnBody?_core_hasType elaboration.complete
      have _ := elaboration.core_hasType
      have _ := typing.elaborates_exact
      have _ := rawBody.deterministic costed.erase
      have _ := rawBody.exists_cost
      have _ := localApplicationReturnBodyEvaluates_iff_exists_cost.mpr ⟨cost,costed⟩
      have _ := (elaboration.evaluates_iff s.sameIds).mpr ((elaboration.evaluates_iff s.sameIds).mp rawBody)
      let path := costed.toStepsWithContinuation elaboration s.sameIds []
      have _ := costed.deterministic ((elaboration.evaluatesWithCost_iff_steps s.sameIds).mpr path)
      have _ := costed.toStepsWithContinuation elaboration s.sameIds [.loadCellApply]
      have done := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost (fuel := cost)).mpr ⟨typing,cost,costed,Nat.le_refl cost⟩
      have _ := LocalInputs.runApplicationReturnBody?_done_iff_typed_cost.mp done
      check (decide (s.checkApplicationReturnBody? body = some (core,type) ∧ s.checkApplicationReturnBody? body = s.checkApplication? r.source ∧
        s.checkReturnBody? body = none ∧ s.checkTypedLetReturnTree? [] owner body = none)) "independent Core/type or full checker equality changed"
      for fuel in List.range (cost+3) do
        have _ := LocalInputs.runApplication?_done_iff_of_cost child.hasType e (fuel := fuel)
        have _ := LocalInputs.runApplication?_outOfFuel_iff_of_cost child.hasType e (fuel := fuel)
        check (decide (s.runApplicationReturnBody? fuel body store = s.runApplication? fuel r.source store ∧
          s.runReturnBody? fuel body store = none)) "return changed full child outcome or old body gate"
        check (match s.runApplicationReturnBody? fuel body store with
          | some (tag,.done v t) => decide (tag = type ∧ cost ≤ fuel ∧ v = value ∧ t = final)
          | some (tag,.outOfFuel _) => decide (tag = type ∧ fuel < cost)
          | _ => false) "fixed independent result/store/cost changed"
      for spent in List.range cost do
        match stopped : Core.runStateful spent (.initial core s.environment.values store) with
        | .outOfFuel checkpoint =>
            have bodyStop := LocalInputs.runApplicationReturnBody?_eq_some_iff.mpr ⟨core,checked,stopped⟩
            have childStop : s.runApplication? spent r.source store = some (type,.outOfFuel checkpoint) := (runEq spent).symm.trans bodyStop
            have _ := LocalInputs.runApplication?_residual_of_outOfFuel e childStop
            for additional in [0,1,cost-spent,cost+2] do
              have _ := LocalInputs.runApplication?_resume childStop additional
              check (decide (s.runApplicationReturnBody? spent body store = some (type,.outOfFuel checkpoint) ∧
                s.runApplicationReturnBody? (spent+additional) body store = some (type,Core.runStateful additional checkpoint))) "identical original checkpoint/full resumption changed"
            check (decide (Core.runStateful (cost-spent) checkpoint = .done value final)) "exact saved residual changed"
        | _ => throw (IO.userError "original genuine checkpoint missing")
    else throw (IO.userError "independent actual expectation changed")
  else throw (IO.userError "independent source expectation changed")
private def fixtures : IO Unit := do
  let r := inputs .word reader writer readerTyped writerTyped 14
  let wr := inputs .word writer reader writerTyped readerTyped 14
  let a := inputs (.cell .word) allocator allocator allocatorTyped allocatorTyped 14
  let body ← parsed "{return f(x);}"; let ret ← returned body
  check (decide (ret.returnSpan.startByte = 1 ∧ ret.returnSpan.endByte = 13 ∧ ret.source.span.startByte = 8 ∧ ret.source.span.endByte = 12)) "original return keyword/semicolon/child ranges changed"
  for old in [23,91] do
    verify r "{return f(x);}" target .word (w old) 8 [w old] [w old]
    verify wr "{return f(x);}" target .word (w 14) 15 [w old] [w 14]
    verify a "{return f(x);}" target (.cell .word) (.cellRef .word 1) 8 [w old] [w old,w 14]
  verify r "{return (c ? f : g)(x);}" (.apply (.ifE (.var 3) (.var 1) (.var 2)) (.var 0)) .word (w 23) 11 [w 23] [w 23]
  verify r "{return f(x);}" target .word (.bool true) 8 [.bool true] [.bool true]
  have _ : ¬ Core.ValueHasType (.bool true) .word := by intro h; cases h
  have et : Core.RuntimeEnvironmentHasTypes [.word] r.environment.values r.context.values := .cons .word
    (.cons (.closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl)))
    (.cons (.closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))) (.cons .bool .nil)))
  have st : Core.StoreHasTypes [.word] [w 23] := Core.StoreHasTypes.nil.allocate .word .word
  let app ← application r ret.source
  let finite ← counted r [w 23] ret.source
  have _ := LocalInputs.runApplication?_runtime_has_exact_cost app.evidence.hasType et st
    ⟨finite.value, finite.final, finite.evidence.erase⟩
  for store in [[],[w 23],[.bool true]] do
    let cp : Core.State := ⟨.eval (.var 0) r.environment.values,[.applyClosure .word .word readBody [.cellRef .word 0]],store⟩
    if checked : r.checkApplication? ret.source = some (target,.word) then
      have stopped : r.runApplication? 3 ret.source store = some (.word,.outOfFuel cp) := LocalInputs.runApplication?_eq_some_iff.mpr ⟨target,checked,rfl⟩
      for additional in [0,4,5,9] do
        have _ := LocalInputs.runApplication?_resume stopped additional
        check (decide (r.runApplicationReturnBody? 3 body store = some (.word,.outOfFuel cp) ∧
          r.runApplicationReturnBody? (3+additional) body store = some (.word,Core.runStateful additional cp))) "fault/done resumption did not retain identical child state"
    else throw (IO.userError "original reader rejected")
  check (decide (r.runApplicationReturnBody? 7 body [] = some (.word,
    .fault (.invalidCellLocation 0) ⟨.ret (.cellRef .word 0),[.loadCellApply],[]⟩))) "return wrapper suppressed missing-cell fault"
  have runtimeEq (fuel) : r.runApplicationReturnBody? fuel body [w 23] = r.runApplication? fuel ret.source [w 23] :=
    (congrArg (fun b => r.runApplicationReturnBody? fuel b [w 23]) ret.shape).trans (r.runApplicationReturnBody?_return _ _ _ _ _)
  for fuel in [0,3,8,20] do
    have bodyNeverFaults (error : Core.MachineFault) (state : Core.State) :
        r.runApplicationReturnBody? fuel body [w 23] ≠ some (.word,.fault error state) := by
      rw [runtimeEq]; exact LocalInputs.runApplication?_runtime_never_faults et st ret.source fuel .word error state
    have _ := bodyNeverFaults
    if completed : r.runApplicationReturnBody? fuel body [w 23] = some (.word,.done (w 23) [w 23]) then
      have _ := LocalInputs.runApplication?_runtime_done_sound et st ((runtimeEq fuel).symm.trans completed)
      pure ()
    else pure ()
  let rejected ← parsed "{return (c ? f : missing)(x);}"; let rr ← returned rejected
  let rawChild ← counted r [w 23] rr.source
  have _ : LocalApplicationReturnBodyEvaluatesWithCost r.names r.environment [w 23] rejected rawChild.value rawChild.final rawChild.cost :=
    Eq.mp (congrArg (fun b => LocalApplicationReturnBodyEvaluatesWithCost r.names r.environment [w 23] b rawChild.value rawChild.final rawChild.cost) rr.shape.symm)
      (.application rawChild.evidence)
  check (decide (rawChild.value = w 23 ∧ rawChild.cost = 11 ∧ r.checkApplicationReturnBody? rejected = none)) "raw selected success bypassed whole body acceptance"
  for (text,old) in [("{return;}",some (Core.Expr.unit,Core.Ty.unit)),("{return x;}",some (.var 0,.word)),
      ("{}",none),("{return f(x);return x;}",none),("{f(x);return x;}",none),
      ("{if(c){return x;}else{return x;}}",none),("{{return f(x);}}",none),("{return f(f(x));}",none)] do
    let bad ← parsed text
    check (decide (r.checkApplicationReturnBody? bad = none ∧ r.checkReturnBody? bad = old)) "new exclusion or old singleton acceptance changed"
    have _ := elaborateLocalApplicationReturnBody?_eq_none_iff (table := r.names) (context := r.context) (body := bad)
    for fuel in [0,3,20] do
      have _ := LocalInputs.runApplicationReturnBody?_eq_none_iff (inputs := r) (body := bad) fuel [w 23]
      check (decide (r.runApplicationReturnBody? fuel bad [w 23] = none)) "unsupported whole body became present"
  let bare ← parsed "{return;}"; let pureReturn ← parsed "{return x;}"
  check (decide (r.runReturnBody? 1 bare [w 23] = some (.unit,.done .unit [w 23]) ∧
    r.runReturnBody? 1 pureReturn [w 23] = some (.word,.done (w 14) [w 23]))) "old successful singleton runners changed"
end ParsedApplicationReturnBodies
open ParsedApplicationReturnBodies
def frontendParsedApplicationReturnBodyTests : IO Unit := fixtures
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedApplicationReturnBodyEntries
/-! Original parameter-only records feed the separate return-call profile.
Independent children, actual body paths and costs precede all executable checks. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ApplicationReturnBodyEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnActualCall", by decide⟩], by decide⟩⟩, 23⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def target : Core.Expr := .apply (.var 1) (.var 0)
private def text := "function invoke(f:F,x:A) returns(R){return f(x);}"
private def parsed : IO Syntax.FunctionDecl := do
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
private structure Original (body : Syntax.Block) where
  blockSpan : Syntax.SourceSpan
  returnSpan : Syntax.SourceSpan
  span : Syntax.SourceSpan
  argumentsSpan : Syntax.SourceSpan
  callee : Syntax.Expr
  argument : Syntax.Expr
  shape : body = ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .call callee ⟨argumentsSpan, [argument]⟩⟩)⟩]⟩
private def original (body : Syntax.Block) : IO (Original body) := do
  match shape : body with
  | ⟨bs, [⟨rs, .returnStmt (some ⟨s, .call f ⟨args, [x]⟩⟩)⟩]⟩ =>
      check (bs.contains rs && rs.contains s && s.contains f.span && s.contains args && args.contains x.span &&
        decide (f.span.endByte ≤ args.startByte)) "original return/call spans changed"
      return ⟨bs, rs, s, args, f, x, shape⟩
  | _ => throw (IO.userError "not original singleton return-call")
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
      have path := Core.Steps.cons .enterLet (.cons (.var (index := 0) rfl) (.cons .bindLet (ih (value :: rest) k)))
      have count : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [count]; exact path
private def execute (argument : TypedRuntimeArgument) (output : Core.Ty) (body : Core.Expr) (captured : Core.Environment)
    (world : Core.StoreTyping) (s t : Core.Store) (value : Core.Value) (bodyCost : Nat)
    (argumentTyped : Core.RuntimeValueHasType world argument.value argument.type)
    (closureTyped : Core.RuntimeValueHasType world (.closure argument.type output body captured) (.function argument.type output))
    (storeTyped : Core.StoreHasTypes world s)
    (bodyPath : ∀ k, Core.Steps bodyCost ⟨.eval body (argument.value :: captured), k, s⟩ ⟨.ret value, k, t⟩) : IO Unit := do
  let f : TypedRuntimeArgument := ⟨.function argument.type output, .closure argument.type output body captured, closureTyped.erase⟩
  let args := [f, argument]; let types := [(["F"], f.type), (["A"], argument.type), (["R"], output)]
  let source ← parsed
  let ps ← parameters types source.value.signature.parameters.elements args
  let inputs := ps.actual
  have _ := RuntimeParametersDeclare.complete ps.declared
  have _ := RuntimeParametersBind.complete ps.bound
  have _ := RuntimeParametersBind.erase_values ps.bound
  check (decide (inputs.names = ps.statics.names ∧ inputs.context = ps.statics.context ∧
    inputs.bindings.map (fun b => (b.name, b.id, b.type, b.value)) =
      [("x", ⟨owner, 1⟩, argument.type, argument.value), ("f", ⟨owner, 0⟩, f.type, f.value)])) "original records changed"
  let rows : PLift (inputs.environment.values = (args.map (·.value)).reverse ∧ inputs.context.values = [argument.type, f.type]) ←
    if same : inputs.environment.values = (args.map (·.value)).reverse ∧ inputs.context.values = [argument.type, f.type] then pure ⟨same⟩
    else throw (IO.userError "original projection order changed")
  have runtimeTyped : Core.RuntimeEnvironmentHasTypes world inputs.environment.values inputs.context.values := by
    rw [rows.down.1, rows.down.2]; exact .cons argumentTyped (.cons closureTyped .nil)
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
      else throw (IO.userError "declared result changed")
  | _ => throw (IO.userError "original return annotation changed")
  let o ← original source.value.body
  let expression : Syntax.Expr := ⟨o.span, .call o.callee ⟨o.argumentsSpan, [o.argument]⟩⟩
  let fn ← reference inputs o.callee; let arg ← reference inputs o.argument
  if exactChildren : fn.type = f.type ∧ arg.type = argument.type ∧ fn.core = .var 1 ∧ arg.core = .var 0 then
    have child : LocalFunctionApplicationElaborates inputs.names inputs.context expression target output := by
      have e := LocalFunctionApplicationElaborates.call (span := o.span) (argumentsSpan := o.argumentsSpan)
        fn.resolution fn.lowered (exactChildren.1 ▸ fn.typing) arg.resolution arg.lowered (exactChildren.2.1 ▸ arg.typing)
      simpa only [target, expression, exactChildren.2.2.1, exactChildren.2.2.2] using e
    have elaboration : LocalApplicationReturnBodyElaborates inputs.names inputs.context source.value.body target output := by
      rw [o.shape]; exact .application child
    have typing : LocalApplicationReturnBodyHasType inputs.names inputs.context source.value.body output := by
      rw [o.shape]; exact .application child.hasType
    let fp ← observed inputs o.callee f.value; let ap ← observed inputs o.argument argument.value
    have costed : LocalFunctionApplicationEvaluatesWithCost inputs.names inputs.environment s expression value t (bodyCost + 5) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        LocalFunctionApplicationEvaluatesWithCost.call (span := o.span) (argumentsSpan := o.argumentsSpan) (fp.evidence s) (ap.evidence s) (bodyPath [])
    have rawBody : LocalApplicationReturnBodyEvaluates inputs.names inputs.environment s source.value.body value t := by
      rw [o.shape]; exact .application costed.erase
    have bodyCosted : LocalApplicationReturnBodyEvaluatesWithCost inputs.names inputs.environment s source.value.body value t (bodyCost + 5) := by
      rw [o.shape]; exact .application costed
    have manual (k) : Core.Steps (bodyCost + 5) ⟨.eval target inputs.environment.values, k, s⟩ ⟨.ret value, k, t⟩ := by
      rw [rows.down.1]
      exact .cons .enterApply (.cons (.var rfl) (.cons .beginArgument (.cons (.var rfl) (.cons .invokeClosure (bodyPath k)))))
    have accepted := elaboration.complete
    have _ := elaborateLocalApplicationReturnBody?_sound accepted
    have _ := elaborateLocalApplicationReturnBody?_iff.mp accepted
    have _ := typing.type_unique elaboration.hasType
    have _ := elaboration.result_unique (elaborateLocalApplicationReturnBody?_iff.mpr elaboration |> elaborateLocalApplicationReturnBody?_sound)
    have _ := typing.elaborates_exact
    have _ := localApplicationReturnBodyHasType_iff_elaborates.mpr ⟨target, elaboration⟩
    have _ := elaboration.core_hasType
    have _ := elaborateLocalApplicationReturnBody?_core_hasType accepted
    have _ := elaborateLocalApplicationReturnBody?_eq_none_iff (table := inputs.names) (context := inputs.context) (body := source.value.body)
    have _ := rawBody.deterministic bodyCosted.erase
    have _ := rawBody.exists_cost
    have _ := localApplicationReturnBodyEvaluates_iff_exists_cost.mpr ⟨_, bodyCosted⟩
    have _ := bodyCosted.deterministic ((elaboration.evaluatesWithCost_iff_steps inputs.sameIds).mpr (manual []))
    have _ := (elaboration.evaluates_iff inputs.sameIds).mpr (Core.steps_from_initial_sound (manual []))
    have _ := (elaboration.evaluates_iff inputs.sameIds).mp rawBody
    have _ := bodyCosted.toStepsWithContinuation elaboration inputs.sameIds [.letBody .unit []]
    have checked := LocalInputs.checkApplicationReturnBody?_iff_elaborates.mpr elaboration
    have checkEqual : inputs.checkApplicationReturnBody? source.value.body = inputs.checkApplication? expression := by
      rw [o.shape]; exact inputs.checkApplicationReturnBody?_return o.blockSpan o.returnSpan expression
    have equal (fuel store) : inputs.runApplicationReturnBody? fuel source.value.body store = inputs.runApplication? fuel expression store := by
      rw [o.shape]; exact inputs.runApplicationReturnBody?_return fuel o.blockSpan o.returnSpan expression store
    let cost := bodyCost + 5
    have done := (LocalInputs.runApplicationReturnBody?_done_iff_typed_cost).mpr ⟨typing, cost, bodyCosted, Nat.le_refl cost⟩
    have _ := LocalInputs.runApplicationReturnBody?_done_iff_typed_cost.mp done
    have _ := LocalInputs.runApplicationReturnBody?_eq_some_iff.mp done
    have childDone := (equal cost s) ▸ done
    have _ := LocalInputs.runApplication?_runtime_done_sound runtimeTyped storeTyped childDone
    have agreement : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future t ∧
        Core.RuntimeValueHasType future value output := by
      obtain ⟨future, final, v, count, extension, st, vt, evaluated, _⟩ :=
        LocalInputs.runApplication?_runtime_has_exact_cost child.hasType runtimeTyped storeTyped ⟨value, t, costed.erase⟩
      obtain ⟨rfl, rfl, _⟩ := costed.deterministic evaluated
      exact ⟨future, extension, st, vt⟩
    have _ := agreement
    check (decide (inputs.checkApplicationReturnBody? source.value.body = some (target, output) ∧
      inputs.checkApplicationReturnBody? source.value.body = inputs.checkApplication? expression)) "static wrapper changed exact child"
    check (decide (inputs.runApplicationReturnBody? 3 source.value.body s = some (output, .outOfFuel
      ⟨.eval (.var 0) inputs.environment.values, [.applyClosure argument.type output body captured], s⟩))) "original child checkpoint changed"
    check (decide (Core.runStateful cost ⟨.eval target inputs.environment.values, [.letBody .unit []], s⟩ =
      .outOfFuel ⟨.ret value, [.letBody .unit []], t⟩)) "pending frame was treated as completed"
    for fuel in List.range (cost + 3) do
      have _ := LocalInputs.runApplicationReturnBody?_eq_none_iff (inputs := inputs) (body := source.value.body) fuel s
      have _ := (LocalInputs.runApplicationReturnBody?_eq_some_iff (fuel := fuel) (store := s)).mpr ⟨target, checked, rfl⟩
      have _ := LocalInputs.runApplication?_done_iff_of_cost child.hasType costed (fuel := fuel)
      have _ := LocalInputs.runApplication?_runtime_never_faults runtimeTyped storeTyped expression fuel output
      check ((compileRuntimeFunction? types owner source).isNone && (prepareRuntimeFunction? types owner source args).isNone &&
        (runRuntimeFunction? types owner source args fuel s).isNone && (inputs.run? fuel expression s).isNone) "return-call leaked into old endpoints"
      check (decide (inputs.runApplicationReturnBody? fuel source.value.body s = inputs.runApplication? fuel expression s ∧
        inputs.runApplicationReturnBody? fuel source.value.body s = some (output, Core.runStateful fuel (.initial target inputs.environment.values s)))) "full return/child result differs"
      match stopped : inputs.runApplicationReturnBody? fuel source.value.body s with
      | some (_, .done v final) => check (decide (cost ≤ fuel ∧ v = value ∧ final = t)) "independent cost/value/store differs"
      | some (_, .outOfFuel checkpoint) =>
          have childStopped := (equal fuel s) ▸ stopped
          have _ := LocalInputs.runApplication?_residual_of_outOfFuel costed childStopped
          check (decide (fuel < cost ∧ Core.runStateful (cost - fuel) checkpoint = .done value t)) "genuine remaining path differs"
          for additional in [0, 1, cost - fuel, cost + 2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (inputs.runApplicationReturnBody? (fuel + additional) source.value.body s =
              some (output, Core.runStateful additional checkpoint))) "genuine full-result resumption differs"
      | _ => throw (IO.userError "actual runtime typed body failed or faulted")
    for otherStore in [[], [.bool true]] do
      match stopped : inputs.runApplicationReturnBody? 3 source.value.body otherStore with
      | some (tag, .outOfFuel checkpoint) =>
          have childStopped := (equal 3 otherStore) ▸ stopped
          for additional in [0, 4, 5, cost + 2] do
            have _ := LocalInputs.runApplication?_resume childStopped additional
            check (decide (tag = output ∧ inputs.runApplicationReturnBody? (3 + additional) source.value.body otherStore =
              some (output, Core.runStateful additional checkpoint))) "unvalidated store full-result replay changed"
      | _ => throw (IO.userError "original call protocol lost its genuine checkpoint")
  else throw (IO.userError "independent original children changed")
end ApplicationReturnBodyEntries
open ApplicationReturnBodyEntries
def frontendParsedApplicationReturnBodyEntryTests : IO Unit := do
  for n in [0, 1, 4, 9] do
    execute ⟨.word, w 14, .word⟩ .word (delayed n) [] [] [] [] (w 14) (3 * n + 1)
      .word (.closure .nil (delayedTyped n .word [])) .nil (delayedPath n (w 14) [] [])
  for current in [3, 17] do
    have st : Core.StoreHasTypes [.word] [w current] := Core.StoreHasTypes.nil.allocate .word .word
    execute ⟨.unit, .unit, .unit⟩ .word (.loadCell (.var 1)) [.cellRef .word 0] [.word] [w current] [w current] (w current) 3
      .unit (.closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl))) st
      (fun _ => .cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
    execute ⟨.word, w 9, .word⟩ (.cell .word) (.newCell .word (.var 0)) [] [.word] [w current] [w current, w 9] (.cellRef .word 1) 3
      .word (.closure .nil (.newCell (.var rfl))) st (fun _ => .cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl)))
    execute ⟨.word, w 9, .word⟩ .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0]
      [.word] [w current] [w 9] (w 9) 10 .word
      (.closure (.cons (.cellRef rfl) .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))) st
      (fun _ => .cons .enterLet (.cons .enterStoreCell (.cons (.var rfl) (.cons (.beginStoreCellValue rfl)
        (.cons (.var rfl) (.cons (.applyStoreCell rfl) (.cons .bindLet (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl))))))))))
  for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨4⟩) (.namedData ⟨8⟩)] do
    let a : TypedRuntimeArgument := ⟨.function type type, .closure type type (.var 0) [], .closure .nil (.var rfl)⟩
    execute a a.type (.var 0) [] [] [] [] a.value 1
      (.closure .nil (.var rfl)) (.closure .nil (.var rfl)) .nil (fun _ => .cons (.var rfl) .refl)
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDiscardEntries
/-! Original semicolon prefixes preserve source rows while hidden Core binders
strictly discard arbitrary actual values. Costs and paths have independent oracles. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace DiscardEntries
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"DiscardEntry", by decide⟩], by decide⟩⟩, 17⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def table (type : Core.Ty) : TypeNameTable := [(["T"], type), (["Bool"], .bool)]
private def parsed (content : String) : IO Syntax.FunctionDecl := do
  let file : Syntax.SourceFile := ⟨⟨.main, "discard-entry.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError "original declaration did not parse")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (source.span = ⟨file.id, 0, content.utf8ByteSize⟩) && source.span.contains source.value.body.span) s!"original complete ranges changed: {content}"
  return source
private structure Meaning (types : TypeNameTable) (source : Syntax.TypeExpr) where
  type : Core.Ty
  evidence : StructuralTypeDenotes types source type
private def meaning (types : TypeNameTable) (source : Syntax.TypeExpr) : IO (Meaning types source) := do
  match atSource : source with
  | ⟨_, .named name none⟩ =>
      match found : types.lookup? (qualifiedTypeNameKey name) with
      | some type => return ⟨type, by rw [atSource]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩
      | none => throw (IO.userError "independent type leaf missing")
  | ⟨_, .tuple [left, right]⟩ =>
      let a ← meaning types left; let b ← meaning types right
      return ⟨.product a.type b.type, by rw [atSource]; exact .pair a.evidence b.evidence⟩
  | _ => throw (IO.userError "outside independent annotation grammar")
termination_by sizeOf source
private structure Parameters (types : TypeNameTable) (initial : LocalTypeInputs) (params : List Syntax.FunctionParameter) where
  inputs : LocalTypeInputs
  evidence : RuntimeParametersDeclareFrom types owner initial params inputs
private def parameters (types : TypeNameTable) (initial : LocalTypeInputs)
    (params : List Syntax.FunctionParameter) : IO (Parameters types initial params) := do
  match atParams : params with
  | [] => return ⟨initial, by rw [atParams]; exact .nil⟩
  | ⟨span, .typed none name annotation⟩ :: rest =>
      check (span.contains name.span && span.contains annotation.span) "original parameter range changed"
      let m ← meaning types annotation
      if unused : name.value ∉ initial.names.map Prod.fst then
        let tail ← parameters types (initial.bindFresh owner name.value m.type) rest
        return ⟨tail.inputs, by rw [atParams]; exact .cons m.evidence unused tail.evidence⟩
      else throw (IO.userError "duplicate parameter")
  | _ => throw (IO.userError "unsupported original parameter")
private structure Expression (s : LocalTypeInputs) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
private def expression (s : LocalTypeInputs) (source : Syntax.Expr) : IO (Expression s source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | some id =>
          match typed : s.context.lookup? id, indexed : Resolved.LocalScope.index? s.ids id with
          | some type, some index => return ⟨.var id, .var index, type,
              by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named),
              .var (Resolved.LocalScope.index?_iff.mp indexed), .var (Resolved.LocalScope.lookup?_iff.mp typed)⟩
          | _, _ => throw (IO.userError "independent context row missing")
      | none => throw (IO.userError "independent name missing")
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s left; let b ← expression s right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s left; let b ← expression s right
      if leftType : a.type = .word then
        if bt : b.type = .word then
          return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word,
            by rw [atSource]; exact .subtract a.resolution b.resolution,
            .binary a.lowered b.lowered,
            .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
              (show Resolved.HasType s.context b.resolved .word from bt ▸ b.typing)⟩
        else throw (IO.userError "right operand not Word")
      else throw (IO.userError "left operand not Word")
  | _ => throw (IO.userError "outside independent expression grammar")
termination_by sizeOf source
private structure Body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  evidence : TypedLetReturnTreeElaborates types owner s source core type
private def body (types : TypeNameTable) (s : LocalTypeInputs) (source : Syntax.Block) : IO (Body types s source) := do
  match atSource : source with
  | ⟨_, [⟨_, .returnStmt (some returned)⟩]⟩ =>
      let a ← expression s returned
      return ⟨a.core, a.type, by rw [atSource]; exact .single (.expression a.resolution
        (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing)⟩
  | ⟨span, ⟨ls, .letDecl name none (some initializer)⟩ :: rest⟩ =>
      check (ls.contains name.span && ls.contains initializer.span) "original none annotation spans changed"
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s initializer
        let b ← body types (s.bindFresh owner name.value a.type) ⟨span, rest⟩
        return ⟨.letE a.core b.core, b.type, by rw [atSource]; exact .inferred unused a.resolution a.lowered a.typing b.evidence⟩
      else throw (IO.userError "ancestor name reused")
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s source; let b ← body types s ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type,
        by rw [atSource]; exact .discard a.resolution a.lowered a.typing b.evidence⟩
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s guard; let a ← body types s yes; let b ← body types s no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
          return ⟨.ifE c.core a.core b.core, a.type, by rw [atSource]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.evidence (bt ▸ b.evidence)⟩
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard is not Bool")
  | _ => throw (IO.userError "outside independent body grammar")
termination_by sizeOf source
private structure Compilation (types : TypeNameTable) (source : Syntax.FunctionDecl) where
  compiled : CompiledRuntimeFunction
  evidence : RuntimeFunctionCompiles types owner source compiled
private def compile (types : TypeNameTable) (source : Syntax.FunctionDecl) : IO (Compilation types source) := do
  let ps ← parameters types .empty source.value.signature.parameters.elements
  let b ← body types ps.inputs source.value.body
  match atClause : source.value.signature.returnsClause with
  | some ⟨_, ⟨_, [returned]⟩⟩ =>
      let m ← meaning types returned
      if same : m.type = b.type then
        if policy : source.value.signature.genericParameters = none ∧ source.value.signature.whereClause = none ∧
            source.value.signature.modifiers.publicMarker = none ∧ source.value.signature.modifiers.payableMarker = none then
          return ⟨⟨ps.inputs, b.core, b.type⟩, ⟨⟨policy.1, policy.2.1, policy.2.2.1, policy.2.2.2,
            by rw [atClause]; exact .single (same ▸ m.evidence)⟩, ps.evidence, b.evidence⟩⟩
        else throw (IO.userError "header policy rejected")
      else throw (IO.userError "return contract differs")
  | _ => throw (IO.userError "return clause is not singleton")

private def mixed : Core.Expr := .letE (.var 2) (.letE (.var 3) (.ifE (.var 2)
  (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1))))
private theorem mixedPaths (x y : Core.Value) (c : Bool) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (if c then 17 else 13) ⟨.eval mixed [.bool c, y, x], k, store⟩ ⟨.ret x, k, store⟩ := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseFalse (.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl))))))))))))
  · exact .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons .enterLet (.cons (.var rfl)
      (.cons .bindLet (.cons .enterIf (.cons (.var rfl) (.cons .chooseTrue (.cons .enterLet
        (.cons .enterPair (.cons (.var rfl) (.cons .enterPairRight (.cons (.var rfl)
          (.cons .applyPair (.cons .bindLet (.cons (.var rfl) .refl))))))))))))))))
private def spine : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var index) (spine n (index + 1))
private theorem spinePaths (n index : Nat) (env : Core.Environment) (value : Core.Value)
    (found : env[index]? = some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3 * n + 1) ⟨.eval (spine n index) env, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing index env with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have tail := ih (index + 1) (value :: env) (by simpa using found)
      have path := Core.Steps.cons .enterLet (.cons (.var found) (.cons .bindLet tail))
      have arithmetic : 3 * (n + 1) + 1 = 3 * n + 1 + 1 + 1 + 1 := by omega
      rw [arithmetic]
      exact path
private theorem arithmeticPaths (store : Core.Store) (k : List Core.Frame) :
    Core.Steps 8 ⟨.eval (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) [.bool true, w 2, w 9], k, store⟩
      ⟨.ret (w 9), k, store⟩ :=
  .cons .enterLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight
    (.cons (.var rfl) (.cons (.applyBinary rfl) (.cons .bindLet (.cons (.var rfl) .refl)))))))
private def text (body : String) := "function f(x:T,y:T,c:Bool) returns(T){" ++ body ++ "}"
private def verify (content : String) (x y : TypedRuntimeArgument) (c : Bool)
    (expectedCore : Core.Expr) (expectedValue : Core.Value) (cost : Nat)
    (paths : ∀ store k, Core.Steps cost ⟨.eval expectedCore [.bool c, y.value, x.value], k, store⟩
      ⟨.ret expectedValue, k, store⟩) : IO Unit := do
  let source ← parsed content; let proof ← compile (table x.type) source
  let args := [x, y, (⟨.bool, .bool c, .bool⟩ : TypedRuntimeArgument)]
  check (decide (proof.compiled.core = expectedCore ∧ proof.compiled.returnType = x.type ∧
    proof.compiled.inputs.names = [("c", ⟨owner, 2⟩), ("y", ⟨owner, 1⟩), ("x", ⟨owner, 0⟩)] ∧
    proof.compiled.inputs.context.values = [.bool, x.type, x.type])) "independent original parameter layout changed"
  let some prepared := prepareRuntimeFunction? (table x.type) owner source args | throw (IO.userError "actual preparation missing")
  check (decide (prepared.core = expectedCore ∧ prepared.returnType = x.type ∧
    prepared.inputs.ids = proof.compiled.inputs.ids ∧ prepared.inputs.names = proof.compiled.inputs.names ∧
    prepared.inputs.environment.values = [.bool c, y.value, x.value])) "hidden discard binder leaked into parameter records"
  if different : proof.compiled.core ≠ .var 2 then
    have _ : ¬ RuntimeFunctionCompiles (table x.type) owner source { proof.compiled with core := .var 2 } :=
      fun wrong => different (congrArg CompiledRuntimeFunction.core (proof.evidence.result_unique wrong))
    pure ()
  else throw (IO.userError "strict work unexpectedly vanished")
  for store in [[], [w 91, .cellRef .word 999]] do
    have _ := paths store [.unaryApply .wordNot]
    let start := Core.State.initial expectedCore [.bool c, y.value, x.value] store
    check (decide (evaluateTypedLetReturnTreeWithCost? owner prepared.inputs.names prepared.inputs.environment source.value.body =
      some (expectedValue, cost) ∧ cost ≤ typedLetReturnTreeFuelBound source.value.body)) "strict source value/cost changed"
    for fuel in List.range (cost + 3) do
      check (decide (runRuntimeFunction? (table x.type) owner source args fuel store =
        some (x.type, Core.runStateful fuel start))) "whole entry differs from fixed Core"
      check (match Core.runStateful fuel start with
        | .done value final => decide (cost ≤ fuel ∧ value = expectedValue ∧ final = store)
        | .outOfFuel _ => decide (fuel < cost)
        | _ => false) "strict fuel threshold changed"
    for spent in List.range cost do
      match exhausted : runRuntimeFunction? (table x.type) owner source args spent store with
      | some (type, .outOfFuel cp) =>
          have _ := runRuntimeFunction?_resume exhausted (cost - spent)
          check (decide (type = x.type ∧ Core.runStateful (cost - spent) cp = .done expectedValue store)) "actual checkpoint residual changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done expectedValue store)) "three chunks lost hidden value"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done expectedValue store) "restart substituted for resume"
      | _ => throw (IO.userError "genuine entry checkpoint missing")
private def checkedOpaque (type : Core.Ty) (x y : Core.Value) (xt : Core.ValueHasType x type) (yt : Core.ValueHasType y type) : IO Unit := do
  for c in [false, true] do
    verify (text "x;let z=x;if(c){(z,y);return z;}else{y;return z;}") ⟨type, x, xt⟩ ⟨type, y, yt⟩ c
      mixed x (if c then 17 else 13) (mixedPaths x y c)
end DiscardEntries
open DiscardEntries

def frontendParsedDiscardEntryTests : IO Unit := do
  for depth in [1, 3, 10, 32] do
    let prefixText := String.join (List.replicate depth "x;")
    verify (text (prefixText ++ "return x;")) ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true
      (spine depth 2) (w 9) (3 * depth + 1) (spinePaths depth 2 [.bool true, w 2, w 9] (w 9) rfl)
  verify (text "x - y;return x;") ⟨.word, w 9, .word⟩ ⟨.word, w 2, .word⟩ true
    (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (w 9) 8 arithmeticPaths
  checkedOpaque .word (w 9) (w 2) .word .word
  checkedOpaque (.cell .word) (.cellRef .word 700) (.cellRef .word 701) .cellRef .cellRef
  checkedOpaque (.function .word .word) (.closure .word .word (.var 0) []) (.closure .word .word (.var 1) [w 7])
    (.closure .nil (.var rfl)) (.closure (.cons .word .nil) (.var rfl))
  checkedOpaque .unit .unit .unit .unit .unit
  checkedOpaque .bool (.bool true) (.bool false) .bool .bool
  for c in [false, true] do
    for store in [[], [w 91]] do
      let values := [.bool c, w 2, w 9]
      let tail : Core.Expr := .letE (.var 3) (.ifE (.var 2)
        (.letE (.pair (.var 0) (.var 3)) (.var 1)) (.letE (.var 3) (.var 1)))
      check (decide (Core.runStateful 2 (.initial mixed values store) =
        .outOfFuel ⟨.ret (w 9), [.letBody tail values], store⟩ ∧
        Core.runStateful 3 (.initial mixed values store) = .outOfFuel ⟨.eval tail (w 9 :: values), [], store⟩))
        "actual hidden binder or saved original environment changed"
      check (decide (Core.runStateful 6 (.initial (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) values store) =
        .outOfFuel ⟨.ret (w 7), [.letBody (.var 3) values], store⟩)) "unused arithmetic head was skipped"
  for type in [Core.Ty.namedData ⟨90⟩, .product (.namedData ⟨90⟩) (.cell (.namedData ⟨13⟩))] do
    let source ← parsed (text "x;let z=x;if(c){(z,y);return z;}else{y;return z;}")
    let proof ← compile (table type) source
    check (decide (proof.compiled.core = mixed ∧ proof.compiled.returnType = type ∧
      Core.infer? proof.compiled.inputs.context.values (.var 2) = some type)) "nominal static or same-typed wrong-Core contrast changed"
    check ((elaborateTypedLetReturnBody? (table type) owner proof.compiled.inputs source.value.body).isNone) "old prefix adapter widened"
  for body in ["x;", "missing;return x;", "f(x);return x;", "x= y;return x;", "return x;y;",
      "if(c){x;return x;}else{missing;return x;}"] do
    let source ← parsed (text body)
    check ((compileRuntimeFunction? (table .word) owner source).isNone) "invalid written head/tail accepted"
  let source ← parsed (text "x;return x;")
  match source.value.body with
  | ⟨span, ⟨statementSpan, .expression expression true⟩ :: rest⟩ =>
      check (statementSpan.contains expression.span && decide (expression.span.endByte + 1 = statementSpan.endByte))
        "original explicit semicolon range changed"
      let falseFlag : Syntax.Block := ⟨span, ⟨statementSpan, .expression expression false⟩ :: rest⟩
      let proof ← compile (table .word) source
      check ((elaborateTypedLetReturnTree? (table .word) owner proof.compiled.inputs falseFlag).isNone) "missing flag was silently repaired"
  | _ => throw (IO.userError "original expression statement shape changed")
  let args : List TypedRuntimeArgument := [⟨.word, w 9, .word⟩, ⟨.word, w 2, .word⟩, ⟨.bool, .bool true, .bool⟩]
  for badArgs in [[], args.drop 1, args ++ [⟨.unit, .unit, .unit⟩], args.reverse] do
    check ((prepareRuntimeFunction? (table .word) owner source badArgs).isNone) "discard bypassed argument count/type/order"
  let skipped ← parsed (text "if(c){x;return x;}else{missing;return x;}")
  let some inputs := bindRuntimeParameters? (table .word) owner skipped.value.signature.parameters.elements args
    | throw (IO.userError "original skipped-arm arguments did not bind")
  check (decide (evaluateTypedLetReturnTreeWithCost? owner inputs.names inputs.environment skipped.value.body = some (w 9, 7) ∧
    compileRuntimeFunction? (table .word) owner skipped = none)) "raw selected success replaced whole written checking"
  for content in ["function f<T>(x:T) returns(T){x;return x;}", "function f(x:T,x:T) returns(T){x;return x;}",
      "function f(x:T) returns(Bool){x;return x;}"] do
    check ((compileRuntimeFunction? (table .word) owner (← parsed content)).isNone) "discard bypassed the whole header or parameter policy"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedDiscardStatements
/-! Original strict statement prefixes, independent source evidence and manually
composed Core paths. Discard keeps the source scope; only Core inserts a value. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace DiscardStatements
private def check (p : Bool) (label : String) : IO Unit := do
  unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Discard", by decide⟩], by decide⟩⟩, 17⟩
private def other : Resolved.DeclarationId := { owner with declarationIndex := 71 }
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def inputs (type : Core.Ty) : LocalTypeInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool⟩, ⟨"r", id 2, .word⟩, ⟨"x", id 7, type⟩, ⟨"x", id 3, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def env (value : Core.Value) (choice : Bool) : Resolved.Environment :=
  [(⟨other, 999⟩, .bool choice), (id 2, w 2), (id 7, value), (id 3, .bool false)]
private def stores : List Core.Store := [[.unit, w 40], [w 91, .cellRef .word 40, .bool false]]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := ⟨⟨.main, "discard.sol"⟩, content⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"complete block rejected: {content}")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd &&
    decide (body.span = ⟨file.id, 0, content.utf8ByteSize⟩)) s!"{content}: original block/range changed"
  return body
private structure Expression (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  resolved : Resolved.Expr
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  resolution : ResolvesLocalExpression s.names source resolved
  lowered : Resolved.Lowers s.ids resolved core
  typing : Resolved.HasType s.context resolved type
  raw : LocalExpressionEvaluatesWithCost s.names e store source value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def expression (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (source : Syntax.Expr) : IO (Expression s e store source) := do
  match atSource : source with
  | ⟨_, .identifier name⟩ =>
      match named : s.names.lookup? name.value with
      | none => throw (IO.userError "independent name absent")
      | some binder =>
          match typed : s.context.lookup? binder, found : e.lookup? binder, indexed : Resolved.LocalScope.index? s.ids binder with
          | some type, some value, some index =>
              let position := Resolved.LocalScope.index?_iff.mp indexed
              return ⟨.var binder, .var index, type, value, 1,
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named), .var position,
                .var (Resolved.LocalScope.lookup?_iff.mp typed),
                by rw [atSource]; exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found),
                fun _ => .cons (.var ((Resolved.LocalScope.lookup_iff_getElem? (aligned.symm ▸ position)).mp
                  (Resolved.LocalScope.lookup?_iff.mp found))) .refl⟩
          | _, _, _ => throw (IO.userError "independent row absent")
  | ⟨_, .tuple ⟨_, []⟩⟩ => return ⟨.unit, .unit, .unit, .unit, 1,
      by rw [atSource]; exact .unit, .unit, .unit, by rw [atSource]; exact .unit, fun _ => .cons .unit .refl⟩
  | ⟨_, .tuple ⟨_, [left, right]⟩⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      return ⟨.pair a.resolved b.resolved, .pair a.core b.core, .product a.type b.type, .pair a.value b.value, a.cost + b.cost + 3,
        by rw [atSource]; exact .pair a.resolution b.resolution, .pair a.lowered b.lowered, .pair a.typing b.typing,
        by rw [atSource]; exact .pair a.raw b.raw, fun k => by
          have path := Core.Steps.cons .enterPair ((a.paths (.pairRight b.core e.values :: k)).trans
            (.cons .enterPairRight ((b.paths _).trans (.cons .applyPair .refl))))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let a ← expression s e aligned store left; let b ← expression s e aligned store right
      match av : a.value, bv : b.value with
      | .word x, .word y =>
          if leftType : a.type = .word then
            if rightType : b.type = .word then
            return ⟨.binary .wordSub a.resolved b.resolved, .binary .wordSub a.core b.core, .word, .word (x.sub y), a.cost + b.cost + 3,
              by rw [atSource]; exact .subtract a.resolution b.resolution, .binary a.lowered b.lowered,
              .binary (show Resolved.HasType s.context a.resolved .word from leftType ▸ a.typing)
                (show Resolved.HasType s.context b.resolved .word from rightType ▸ b.typing),
              by rw [atSource]; exact .subtract (av ▸ a.raw) (bv ▸ b.raw), fun k => by
                have path := Core.Steps.cons .enterBinary ((av ▸ a.paths (.binaryRight .wordSub b.core e.values :: k)).trans
                  (.cons .enterBinaryRight ((bv ▸ b.paths _).trans (.cons (.applyBinary rfl) .refl))))
                simpa only [Nat.add_assoc] using path⟩
            else throw (IO.userError "right is not Word")
          else throw (IO.userError "left is not Word")
      | _, _ => throw (IO.userError "actual operand not Word")
  | _ => throw (IO.userError "outside independent expression script")
termination_by sizeOf source
private structure Certificate (s : LocalTypeInputs) (e : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  core : Core.Expr
  type : Core.Ty
  value : Core.Value
  cost : Nat
  elaboration : TypedLetReturnTreeElaborates types owner s body core type
  raw : TypedLetReturnTreeEvaluatesWithCost owner s.names e store body value store cost
  paths : ∀ k, Core.Steps cost ⟨.eval core e.values, k, store⟩ ⟨.ret value, k, store⟩
private def certify (s : LocalTypeInputs) (e : Resolved.Environment) (aligned : e.ids = s.ids)
    (store : Core.Store) (body : Syntax.Block) : IO (Certificate s e store body) := do
  match atBody : body with
  | ⟨_, [⟨_, .returnStmt (some source)⟩]⟩ =>
      let a ← expression s e aligned store source
      return ⟨a.core, a.type, a.value, a.cost,
        by rw [atBody]; exact .single (.expression a.resolution (by simpa only [LocalTypeInputs.context_ids] using a.lowered) a.typing),
        by rw [atBody]; exact .single (.expression a.raw), a.paths⟩
  | ⟨span, ⟨_, .expression source true⟩ :: rest⟩ =>
      let a ← expression s e aligned store source
      let b ← certify s e aligned store ⟨span, rest⟩
      return ⟨.letE a.core (b.core.weakenAt 0), b.type, b.value, a.cost + b.cost + 2,
        by rw [atBody]; exact .discard a.resolution a.lowered a.typing b.elaboration,
        by rw [atBody]; exact .discard a.raw b.raw, fun k => by
          have shifted := (b.paths []).weakenAt_zero_localFragment b.elaboration.localFragment a.value k
          have path := Core.Steps.cons .enterLet
            ((a.paths (.letBody (b.core.weakenAt 0) e.values :: k)).trans (.cons .bindLet shifted))
          simpa only [Nat.add_assoc] using path⟩
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      if unused : name.value ∉ s.names.map Prod.fst then
        let a ← expression s e aligned store initializer
        let next := s.bindFresh owner name.value a.type
        let b ← certify next ((Resolved.freshLocalId owner s.ids, a.value) :: e)
          (by simpa only [next, LocalTypeInputs.bindFresh_ids, Resolved.LocalScope.ids, List.map_cons]
            using congrArg (List.cons _) aligned) store ⟨span, rest⟩
        let rawTail := by simpa only [next, LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using b.raw
        let common := fun elaboration raw => (⟨.letE a.core b.core, b.type, b.value, a.cost + b.cost + 2, elaboration, raw, fun k => by
          have path := Core.Steps.cons .enterLet ((a.paths (.letBody b.core e.values :: k)).trans (.cons .bindLet (b.paths k)))
          simpa only [Resolved.LocalScope.values, List.map_cons, Nat.add_assoc] using path⟩ : Certificate s e store body)
        match atAnnotation : annotation with
        | none => return (common (by rw [atBody, atAnnotation]; exact .inferred unused a.resolution a.lowered a.typing b.elaboration)
            (by rw [atBody, atAnnotation]; exact .inferred a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
        | some written =>
            match atWritten : written with
            | ⟨_, .named name none⟩ =>
                if meaning : types.lookup? (qualifiedTypeNameKey name) = some a.type then
                  return (common (by rw [atBody, atAnnotation, atWritten]; exact .binding (.named (TypeNameTable.lookup?_iff.mp meaning)) unused a.resolution a.lowered a.typing b.elaboration)
                    (by rw [atBody, atAnnotation]; exact .binding a.raw (by simpa only [LocalTypeInputs.names_ids] using rawTail)))
                else throw (IO.userError "written annotation disagrees")
            | _ => throw (IO.userError "outside independent annotation script")
      else throw (IO.userError "written name is already used")
  | ⟨_, [⟨_, .ifThen guard yes (some no)⟩]⟩ =>
      let c ← expression s e aligned store guard
      let a ← certify s e aligned store yes; let b ← certify s e aligned store no
      if ct : c.type = .bool then
        if bt : b.type = a.type then
        have elaboration : TypedLetReturnTreeElaborates types owner s body (.ifE c.core a.core b.core) a.type := by
          rw [atBody]; exact .conditional c.resolution c.lowered (ct ▸ c.typing) a.elaboration (bt ▸ b.elaboration)
        match cv : c.value with
        | .bool true => return ⟨.ifE c.core a.core b.core, a.type, a.value, c.cost + a.cost + 2, elaboration,
            by rw [atBody]; exact .ifTrue (cv ▸ c.raw) a.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseTrue (a.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | .bool false => return ⟨.ifE c.core a.core b.core, a.type, b.value, c.cost + b.cost + 2, elaboration,
            by rw [atBody]; exact .ifFalse (cv ▸ c.raw) b.raw, fun k => by
              have path := Core.Steps.cons .enterIf ((cv ▸ c.paths (.ifBranches a.core b.core e.values :: k)).trans (.cons .chooseFalse (b.paths k)))
              simpa only [Nat.add_assoc] using path⟩
        | _ => throw (IO.userError "actual guard not Bool")
        else throw (IO.userError "arm types differ")
      else throw (IO.userError "guard type not Bool")
  | _ => throw (IO.userError "outside independent body script")
termination_by sizeOf body
private structure Actual where
  type : Core.Ty
  value : Core.Value
  typed : Core.ValueHasType value type
private def supplied (a : Actual) (choice : Bool) : LocalInputs := ⟨[
  ⟨"c", ⟨other, 999⟩, .bool, .bool choice, .bool⟩, ⟨"r", id 2, .word, w 2, .word⟩,
  ⟨"x", id 7, a.type, a.value, a.typed⟩, ⟨"x", id 3, .bool, .bool false, .bool⟩], by
    change ([⟨other, 999⟩, id 2, id 7, id 3] : List Resolved.LocalId).Nodup; decide⟩
private def checked (content : String) (a : Actual) (choice : Bool) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let body ← parsed content; let actual := supplied a choice
  let s := actual.toTypeInputs; let e := actual.environment
  have _ : s = inputs a.type := rfl
  check (decide (e = env a.value choice ∧ actual.bindings.length = 4)) "original supplied rows changed"
  for store in stores do
    let cert ← certify s e rfl store body
    check (decide (cert.core = core ∧ cert.type = type ∧ cert.value = value ∧ cert.cost = cost)) "independent expectations changed"
    let accepted := cert.elaboration.complete
    match atShape : body with
    | ⟨_, ⟨_, .expression _ true⟩ :: _⟩ =>
        have _ := elaborateTypedLetReturnTree?_discard_children (by rw [← atShape]; exact accepted)
        pure ()
    | _ => pure ()
    check (decide (actual.checkTypedLetReturnTree? types owner body = some (core, type) ∧
      evaluateTypedLetReturnTreeWithCost? owner s.names e body = some (value, cost) ∧
      Core.infer? s.context.values core = some type ∧ typedLetReturnTreeFuelBound body = bound ∧ cost ≤ bound))
      "independent Core/type/value/cost/bound disagreed with the public APIs"
    check ((elaborateTypedLetReturnBody? types owner s body).isNone) "old prefix adapter widened"
    let start := Core.State.initial cert.core e.values store
    let run := fun fuel => actual.runTypedLetReturnTree? types owner fuel body store
    for k in [[], [.letBody (.var 0) [w 17]], [.unaryApply .wordNot]] do
      have _ := cert.paths k
      have _ := cert.raw.checked_toStepsWithContinuation accepted rfl k
      pure ()
    for fuel in List.range (bound + 3) do
      check (decide (run fuel = some (type, Core.runStateful fuel start))) "body wrapper changed the full machine result"
      check (match run fuel with
        | some (_, .done v st) => decide (cost ≤ fuel ∧ v = value ∧ st = store)
        | some (_, .outOfFuel cp) => decide (fuel < cost ∧ cp.store = store)
        | _ => false) "exact threshold or own store changed"
    for spent in List.range cost do
      match exhausted : run spent with
      | some (_, .outOfFuel cp) =>
          have _ := actual.runTypedLetReturnTree?_resume exhausted (cost - spent)
          for remaining in [0, 1, cost - spent, cost - spent + 2] do
            check (decide (run (spent + remaining) = some (type, Core.runStateful remaining cp))) "genuine checkpoint replay changed"
          check (decide (Core.runStateful (cost - spent) cp = .done value store)) "exact residual cost changed"
          if cost - spent > 1 then
            let .outOfFuel next := Core.runStateful 1 cp | throw (IO.userError "second chunk missing")
            check (decide (Core.runStateful (cost - spent - 1) next = .done value store)) "third chunk lost its continuation"
          if spent > 0 then check (Core.runStateful (cost - spent) start != .done value store) "restart impersonated resume"
      | _ => throw (IO.userError "checkpoint missing")
private def spine : Nat → String × Core.Expr
  | 0 => ("return x;", .var 2)
  | n + 1 => let (tail, core) := spine n; ("x;" ++ tail, .letE (.var 2) (core.weakenAt 0))
private def nominal (body : Syntax.Block) : IO Unit := do
  match atBody : body with
  | ⟨_, [⟨_, .expression ⟨_, .identifier name⟩ true⟩, ⟨_, .returnStmt (some ⟨_, .identifier result⟩)⟩]⟩ =>
      if hn : name.value = "x" then
        if hr : result.value = "x" then
          for type in [Core.Ty.namedData ⟨99⟩, .product (.namedData ⟨99⟩) (.cell (.namedData ⟨13⟩))] do
            have named : LocalNameTable.Lookup (inputs type).names "x" (id 7) :=
              .tail (by decide) (.tail (by decide) .head)
            have typed : Resolved.HasType (inputs type).context (.var (id 7)) type :=
              .var (.tail (by decide) (.tail (by decide) .head))
            have lowered : Resolved.Lowers (inputs type).ids (.var (id 7)) (.var 2) :=
              .var (.tail (by decide) (.tail (by decide) .head))
            have evidence : TypedLetReturnTreeElaborates types owner (inputs type) body (.letE (.var 2) (.var 3)) type := by
              rw [atBody]; simpa [Core.Expr.weakenAt] using
                (TypedLetReturnTreeElaborates.discard (types := types) (owner := owner)
                  (.identifier (hn ▸ named)) lowered typed (.single (.expression (.identifier (hr ▸ named)) lowered typed)))
            have _ (definitions : Core.DataEnvironment) :
                Core.HasType (inputs type).context.values (.letE (.var 2) (.var 3)) type definitions :=
              .letE (.var rfl) (.var rfl)
            have _ : ¬ TypedLetReturnTreeElaborates types owner (inputs type) body (.var 2) type := by
              intro wrong; have impossible := evidence.result_unique wrong; cases impossible.1
            check (decide (elaborateTypedLetReturnTree? types owner (inputs type) body =
              some (.letE (.var 2) (.var 3), type))) "value-free nominal discard changed"
        else throw (IO.userError "return spelling changed")
      else throw (IO.userError "discard spelling changed")
  | _ => throw (IO.userError "original nominal body shape changed")
end DiscardStatements
open DiscardStatements
def frontendParsedDiscardStatementTests : IO Unit := do
  let wordActual : Actual := ⟨.word, w 9, .word⟩
  for depth in [1, 2, 5, 15] do
    let (content, core) := spine depth
    checked ("{" ++ content ++ "}") wordActual true core .word (w 9) (3 * depth + 1) (3 * depth + 1)
  checked "{x - r;return r;}" wordActual true (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) .word (w 2) 8 8
  checked "{(x,r);return x;}" wordActual true (.letE (.pair (.var 2) (.var 1)) (.var 3)) .word (w 9) 8 8
  checked "{();return ();}" wordActual false (.letE .unit .unit) .unit .unit 4 4
  checked "{x;let z=x - r;z;let q: Word=z;return q;}" wordActual true
    (.letE (.var 2) (.letE (.binary .wordSub (.var 3) (.var 2)) (.letE (.var 0) (.letE (.var 1) (.var 0))))) .word (w 7) 17 17
  for choice in [false, true] do
    checked "{if(c){x - r;return x;}else{return r;}}" wordActual choice
      (.ifE (.var 0) (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 3)) (.var 1))
      .word (if choice then w 9 else w 2) (if choice then 11 else 4) 11
  for a in [⟨.cell .word, .cellRef .word 999, .cellRef⟩,
      ⟨.function .word .word, .closure .word .word (.var 1) [w 7], .closure (.cons .word .nil) (.var rfl)⟩,
      ⟨.unit, .unit, .unit⟩, ⟨.product .unit (.cell .word), .pair .unit (.cellRef .word 19), .pair .unit .cellRef⟩] do
    checked "{x;return x;}" a true (.letE (.var 2) (.var 3)) a.type a.value 4 4
  let body ← parsed "{x;return x;}"; nominal body
  match body.value with
  | [⟨statementSpan, .expression source true⟩, returned] =>
      check (decide (statementSpan.startByte = 1 ∧ statementSpan.endByte = 3 ∧
        source.span.startByte = 1 ∧ source.span.endByte = 2 ∧ returned.span.startByte = 3))
        "original expression/semicolon/tail byte positions changed"
  | _ => throw (IO.userError "original strict statement shape changed")
  check (decide (Resolved.freshLocalId owner (inputs .word).ids = DiscardStatements.id 8)) "discard introduced a source identity"
  for store in stores do
    let e := (supplied wordActual true).environment.values
    let start := Core.State.initial (.letE (.binary .wordSub (.var 2) (.var 1)) (.var 2)) e store
    let cp : Core.State := ⟨.ret (w 7), [.letBody (.var 2) e], store⟩
    check (decide (Core.runStateful 6 start = .outOfFuel cp ∧
      Core.runStateful 7 start = .outOfFuel ⟨.eval (.var 2) (w 7 :: e), [], store⟩ ∧
      Core.runStateful 2 cp = .done (w 2) store ∧
      Core.runStateful 0 { cp with continuation := [] } = .done (w 7) store)) "discard's actual hidden value/frame was erased"
  for content in ["{x}", "{x;}", "{missing;return x;}", "{~c;return x;}", "{f(x);return x;}",
      "{x=r;return x;}", "{return x;x;}", "{x;let x=r;return x;}", "{x;let z: Unknown=x;return z;}"] do
    let rejected ← parsed content
    check ((elaborateTypedLetReturnTree? types owner (inputs .word) rejected).isNone) "unsupported or invalid statement accepted"
  for content in ["{missing;return x;}", "{~c;return x;}", "{f(x);return x;}"] do
    check ((evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) (← parsed content)).isNone)
      "an unused invalid expression was skipped by raw execution"
  let skipped ← parsed "{if(c){x;return x;}else{missing;return x;}}"
  check (decide (evaluateTypedLetReturnTreeWithCost? owner (inputs .word).names (env (w 9) true) skipped = some (w 9, 7) ∧
    elaborateTypedLetReturnTree? types owner (inputs .word) skipped = none)) "raw selected path bypassed whole checking"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedConditionalReturnBodies
/-! A fully parsed terminal statement conditional uses its separate body API
and the integrated runtime entry. Actual typed parameters and returned
cells/closures are retained; the original singleton adapter stays narrow. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ConditionalReturnBody", by decide⟩], by decide⟩⟩, 27⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def store : Core.Store := [.word (word 91), .bool true]
private def types : TypeNameTable := [(["Bool"], .bool), (["Word"], .word), (["Unit"], .unit),
  (["Cell"], .cell .word), (["Fn"], .function .bool .bool)]
private def arguments (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word (word 7), .word⟩, ⟨.word, .word (word 9), .word⟩]
private def lt (left right : Core.Expr) : Core.Expr :=
  .letE left (.letE (right.weakenAt 0) (.binary .wordGt (.var 0) (.var 1)))

private def parsed? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-conditional-return.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")
private def body (content : String) : IO Syntax.Block := do
  let some result ← parsed? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected complete diagnostic-free block")
  return result

private def checkBody (inputs : LocalInputs) (source : Syntax.Block) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  assertTrue (decide (inputs.checkConditionalReturnBody? source = some (core, type)))
    s!"wrong exact Core/body type: expected {reprStr (core, type)}, observed {reprStr (inputs.checkConditionalReturnBody? source)}"
  assertTrue (conditionalReturnBodyFuelBound source == bound) "wrong maximum-arm source bound"
  assertTrue (inputs.checkReturnBody? source).isNone "old singleton checker accepted statement conditional"
  let initial := Core.State.initial core inputs.environment.values store
  let run := fun fuel => inputs.runConditionalReturnBody? fuel source store
  for fuel in List.range (bound + 3) do
    assertTrue (decide (run fuel = some (type, Core.runStateful fuel initial))) "full checked Core result changed"
    assertTrue (inputs.runReturnBody? fuel source store).isNone "old singleton runner accepted conditional"
    assertTrue (match run fuel with
      | some (actualType, .done actualValue finalStore) =>
          decide (cost ≤ fuel ∧ actualType = type ∧ actualValue = value ∧ finalStore = store)
      | some (actualType, .outOfFuel state) => decide (fuel < cost ∧ actualType = type ∧ state.store = store)
      | _ => false) "wrong exact completion threshold, value, type, or store"
  for spent in List.range cost do
    let some (_, .outOfFuel checkpoint) := run spent | throw (IO.userError "genuine checkpoint disappeared")
    for remaining in List.range (cost - spent + 3) do
      assertTrue (decide (run (spent + remaining) = some (type, Core.runStateful remaining checkpoint)))
        "same-state resumption changed a frame/environment or the full result"
  match source.value, core with
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩], .ifE conditionCore thenCore elseCore =>
      assertTrue (decide (inputs.check? condition = some (conditionCore, .bool) ∧
        inputs.checkReturnBody? thenBody = some (thenCore, type) ∧
        inputs.checkReturnBody? elseBody = some (elseCore, type))) "condition or arm moved out of original inputs"
      assertTrue (source.span.contains statementSpan && statementSpan.contains condition.span &&
        statementSpan.contains thenBody.span && statementSpan.contains elseBody.span &&
        decide (condition.span.endByte ≤ thenBody.span.startByte ∧ thenBody.span.endByte ≤ elseBody.span.startByte))
        "canonical spans or written branch order changed"
      let first : Core.State := ⟨.eval conditionCore inputs.environment.values,
        [.ifBranches thenCore elseCore inputs.environment.values], store⟩
      assertTrue (decide (run 1 = some (type, .outOfFuel first))) "initial conditional frame was discarded"
  | _, _ => throw (IO.userError "accepted something other than one explicit if/else")
private def checkText (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  checkBody inputs (← body content) core type value cost bound

private def checkEntry (content : String) (supplied : List TypedRuntimeArgument) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost bound : Nat) : IO Unit := do
  let some declaration ← parsed? (Syntax.Parser.functionDecl .module) content
    | throw (IO.userError "complete declaration did not parse")
  let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements supplied
    | throw (IO.userError "actual declaration arguments did not bind")
  assertTrue (decide (inputs.environment.values = supplied.reverse.map (·.value))) "actual argument order changed"
  checkBody inputs declaration.value.body core type value cost bound
  match accepted : compileRuntimeFunction? types owner declaration with
  | none => throw (IO.userError "terminal statement entry did not compile")
  | some compiled =>
      let provenance := compileRuntimeFunction?_sound accepted
      let some prepared := prepareRuntimeFunction? types owner declaration supplied
        | throw (IO.userError "actual conditional arguments did not prepare")
      assertTrue (decide (compiled.core = core ∧ compiled.returnType = type ∧ prepared.core = core ∧
        prepared.returnType = type ∧ prepared.inputs.environment.values = supplied.reverse.map (·.value)))
        "conditional entry changed the actual compilation or input projection"
      if matching : supplied.map (·.type) = compiled.inputs.context.values.reverse then
        for fuel in List.range (bound + 3) do
          have _ := provenance.run_eq supplied matching fuel store
          assertTrue (decide (runRuntimeFunction? types owner declaration supplied fuel store =
            inputs.runConditionalReturnBody? fuel declaration.value.body store)) "entry charged extra body steps"
      else throw (IO.userError "conditional entry changed ordered argument types")

private theorem selectedPiecesEvaluate (inputs : LocalInputs) (blockSpan statementSpan : Syntax.SourceSpan)
    (condition : Syntax.Expr) (thenBody elseBody : Syntax.Block) (choice : Bool) (type : Core.Ty) (value : Core.Value)
    (conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store))
    (branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (type, .done value store)) :
    ConditionalReturnBodyEvaluates inputs.names inputs.environment store
      ⟨blockSpan, [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩]⟩ value store := by
  obtain ⟨_, _, conditionCosted, _⟩ := LocalInputs.run?_done_iff_typed_cost.mp conditionDone
  cases choice with
  | false =>
      change inputs.runReturnBody? 40 elseBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .ifFalse conditionCosted.erase branchCosted.erase
  | true =>
      change inputs.runReturnBody? 40 thenBody store = some (type, .done value store) at branchDone
      obtain ⟨_, _, branchCosted, _⟩ := LocalInputs.runReturnBody?_done_iff_typed_cost.mp branchDone
      exact .ifTrue conditionCosted.erase branchCosted.erase

private def checkSkipped (inputs : LocalInputs) (choice : Bool) (invalid : String) : IO Unit := do
  let content := if choice then "{ if(c) { return t; } else { return " ++ invalid ++ "; } }"
    else "{ if(c) { return " ++ invalid ++ "; } else { return f; } }"
  let source ← body content
  assertTrue (inputs.checkConditionalReturnBody? source).isNone "invalid unselected arm checked"
  for fuel in [0, 4, conditionalReturnBodyFuelBound source, 40] do
    assertTrue (inputs.runConditionalReturnBody? fuel source store).isNone "numeric bound bypassed whole-arm rejection"
  match source.value with
  | [⟨statementSpan, .ifThen condition thenBody (some elseBody)⟩] =>
      let expected := Core.Value.word (word (if choice then 7 else 9))
      if conditionDone : inputs.run? 40 condition store = some (.bool, .done (.bool choice) store) then
        if branchDone : inputs.runReturnBody? 40 (if choice then thenBody else elseBody) store = some (.word, .done expected store) then
          have _ := selectedPiecesEvaluate inputs source.span statementSpan condition thenBody elseBody
            choice .word expected conditionDone branchDone
          pure ()
        else throw (IO.userError "selected valid arm did not independently execute")
      else throw (IO.userError "actual condition selected the wrong branch")
  | _ => throw (IO.userError "skipped-arm fixture lost its canonical conditional")

private def checkRejected (inputs : LocalInputs) (content : String) (zeroShapeBound : Bool) : IO Unit := do
  let source ← body content
  assertTrue (inputs.checkConditionalReturnBody? source).isNone s!"{content}: unsupported body checked"
  if zeroShapeBound then assertTrue (conditionalReturnBodyFuelBound source == 0) "unsupported outer shape gained a bound"
  for fuel in [0, 1, 4, 13, conditionalReturnBodyFuelBound source, 50] do
    assertTrue (inputs.runConditionalReturnBody? fuel source store).isNone "structural/type rejection depended on fuel"

def frontendParsedConditionalReturnBodiesTests : IO Unit := do
  for choice in [false, true] do
    let some declaration ← parsed? (Syntax.Parser.functionDecl .module)
      "function parameters(c: Bool, t: Word, f: Word) returns (Word) { return t; }"
      | throw (IO.userError "actual parameter declaration did not parse")
    let some inputs := bindRuntimeParameters? types owner declaration.value.signature.parameters.elements (arguments choice)
      | throw (IO.userError "typed Word parameters did not bind")
    let simple := Core.Expr.ifE (.var 2) (.var 1) (.var 0)
    let simpleBody ← body "{ if(c){return t;}else{return f;} }"
    let pending : Core.State := ⟨.ret (.bool choice), [.ifBranches (.var 1) (.var 0) inputs.environment.values], store⟩
    assertTrue (decide (inputs.runConditionalReturnBody? 2 simpleBody store = some (.word, .outOfFuel pending) ∧
      Core.runStateful 0 pending = .outOfFuel pending ∧
      Core.runStateful 1 pending = .outOfFuel ⟨.eval (if choice then .var 1 else .var 0) inputs.environment.values, [], store⟩ ∧
      Core.runStateful 0 { pending with continuation := [] } = .done (.bool choice) store))
      "pending conditional selection or dropped-frame counterexample changed"
    checkText inputs " /* lead */ { if /* guard */ (c) { return ((t)); } else { return f; } }"
      simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkEntry "function choose(c: Bool, t: Word, f: Word) returns (Word) { if(c){return t;}else{return f;} }"
      (arguments choice) simple .word (.word (word (if choice then 7 else 9))) 4 4
    checkText inputs "{ if(c){return t * f + t;}else{return f;} }"
      (.ifE (.var 2) (.binary .wordAdd (.binary .wordMul (.var 1) (.var 0)) (.var 1)) (.var 0))
      .word (.word (word (if choice then 70 else 9))) (if choice then 12 else 4) 12
    checkText inputs "{ if(c){return t < f;}else{return t >= f;} }"
      (.ifE (.var 2) (lt (.var 1) (.var 0)) (.unary .boolNot (lt (.var 1) (.var 0))))
      .bool (.bool choice) (if choice then 14 else 16) 16
    checkText inputs "{ if(c && t < f){return t + f;}else{return f;} }"
      (.ifE (.ifE (.var 2) (lt (.var 1) (.var 0)) (.bool false)) (.binary .wordAdd (.var 1) (.var 0)) (.var 0))
      .word (.word (word (if choice then 16 else 9))) (if choice then 21 else 7) 21
    checkText inputs "{ if(c){return c ? t - f : f;}else{return c ? t : f;} }"
      (.ifE (.var 2) (.ifE (.var 2) (.binary .wordSub (.var 1) (.var 0)) (.var 0))
        (.ifE (.var 2) (.var 1) (.var 0))) .word
      (.word (if choice then (word 7).sub (word 9) else word 9)) (if choice then 11 else 7) 11
    for invalid in ["missing", "c", "t + c", "t(c)", s!"{Core.wordModulus}"] do
      checkSkipped inputs choice invalid
    for content in ["{}", "{ return; }", "{ return t; }", "{ if(c){return t;} }",
        "{ t; if(c){return t;}else{return f;} }", "{ if(c){return t;}else{return f;} return t; }",
        "{ if(c){return t;}else{return f;} if(c){return f;}else{return t;} }",
        "{ { if(c){return t;}else{return f;} } }"] do checkRejected inputs content true
    for content in ["{ if(t){return t;}else{return f;} }", "{ if(missing){return t;}else{return f;} }",
        "{ if(c){return t;}else{return c;} }", "{ if(c){return;}else{return t;} }",
        "{ if(c){}else{return f;} }", "{ if(c){return t;}else{} }",
        "{ if(c){t; return t;}else{return f;} }", "{ if(c){return t; f;}else{return f;} }",
        "{ if(c){return t; return f;}else{return f;} }", "{ if(c){return t;}else{return f; t;} }",
        "{ if(c){if(c){return t;}else{return f;}}else{return f;} }",
        "{ if(c){return t;}else{if(c){return t;}else{return f;}} }",
        "{ if(c){return t;}else{while(c){return f;}} }"] do checkRejected inputs content false
    checkText inputs "{ if(c){return;}else{return;} }" (.ifE (.var 2) .unit .unit) .unit .unit 4 4
  checkText LocalInputs.empty "{ if(0 < 1){return;}else{return;} }"
    (.ifE (lt (.word (word 0)) (.word (word 1))) .unit .unit) .unit .unit 14 14
  let unit : TypedRuntimeArgument := ⟨.unit, .unit, .unit⟩
  let cellLeft : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 40, .cellRef⟩
  let cellRight : TypedRuntimeArgument := ⟨.cell .word, .cellRef .word 91, .cellRef⟩
  let closureLeft : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 0) [], .closure .nil (.var rfl)⟩
  let closureRight : TypedRuntimeArgument :=
    ⟨.function .bool .bool, .closure .bool .bool (.var 1) [.bool true], .closure (.cons .bool .nil) (.var rfl)⟩
  for (name, left, right) in [("Unit", unit, unit), ("Cell", cellLeft, cellRight), ("Fn", closureLeft, closureRight),
      ("Bool", (⟨.bool, .bool true, .bool⟩ : TypedRuntimeArgument), ⟨.bool, .bool false, .bool⟩)] do
    for choice in [false, true] do
      checkEntry (s!"function values(c: Bool, t: {name}, f: {name}) returns ({name})" ++
        " { if(c){return t;}else{return f;} }") [⟨.bool, .bool choice, .bool⟩, left, right]
        (.ifE (.var 2) (.var 1) (.var 0)) left.type (if choice then left.value else right.value) 4 4
      checkEntry "function units(c: Bool, u: Unit) returns (Unit) { if(c){return;}else{return u;} }"
        [⟨.bool, .bool choice, .bool⟩, unit] (.ifE (.var 1) .unit (.var 0)) .unit .unit 4 4
  for content in ["", "if(c){return t;}else{return f;}", "{ if(c){return t;}else{return f;} ",
      "{ if(c){return t}else{return f;} }", "{ if(c){return t;}else }", "{ if(c){return t;}else{return f;} } trailing"] do
    assertTrue (← parsed? (Syntax.Parser.block .allow) content).isNone "malformed or incompletely consumed block accepted"
  assertTrue (← parsed? (Syntax.Parser.functionDecl .module)
    "function trailing(c: Bool) returns (Unit) { if(c){return;}else{return;} } trailing").isNone
    "function helper accepted only a valid prefix"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedReturnBodies
/-! Actual singleton return bodies retain the checked expression's Core and
fuel behavior. Parsed declarations supply parameters and body separately; this
test does not interpret a signature contract or invoke a source function. -/

set_option autoImplicit false

namespace Tests

open Solcore Solcore.Frontend

private def parsed_variant? {α : Type} (parser : Syntax.Parser.Parser α) (content : String) : IO (Option α) := do
  let file : Syntax.SourceFile := { id := ⟨.main, "parsed-return-body.sol"⟩, content }
  let lexed ← match Syntax.Lexer.lex file with
    | .ok lexed => pure lexed
    | .error error => throw (IO.userError s!"{content}: lexer invariant {reprStr error}")
  if !lexed.diagnostics.isEmpty then return none
  match parser (Syntax.Parser.State.initial file lexed) with
  | .ok source next =>
      if !next.atEnd || !next.diagnostics.isEmpty then return none
      return some source
  | .reject _ _ => return none
  | .invariant error => throw (IO.userError s!"{content}: parser invariant {reprStr error}")

private def owner_variant : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"ReturnBody", by decide⟩], by decide⟩⟩, 0⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def nine : Core.Word := ⟨9, by decide⟩
private def store_variant : Core.Store := [.word nine, .bool true]
private def types_variant : TypeNameTable := [(["Bool"], .bool), (["Word"], .word)]
private def arguments_variant (choice : Bool) : List TypedRuntimeArgument :=
  [⟨.bool, .bool choice, .bool⟩, ⟨.word, .word seven, .word⟩, ⟨.word, .word nine, .word⟩]

private def checkBody_variant (inputs : LocalInputs) (body : Syntax.Block) (label : String)
    (expectedCore : Core.Expr) (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let checked := inputs.checkReturnBody? body
  assertTrue (decide (checked = some (expectedCore, type))) s!"{label}: wrong body Core or type"
  let some (actualCore, _) := checked
    | throw (IO.userError s!"{label}: body checking failed")
  assertTrue (decide (inputs.runReturnBody? 0 body store_variant =
    some (type, .outOfFuel (Core.State.initial actualCore inputs.environment.values store_variant))))
    s!"{label}: wrong zero-fuel initial state"
  for fuel in [0, cost - 1] do
    match inputs.runReturnBody? fuel body store_variant with
    | some (actualType, .outOfFuel _) =>
        assertTrue (decide (actualType = type)) s!"{label}: exhaustion changed the type"
    | _ => throw (IO.userError s!"{label}: body did not exhaust below its cost")
  for fuel in [cost, cost + 5] do
    assertTrue (decide (inputs.runReturnBody? fuel body store_variant = some (type, .done value store_variant)))
      s!"{label}: wrong returned value, preserved store, or completion threshold"
  match body.value with
  | [⟨_, .returnStmt (some expression)⟩] =>
      assertTrue (decide (checked = inputs.check? expression))
        s!"{label}: return changed the exact expression Core"
      for fuel in [0, 1, 3, 4, 5, 6, 8, cost, cost + 5] do
        assertTrue (decide (inputs.runReturnBody? fuel body store_variant = inputs.run? fuel expression store_variant))
          s!"{label}: return introduced execution overhead or altered a suspended state"
  | [⟨_, .returnStmt none⟩] => pure ()
  | _ => throw (IO.userError s!"{label}: accepted a non-singleton return body")
  let invalidSpan : Syntax.SourceSpan := ⟨⟨.main, "unrelated.sol"⟩, 900, 2⟩
  let moved : Syntax.Block := ⟨invalidSpan, body.value.map fun statement =>
    { statement with span := invalidSpan }⟩
  assertTrue (decide (inputs.checkReturnBody? moved = checked))
    s!"{label}: block or statement range changed body checking"

private def checkText_variant (inputs : LocalInputs) (content : String) (core : Core.Expr)
    (type : Core.Ty) (value : Core.Value) (cost : Nat) : IO Unit := do
  let some body ← parsed_variant? (Syntax.Parser.block .allow) content
    | throw (IO.userError s!"{content}: expected a complete body")
  checkBody_variant inputs body content core type value cost

def frontendParsedReturnBodyTests : IO Unit := do
  checkText_variant LocalInputs.empty "{ return; }" .unit .unit .unit 1
  checkText_variant LocalInputs.empty " /* lead */ { /* inside */ return /* unit */ ; } " .unit .unit .unit 1
  checkText_variant LocalInputs.empty "{ return ((0007)); }" (.word seven) .word (.word seven) 1
  checkText_variant LocalInputs.empty "{ return ~7; }" (.unary .wordNot (.word seven)) .word (.word seven.bitNot) 3
  let some mismatched ← parsed_variant? (Syntax.Parser.functionDecl .module)
      "function mismatch() returns (Bool) { return 7; }"
    | throw (IO.userError "signature mismatch example should parse")
  let some returns := mismatched.value.signature.returnsClause
    | throw (IO.userError "explicit return annotation disappeared")
  let [annotation] := returns.types.elements
    | throw (IO.userError "expected one declared return type")
  assertTrue (decide (interpretTypeName? types_variant annotation = some .bool))
    "mismatch example must declare Bool independently of its Word body"
  checkBody_variant LocalInputs.empty mismatched.value.body "body type is not signature checking"
    (.word seven) .word (.word seven) 1
  for choice in [false, true] do
    let some declaration ← parsed_variant? (Syntax.Parser.functionDecl .module)
        "function choose(c: Bool, t: Word, f: Word) returns (Word) { return c ? t : f; }"
      | throw (IO.userError "complete declaration parsing failed")
    let some inputs := bindRuntimeParameters? types_variant owner_variant declaration.value.signature.parameters.elements (arguments_variant choice)
      | throw (IO.userError "actual declaration parameters failed to bind")
    checkBody_variant inputs declaration.value.body "actual declaration body"
      (.ifE (.var 2) (.var 1) (.var 0)) .word (.word (if choice then seven else nine)) 4
    checkText_variant inputs "{ return; }" .unit .unit .unit 1
    checkText_variant inputs "{ return c ? ~t : f; }"
      (.ifE (.var 2) (.unary .wordNot (.var 1)) (.var 0)) .word
      (.word (if choice then seven.bitNot else nine)) (if choice then 6 else 4)
    checkText_variant inputs "{ return c && !c; }"
      (.ifE (.var 2) (.unary .boolNot (.var 2)) (.bool false)) .bool (.bool false)
      (if choice then 6 else 4)
    checkText_variant inputs "{ return t ^ f; }" (.binary .wordXor (.var 1) (.var 0)) .word (.word (seven.bitXor nine)) 5
    checkText_variant inputs "{ return t + f; }" (.binary .wordAdd (.var 1) (.var 0)) .word (.word (seven.add nine)) 5
    checkText_variant inputs "{ return t - f; }" (.binary .wordSub (.var 1) (.var 0)) .word (.word (seven.sub nine)) 5
    checkText_variant inputs "{ return t * f; }" (.binary .wordMul (.var 1) (.var 0)) .word (.word (seven.mul nine)) 5
    for content in ["{}", "{ t; }", "{ t }", "{ { return t; } }", "{ return t; return f; }",
        "{ t; return f; }", "{ return t; missing; }", "{ let x = t; return x; }",
        "{ return c ? t : missing; }", "{ return c ? t : c; }", "{ return t(c); }",
        "{ return \"7\"; }"] do
      let some body ← parsed_variant? (Syntax.Parser.block .allow) content
        | throw (IO.userError s!"{content}: unsupported body should still parse")
      assertTrue (inputs.checkReturnBody? body).isNone s!"{content}: unsupported body or expression checked"
      for fuel in [0, 4, 20] do
        assertTrue (inputs.runReturnBody? fuel body store_variant).isNone
          s!"{content}: dropped written syntax or bypassed body checking"
  for content in ["", "return;", "{ return;", "{ return 7 }", "{ return; } trailing"] do
    assertTrue (← parsed_variant? (Syntax.Parser.block .allow) content).isNone
      s!"{content}: accepted malformed, diagnosed, or incompletely consumed body text"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendReturnBodyProperties
/-! ADR-0169: singleton return wrappers preserve the checked expression and its
independent transition count. Other statements are never silently discarded. -/

set_option autoImplicit false

namespace Tests.FrontendReturnBody

open Solcore Solcore.Frontend

private def span : Syntax.SourceSpan := ⟨⟨.main, "return-body.sol"⟩, 0, 4⟩
private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"ReturnBody", by decide⟩], by decide⟩⟩, 0⟩
private def returned (source : Option Syntax.Expr) : Syntax.Block := ⟨span, [⟨span, .returnStmt source⟩]⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def unary (op : Syntax.UnaryOp) (child : Syntax.Expr) : Syntax.Expr := ⟨span, .unary ⟨span, op⟩ child⟩
private def binary (op : Syntax.BinaryOp) (left right : Syntax.Expr) : Syntax.Expr := ⟨span, .binary left ⟨span, op⟩ right⟩
private def branch (condition left right : Syntax.Expr) : Syntax.Expr := ⟨span, .conditional condition span left span right⟩
private def seven : Core.Word := ⟨7, by decide⟩
private def literal : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "7"⟩⟩
private theorem meaning : WordLiteralDenotes ⟨span, .decimal "7"⟩ seven :=
  NumericLiteralDenotes.decimal (by decide) (.cons (.decimal (digit := 7) (by decide) (by decide)) .nil)
private def inputs (choice : Bool) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "c" .bool (.bool choice) .bool

theorem bare_return_has_unit_meaning_and_exact_zero_one_fuel_boundary
    (supplied : LocalInputs) (store : Core.Store) (blockSpan returnSpan : Syntax.SourceSpan) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt none⟩]⟩
    ReturnBodyHasType supplied.names supplied.context body .unit ∧
    ReturnBodyEvaluates supplied.names supplied.environment store body .unit store ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body .unit store 1 ∧
    supplied.checkReturnBody? body = some (.unit, .unit) ∧
    supplied.runReturnBody? 0 body store = some (.unit, .outOfFuel
      (Core.State.initial .unit (Resolved.LocalScope.values supplied.environment) store)) ∧
    supplied.runReturnBody? 1 body store = some (.unit, .done .unit store) := by
  intro body
  exact ⟨.bare, .bare, .bare, rfl, rfl, rfl⟩

theorem expression_return_retains_the_actual_checker_and_independent_child_meaning
    (supplied : LocalInputs) (source : Syntax.Expr) (type : Core.Ty)
    (value : Core.Value) (initialStore finalStore : Core.Store) (cost : Nat)
    (blockSpan returnSpan : Syntax.SourceSpan) :
    let body : Syntax.Block := ⟨blockSpan, [⟨returnSpan, .returnStmt (some source)⟩]⟩
    supplied.checkReturnBody? body = supplied.check? source ∧
    (ReturnBodyHasType supplied.names supplied.context body type ↔
      LocalExpressionHasType supplied.names supplied.context source type) ∧
    (ReturnBodyEvaluates supplied.names supplied.environment initialStore body value finalStore ↔
      LocalExpressionEvaluates supplied.names supplied.environment initialStore source value finalStore) ∧
    (ReturnBodyEvaluatesWithCost supplied.names supplied.environment initialStore body value finalStore cost ↔
      LocalExpressionEvaluatesWithCost supplied.names supplied.environment initialStore source value finalStore cost) := by
  intro body
  dsimp only [body]
  refine ⟨rfl, ⟨?_, ReturnBodyHasType.expression⟩,
    ⟨?_, ReturnBodyEvaluates.expression⟩, ⟨?_, ReturnBodyEvaluatesWithCost.expression⟩⟩
  all_goals intro derived; cases derived with | expression child => exact child

private def source : Syntax.Expr :=
  branch (binary .logicalAnd (unary .logicalNot (ref "c")) (unary .logicalNot (ref "c")))
    (unary .bitNot literal) (unary .bitNot (binary .bitOr literal literal))
private def required (choice : Bool) : Nat := if choice then 15 else 13
private abbrev Cost (choice : Bool) (store : Core.Store) (source : Syntax.Expr) (value : Core.Value) (cost : Nat) :=
  LocalExpressionEvaluatesWithCost (inputs choice).names (inputs choice).environment store source value store cost
private theorem cost_c (choice : Bool) (store : Core.Store) : Cost choice store (ref "c") (.bool choice) 1 :=
  .identifier .head .head
private theorem cost_seven (choice : Bool) (store : Core.Store) : Cost choice store literal (.word seven) 1 :=
  .wordLiteral meaning
private theorem sourceTyped (choice : Bool) : LocalExpressionHasType (inputs choice).names (inputs choice).context source .word :=
  .conditional (.logicalAnd (.logicalNot (.identifier .head .head)) (.logicalNot (.identifier .head .head)))
    (.bitNot (.wordLiteral meaning)) (.bitNot (.bitOr (.wordLiteral meaning) (.wordLiteral meaning)))
private theorem sourceCost (choice : Bool) (store : Core.Store) :
    Cost choice store source (.word seven.bitNot) (required choice) := by
  have left : Cost choice store (unary .bitNot literal) (.word seven.bitNot) 3 := .bitNot (cost_seven choice store)
  have right : Cost choice store (unary .bitNot (binary .bitOr literal literal)) (.word seven.bitNot) 7 := by
    simpa [Cost, unary, binary, Core.Word.bitOr_self] using
      (LocalExpressionEvaluatesWithCost.bitNot (.bitOr (cost_seven choice store) (cost_seven choice store)))
  cases choice
  · exact .ifTrue (.andTrue (.logicalNot (cost_c false store)) (.logicalNot (cost_c false store))) left
  · exact .ifFalse (.andFalse (.logicalNot (cost_c true store))) right

theorem returned_negation_complement_bitwise_conditional_and_short_circuit_keep_their_cost
    (choice : Bool) (store : Core.Store) (fuel : Nat) :
    ReturnBodyHasType (inputs choice).names (inputs choice).context (returned (some source)) .word ∧
    ReturnBodyEvaluatesWithCost (inputs choice).names (inputs choice).environment store
      (returned (some source)) (.word seven.bitNot) store (required choice) ∧
    ((inputs choice).runReturnBody? fuel (returned (some source)) store =
      some (.word, .done (.word seven.bitNot) store) ↔ required choice ≤ fuel) ∧
    ((∃ suspended, (inputs choice).runReturnBody? fuel (returned (some source)) store =
      some (.word, .outOfFuel suspended)) ↔ fuel < required choice) := by
  have typed : ReturnBodyHasType (inputs choice).names (inputs choice).context (returned (some source)) .word :=
    .expression (sourceTyped choice)
  have evaluated : ReturnBodyEvaluatesWithCost (inputs choice).names (inputs choice).environment store
      (returned (some source)) (.word seven.bitNot) store (required choice) := .expression (sourceCost choice store)
  obtain ⟨value, cost, other, _, boundaries⟩ := LocalInputs.returnBody_typed_cost_execution typed store
  obtain ⟨sameValue, _, sameCost⟩ := other.deterministic evaluated
  refine ⟨typed, evaluated, by simpa only [sameValue, sameCost] using (boundaries fuel).1, ?_⟩
  rw [LocalInputs.runReturnBody?_outOfFuel_iff_typed_cost]
  constructor
  · rintro ⟨_, otherValue, otherCost, otherEvaluation, short⟩
    exact (otherEvaluation.deterministic evaluated).2.2 ▸ short
  · intro short
    exact ⟨typed, .word seven.bitNot, required choice, evaluated, short⟩

private def missing : Syntax.Expr := branch (ref "c") literal (ref "missing")
theorem raw_return_of_a_skipped_missing_branch_does_not_bypass_checking
    (store : Core.Store) (fuel : Nat) :
    ReturnBodyEvaluates (inputs true).names (inputs true).environment store (returned (some missing)) (.word seven) store ∧
    ReturnBodyEvaluatesWithCost (inputs true).names (inputs true).environment store (returned (some missing)) (.word seven) store 4 ∧
    (inputs true).checkReturnBody? (returned (some missing)) = none ∧
    (inputs true).runReturnBody? fuel (returned (some missing)) store = none := by
  have counted : Cost true store missing (.word seven) 4 := .ifTrue (cost_c true store) (cost_seven true store)
  have rejected : (inputs true).checkReturnBody? (returned (some missing)) = none := by
    simp [LocalInputs.checkReturnBody?, elaborateReturnBody?, returned, elaborateLocalExpression?,
      resolveLocalExpression?, missing, branch, ref, inputs, LocalInputs.names, LocalInputs.bindFresh,
      LocalInputs.empty, LocalNameTable.lookup?]
  exact ⟨.expression counted.erase, .expression counted, rejected,
    by simp only [LocalInputs.runReturnBody?, rejected, bind, Option.bind_none]⟩

private def unsupported : List (List Syntax.Statement) :=
  [[], [⟨span, .returnStmt none⟩, ⟨span, .returnStmt none⟩],
   [⟨span, .block [⟨span, .returnStmt none⟩]⟩],
   [⟨span, .expression literal false⟩], [⟨span, .expression literal true⟩],
   [⟨span, .letDecl ⟨span, "x"⟩ none (some literal)⟩],
   [⟨span, .returnStmt (some literal)⟩, ⟨span, .expression (ref "missing") true⟩]]

theorem other_statements_are_not_dropped_even_after_return
    (supplied : LocalInputs) (statements : List Syntax.Statement) (present : statements ∈ unsupported)
    (outer : Syntax.SourceSpan) (store finalStore : Core.Store) (value : Core.Value) (type : Core.Ty) (cost fuel : Nat) :
    supplied.checkReturnBody? ⟨outer, statements⟩ = none ∧
    supplied.runReturnBody? fuel ⟨outer, statements⟩ store = none ∧
    ¬ ReturnBodyHasType supplied.names supplied.context ⟨outer, statements⟩ type ∧
    ¬ ReturnBodyEvaluates supplied.names supplied.environment store ⟨outer, statements⟩ value finalStore ∧
    ¬ ReturnBodyEvaluatesWithCost supplied.names supplied.environment store ⟨outer, statements⟩ value finalStore cost := by
  simp only [unsupported, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> intro impossible <;> cases impossible

theorem raw_cost_derivations_determine_value_store_and_positive_cost_without_checking
    (table : LocalNameTable) (environment : Resolved.Environment) (body : Syntax.Block)
    (initialStore leftStore rightStore : Core.Store) (left right : Core.Value) (leftCost rightCost : Nat)
    (first : ReturnBodyEvaluatesWithCost table environment initialStore body left leftStore leftCost)
    (second : ReturnBodyEvaluatesWithCost table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost ∧
    leftStore = initialStore ∧ 0 < leftCost ∧
    ReturnBodyEvaluates table environment initialStore body left leftStore ∧
    (ReturnBodyEvaluates table environment initialStore body right rightStore ↔
      ∃ cost, ReturnBodyEvaluatesWithCost table environment initialStore body right rightStore cost) := by
  obtain ⟨sameValue, sameStore, sameCost⟩ := first.deterministic second
  exact ⟨sameValue, sameStore, sameCost, first.store_eq, first.cost_pos, first.erase,
    returnBodyEvaluates_iff_exists_cost⟩

private def singleton (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) : LocalInputs :=
  LocalInputs.empty.bindFresh owner "item" type value typed

theorem structurally_typed_input_values_are_returned_with_one_transition
    (type : Core.Ty) (value : Core.Value) (typed : Core.ValueHasType value type) (store : Core.Store) :
    let supplied := singleton type value typed
    let body := returned (some (ref "item"))
    ReturnBodyHasType supplied.names supplied.context body type ∧
    ReturnBodyEvaluates supplied.names supplied.environment store body value store ∧
    ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body value store 1 ∧
    supplied.checkReturnBody? body = some (.var 0, type) ∧
    Core.Evaluates [value] store (.var 0) value store ∧
    supplied.runReturnBody? 1 body store = some (type, .done value store) := by
  intro supplied body
  have typing : ReturnBodyHasType supplied.names supplied.context body type := .expression (.identifier .head .head)
  have counted : ReturnBodyEvaluatesWithCost supplied.names supplied.environment store body value store 1 :=
    .expression (.identifier .head .head)
  have checked : supplied.checkReturnBody? body = some (.var 0, type) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  exact ⟨typing, counted.erase, counted, checked, .var rfl,
    LocalInputs.runReturnBody?_done_iff_typed_cost.mpr ⟨typing, 1, counted, Nat.le_refl _⟩⟩

private def closure : Core.Value := .closure .bool .bool (.var 0) []
private theorem closureTyped : Core.ValueHasType closure (.function .bool .bool) := .closure .nil (.var rfl)
theorem returning_closures_and_cell_references_neither_calls_nor_allocates
    (location : Core.Location) (store : Core.Store) :
    (singleton (.function .bool .bool) closure closureTyped).runReturnBody? 1
      (returned (some (ref "item"))) (.unit :: store) =
      some (.function .bool .bool, .done closure (.unit :: store)) ∧
    (singleton (.cell .word) (.cellRef .word location) .cellRef).runReturnBody? 1
      (returned (some (ref "item"))) [] = some (.cell .word, .done (.cellRef .word location) []) ∧
    ([] : Core.Store)[location]? = none :=
  ⟨(structurally_typed_input_values_are_returned_with_one_transition
      (.function .bool .bool) closure closureTyped (.unit :: store)).2.2.2.2.2,
    (structurally_typed_input_values_are_returned_with_one_transition
      (.cell .word) (.cellRef .word location) .cellRef []).2.2.2.2.2, by simp⟩

end Tests.FrontendReturnBody
end
