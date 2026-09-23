import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

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
