import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Safety

/-! Original grouped call spines have independent source and machine proofs.
Static types, actual tags, captures and inserted caller slots stay separate. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveLocalComputation
open Solcore Solcore.Frontend

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Recursive", by decide⟩], by decide⟩⟩, 53⟩
private def fid : Resolved.LocalId := ⟨owner, 17⟩
private def xid : Resolved.LocalId := ⟨{ owner with declarationIndex := 91 }, 999⟩
private def gid : Resolved.LocalId := ⟨owner, 2⟩
private def names : LocalNameTable := [("f", fid), ("x", xid), ("f", gid)]
private def context (a : Core.Ty) : Resolved.Context := [(xid, a), (fid, .function a a), (gid, .unit), (fid, .unit)]
private def span : Syntax.SourceSpan := ⟨⟨.main, "recursive.sol"⟩, 253, 3⟩
private def ref (s : Syntax.SourceSpan) (name : String) : Syntax.Expr := ⟨s, .identifier ⟨s, name⟩⟩
private def source (s t : Syntax.SourceSpan) : Nat → Syntax.Expr
  | 0 => ref s "x"
  | n + 1 => ⟨s, .call ⟨t, .group (ref s "f")⟩ ⟨t, [⟨s, .group (source s t n)⟩]⟩⟩
private def core : Nat → Core.Expr
  | 0 => .var 0
  | n + 1 => .apply (.var 1) (core n)
private theorem provenance (n : Nat) (a : Core.Ty) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationElaborates names (context a) (source s t n) (core n) a := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head)) (.var .head) (.var .head)
  | succ n ih =>
      exact .application (.group (.pure (.identifier .head)
        (.var (.tail (by change xid ≠ fid; decide) .head)) (.var (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
private theorem typing (n : Nat) (a : Core.Ty) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationHasType names (context a) (source s t n) a := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih => exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private def environment (m : Nat) (value : Core.Value) (captured : Core.Environment) : Resolved.Environment :=
  [(xid, value), (fid, .closure .unit .unit (delay m 0) captured), (gid, .unit), (fid, .bool false)]
private def charge (n m : Nat) : Nat := n * (3 * m + 5) + 1
private theorem bodyRaw (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (found : (value :: rest)[index]? = some value) :
    Core.Evaluates (value :: rest) store (delay m index) value store := by
  induction m generalizing index rest with
  | zero => exact .var found
  | succ m ih => exact .letE (.var rfl) (ih (index + 1) (value :: rest) (by simpa using found))
private theorem bodyPath (m index : Nat) (value : Core.Value) (rest : Core.Environment) (store : Core.Store)
    (k : List Core.Frame) (found : (value :: rest)[index]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (value :: rest), k, store⟩ ⟨.ret value, k, store⟩ := by
  induction m generalizing index rest k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (value :: rest) k (by simpa using found))))
private theorem raw (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationEvaluates names (environment m value captured) store (source s t n) value store := by
  induction n with
  | zero => exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih =>
      exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head))))
        (.group ih) (bodyRaw m 0 value captured store rfl)
private theorem counted (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store (source s t n) value store (charge n m) := by
  induction n with
  | zero =>
      simp only [charge, Nat.zero_mul, Nat.zero_add]
      exact .pure (.identifier (.tail (by change "f" ≠ "x"; decide) .head) .head)
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact .application (.group (.pure (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))) (.group ih)
        (bodyPath m 0 value captured store [] rfl)
private theorem manual (n m : Nat) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ := by
  induction n generalizing k with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n + 1) m = 1 + charge n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]
      exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) (bodyPath m 0 value captured store [] rfl)

theorem arbitrary_depth_preserves_original_spans_and_independent_evidence
    (n m : Nat) (a : Core.Ty) (value : Core.Value) (captured : Core.Environment)
    (store : Core.Store) (s t : Syntax.SourceSpan) :
    RecursiveLocalComputationElaborates names (context a) (source s t n) (core n) a ∧
    RecursiveLocalComputationHasType names (context a) (source s t n) a ∧
    RecursiveLocalComputationEvaluates names (environment m value captured) store (source s t n) value store ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source s t n) value store (charge n m) ∧
    ∀ k, Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨provenance n a s t, typing n a s t, raw n m value captured store s t,
    counted n m value captured store s t, manual n m value captured store⟩

theorem exact_static_provenance_rejects_another_same_typed_core (n : Nat) (a : Core.Ty) :
    elaborateRecursiveLocalComputation? names (context a) (source span span (n + 1)) = some (core (n + 1), a) ∧
    Core.HasType (context a).values (core (n + 1)) a ∧ Core.HasType (context a).values (.var 0) a ∧
    (∃ expected, RecursiveLocalComputationElaborates names (context a) (source span span (n + 1)) expected a) ∧
    ¬ RecursiveLocalComputationElaborates names (context a) (source span span (n + 1)) (.var 0) a := by
  have accepted := elaborateRecursiveLocalComputation?_iff.mpr (provenance (n + 1) a span span)
  refine ⟨accepted, (provenance (n + 1) a span span).core_hasType, .var rfl,
    recursiveLocalComputationHasType_iff_elaborates.mp (typing (n + 1) a span span), ?_⟩
  intro other
  have impossible := accepted.symm.trans (elaborateRecursiveLocalComputation?_iff.mpr other)
  cases impossible

theorem supplied_raw_cost_reflects_exact_core_without_runtime_typing
    (n m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    (∃ cost, RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span n) value store cost) ∧
    Core.Evaluates (environment m value captured).values store (core n) value store ∧
    (RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span n) value store (charge n m) ↔
      Core.Steps (charge n m) (.initial (core n) (environment m value captured).values store) (.final value store)) ∧
    ∀ k, Core.Steps (charge n m) ⟨.eval (core n) (environment m value captured).values, k, store⟩ ⟨.ret value, k, store⟩ :=
  ⟨recursiveLocalComputationEvaluates_iff_exists_cost.mp (raw n m value captured store span span),
    ((provenance n .word span span).evaluates_iff rfl).mp (raw n m value captured store span span),
    (provenance n .word span span).evaluatesWithCost_iff_steps rfl,
    fun k => (counted n m value captured store span span).toStepsWithContinuation (provenance n .word span span) rfl k⟩

theorem all_other_successes_have_the_independent_value_store_and_cost
    (n m : Nat) (value other : Core.Value) (captured : Core.Environment) (store final : Core.Store) (cost : Nat)
    (otherPath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store (source span span n) other final cost) :
    value = other ∧ store = final ∧ charge n m = cost :=
  (counted n m value captured store span span).deterministic otherPath

private def checkpoint (n m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) : Core.State :=
  ⟨.eval (core n) (environment m value captured).values, [.applyClosure .unit .unit (delay m 0) captured], store⟩
theorem every_fuel_observes_the_independent_exact_cost
    (n m fuel : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    (Core.runStateful fuel (.initial (core (n + 1)) (environment m value captured).values store) = .done value store ↔ charge (n + 1) m ≤ fuel) ∧
    ((∃ cp, Core.runStateful fuel (.initial (core (n + 1)) (environment m value captured).values store) = .outOfFuel cp) ↔ fuel < charge (n + 1) m) :=
  ⟨(manual (n + 1) m value captured store []).runStateful_done_iff,
    (manual (n + 1) m value captured store []).runStateful_outOfFuel_iff⟩

theorem genuine_nested_argument_checkpoint_keeps_its_residual_and_frames
    (n m additional : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    Core.runStateful 3 (.initial (core (n + 1)) (environment m value captured).values store) = .outOfFuel (checkpoint n m value captured store) ∧
    Core.Steps (charge (n + 1) m - 3) (checkpoint n m value captured store) (.final value store) ∧
    Core.runStateful additional (checkpoint n m value captured store) =
      Core.runStateful (3 + additional) (.initial (core (n + 1)) (environment m value captured).values store) := by
  have stopped : Core.runStateful 3 (.initial (core (n + 1)) (environment m value captured).values store) =
      .outOfFuel (checkpoint n m value captured store) := by cases n <;> rfl
  exact ⟨stopped, ((manual (n + 1) m value captured store []).residual_of_outOfFuel stopped).2,
    Core.runStateful_resume stopped additional⟩

theorem arbitrary_caller_insertion_has_one_manual_cost_before_all_continuations
    (n m : Nat) (value inserted : Core.Value) (captured leading suffix : Core.Environment) (store : Core.Store)
    (split : leading ++ suffix = (environment m value captured).values) :
    Core.Evaluates (leading ++ inserted :: suffix) store ((core n).weakenAt leading.length) value store ∧
    Core.Evaluates (leading ++ suffix) store (core n) value store ∧
    ∃ cost, cost = charge n m ∧ ∀ k,
      Core.Steps cost ⟨.eval (core n) (leading ++ suffix), k, store⟩ ⟨.ret value, k, store⟩ ∧
      Core.Steps cost ⟨.eval ((core n).weakenAt leading.length) (leading ++ inserted :: suffix), k, store⟩ ⟨.ret value, k, store⟩ := by
  have fragment := (provenance n .word span span).core_fragment
  have original := split ▸ Core.steps_from_initial_sound (manual n m value captured store [])
  have insertedEvaluation := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
  have recovered := (fragment.evaluates_insert_iff leading suffix inserted).mp insertedEvaluation
  obtain ⟨cost, paths⟩ := fragment.insertion_paths leading suffix inserted recovered
  exact ⟨insertedEvaluation, recovered, cost, ((paths []).1.final_unique (split ▸ manual n m value captured store [])).1, paths⟩

theorem syntactic_recursive_fragment_and_weakening_need_no_scoping (i j cutoff : Nat) :
    RecursiveLocalComputationFragment (.apply (.var i) (.apply (.var j) (.var i))) ∧
    RecursiveLocalComputationFragment ((Core.Expr.apply (.var i) (.apply (.var j) (.var i))).weakenAt cutoff) := by
  have fragment : RecursiveLocalComputationFragment (.apply (.var i) (.apply (.var j) (.var i))) :=
    .application (.pure .var) (.application (.pure .var) (.pure .var))
  exact ⟨fragment, fragment.weakenAt cutoff⟩

theorem insertion_preserves_a_pending_endpoint_not_its_safety (inserted : Core.Value) (store : Core.Store) :
    Core.Steps 11 ⟨.eval ((core 2).weakenAt 0) (inserted :: (environment 0 .unit []).values), [.unaryApply .wordNot], store⟩
      ⟨.ret .unit, [.unaryApply .wordNot], store⟩ ∧
    Core.runStateful 0 ⟨.ret .unit, [.unaryApply .wordNot], store⟩ =
      .fault (.invalidUnaryOperand .wordNot .unit) ⟨.ret .unit, [.unaryApply .wordNot], store⟩ := by
  obtain ⟨_, _, cost, rfl, paths⟩ := arbitrary_caller_insertion_has_one_manual_cost_before_all_continuations
    2 0 .unit inserted [] [] (environment 0 .unit []).values store rfl
  exact ⟨(paths _).2, rfl⟩

theorem pure_and_recursive_group_derivations_reconcile_the_same_actual_cost
    (m : Nat) (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 ∧
    ∀ other final cost, RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ other final cost → other = value ∧ final = store ∧ cost = 1 := by
  have purePath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 := .pure (.group (.identifier (.tail (by decide) .head) .head))
  have recursivePath : RecursiveLocalComputationEvaluatesWithCost names (environment m value captured)
      store ⟨span, .group (ref span "x")⟩ value store 1 := .group (.pure (.identifier (.tail (by decide) .head) .head))
  exact ⟨purePath, fun _ _ _ alternative => alternative.deterministic recursivePath⟩

theorem old_successes_embed_but_old_nested_call_rejection_remains (a : Core.Ty) (m : Nat)
    (value : Core.Value) (captured : Core.Environment) (store : Core.Store) :
    RecursiveLocalComputationElaborates names (context a) (source span span 1) (core 1) a ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment m value captured) store (source span span 1) value store (charge 1 m) ∧
    elaborateLocalComputation? names (context a) (source span span 2) = none := by
  have old : LocalComputationElaborates names (context a) (source span span 1) (core 1) a :=
    .application (.call (.group (.identifier .head)) (.var (.tail (by change xid ≠ fid; decide) .head))
      (.var (.tail (by change xid ≠ fid; decide) .head)) (.group (.identifier (.tail (by decide) .head))) (.var .head) (.var .head))
  have oldCost : LocalComputationEvaluatesWithCost names (environment m value captured)
      store (source span span 1) value store (charge 1 m) := by
    have count : charge 1 m = 1 + 1 + (3 * m + 1) + 3 := by simp [charge]; omega
    rw [count]
    exact .application (.call (.group (.identifier .head (.tail (by change xid ≠ fid; decide) .head)))
      (.group (.identifier (.tail (by decide) .head) .head)) (bodyPath m 0 value captured store [] rfl))
  refine ⟨old.toRecursiveLocalComputation, oldCost.toRecursiveLocalComputation, ?_⟩
  simp [elaborateLocalComputation?, elaborateLocalFunctionApplication?, source, elaborateLocalExpression?, resolveLocalExpression?]

private def computed : Syntax.Expr := ⟨span, .call (source span span 1) ⟨span, [⟨span, .tuple ⟨span, []⟩⟩]⟩⟩
theorem a_computed_callee_invokes_its_literal_captured_body (captured : Core.Value) (store : Core.Store) :
    let returned := Core.Value.closure .unit .unit (.var 1) [captured]
    RecursiveLocalComputationElaborates names (context (.function .unit .unit)) computed (.apply (core 1) .unit) .unit ∧
    RecursiveLocalComputationEvaluatesWithCost names (environment 0 returned []) store computed captured store 11 ∧
    ∀ k, Core.Steps 11 ⟨.eval (.apply (core 1) .unit) (environment 0 returned []).values, k, store⟩ ⟨.ret captured, k, store⟩ := by
  let returned := Core.Value.closure .unit .unit (.var 1) [captured]
  have body : Core.Steps 1 (.initial (.var 1) [.unit, captured] store) (.final captured store) := .cons (.var rfl) .refl
  refine ⟨.application (provenance 1 (.function .unit .unit) span span) (.pure .unit .unit .unit),
    .application (counted 1 0 returned [] store span span) (.pure .unit) body, ?_⟩
  intro k
  exact CostStepComposition.apply (manual 1 0 returned [] store _) (.cons .unit .refl) body

theorem nominal_static_paths_do_not_manufacture_an_argument (n : Nat) (nominal : Core.DataTypeId) :
    RecursiveLocalComputationHasType names (context (.namedData nominal)) (source span span n) (.namedData nominal) ∧
    Core.ValueHasType (.closure (.namedData nominal) (.namedData nominal) (.var 0) [])
      (.function (.namedData nominal) (.namedData nominal)) ∧
    ¬ ∃ value, Core.ValueHasType value (.namedData nominal) := by
  refine ⟨typing n _ span span, .closure .nil (.var rfl), ?_⟩
  rintro ⟨value, typed⟩; cases typed with
  | constructed found _ => simp [Core.DataEnvironment.lookupConstructorPayloadType?, Core.DataEnvironment.lookupDataType?] at found

private def skipped : Syntax.Expr :=
  ⟨span, .group ⟨span, .conditional (ref span "x") span (ref span "f") span
    ⟨span, .call (ref span "missing") ⟨span, [source span span 2]⟩⟩⟩⟩
theorem pure_group_overlap_preserves_unselected_unsupported_source (value : Core.Value) (store : Core.Store) :
    let env : Resolved.Environment := [(xid, .bool true), (fid, value), (gid, .unit), (fid, .unit)]
    RecursiveLocalComputationEvaluates names env store skipped value store ∧
    RecursiveLocalComputationEvaluatesWithCost names env store skipped value store 4 ∧
    elaborateRecursiveLocalComputation? names (context .bool) skipped = none := by
  refine ⟨.pure (.group (.ifTrue (.identifier (.tail (by decide) .head) .head)
    (.identifier .head (.tail (by decide) .head)))),
    .group (.pure (.ifTrue (conditionCost := 1) (branchCost := 1)
      (.identifier (.tail (by decide) .head) .head) (.identifier .head (.tail (by decide) .head)))), ?_⟩
  simp [elaborateRecursiveLocalComputation?, skipped, ref, elaborateLocalExpression?,
    resolveLocalExpression?, names, LocalNameTable.lookup?]

end Tests.FrontendRecursiveLocalComputation
