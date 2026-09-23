import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties
import Solcore.Core.Safety

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
