import Solcore.Frontend.LocalFunctionApplication

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
    ∃ future, Core.WorldExtends [] future ∧ Core.StoreHasTypes future [] ∧ Core.RuntimeValueHasType future .unit .unit ∧
      ∀ fuel, ((inputs n).runApplication? fuel (source span span) [] = some (.unit, .done .unit []) ↔ 3 * n + 6 ≤ fuel) ∧
        ((∃ cp, (inputs n).runApplication? fuel (source span span) [] = some (.unit, .outOfFuel cp)) ↔ fuel < 3 * n + 6) := by
  obtain ⟨future, final, value, cost, ext, st, vt, evaluation, thresholds⟩ :=
    LocalInputs.runApplication?_runtime_has_exact_cost (exact n span span).hasType (runtimeInputs n) Core.StoreHasTypes.nil
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
  .closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)
private def readerInputs : LocalInputs := bundle .unit .word reader .unit readerTyped .unit
private theorem readerExact : LocalFunctionApplicationElaborates readerInputs.names readerInputs.context (source span span) core .word :=
  elaborated .unit .word reader .unit readerTyped .unit span span
private theorem readerRuntime : Core.RuntimeEnvironmentHasTypes [.word] readerInputs.environment.values readerInputs.context.values := by
  have f : Core.RuntimeValueHasType [.word] reader (.function .unit .word) :=
    .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)
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
    (∃ future, Core.WorldExtends [.word] future ∧ Core.StoreHasTypes future [w n] ∧ Core.RuntimeValueHasType future (w n) .word) ∧
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
