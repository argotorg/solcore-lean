import Solcore.Frontend.LocalApplication
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Frontend.ReturnBody

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
private theorem readerTyped : Core.ValueHasType reader (.function .unit .word) := .closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)
private def readerInputs : LocalInputs := bundle .unit .word reader .unit readerTyped .unit
private def w (n : Nat) : Core.Value := .word (Core.Word.ofNatModulo n)
private theorem readerCost (v : Core.Value) : LocalFunctionApplicationEvaluatesWithCost readerInputs.names readerInputs.environment [v] (call span span) v [v] 8 :=
  callCost .unit .word (.loadCell (.var 1)) [.cellRef .word 0] .unit v readerTyped .unit [v] [v] 3
    (.cons .enterLoadCell (.cons (.var rfl) (.cons (.applyLoadCell rfl) .refl)))
private theorem readerRuntime : Core.RuntimeEnvironmentHasTypes [.word] readerInputs.environment.values readerInputs.context.values := by
  have f : Core.RuntimeValueHasType [.word] reader (.function .unit .word) := .closure (.cons (.cellRef rfl) .nil) (.loadCell (.var rfl) .word)
  exact .cons .unit (.cons f (.cons f (.cons .bool .nil)))
theorem runtime_world_laws_transport_through_full_result_equality (n fuel : Nat) (error : Core.MachineFault) (fault : Core.State) :
    readerInputs.runApplicationReturnBody? 8 body [w n] = some (.word, .done (w n) [w n]) ∧
    (∃ world, Core.WorldExtends [.word] world ∧ Core.StoreHasTypes world [w n] ∧ Core.RuntimeValueHasType world (w n) .word) ∧
    readerInputs.runApplicationReturnBody? fuel body [w n] ≠ some (.word, .fault error fault) := by
  have st : Core.StoreHasTypes [.word] [w n] := Core.StoreHasTypes.nil.allocate .word .word
  obtain ⟨_, final, v, cost, _, _, _, actual, thresholds⟩ := LocalInputs.runApplication?_runtime_has_exact_cost (inputs := readerInputs) (child .unit .word span span).hasType readerRuntime st
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
private def allocatorInputs : LocalInputs := bundle .word (.cell .word) allocator (w 7) (.closure .nil (.newCell (.var rfl) .word)) .word
theorem return_keeps_the_actual_allocation_effect (store : Core.Store) :
    LocalApplicationReturnBodyEvaluatesWithCost allocatorInputs.names allocatorInputs.environment store body (.cellRef .word store.length) (store ++ [w 7]) 8 ∧
    allocatorInputs.runApplicationReturnBody? 8 body store = some (.cell .word, .done (.cellRef .word store.length) (store ++ [w 7])) := by
  have actual : LocalFunctionApplicationEvaluatesWithCost allocatorInputs.names allocatorInputs.environment store (call span span)
      (.cellRef .word store.length) (store ++ [w 7]) 8 :=
    callCost .word (.cell .word) (.newCell .word (.var 0)) [] (w 7) (.cellRef .word store.length) (.closure .nil (.newCell (.var rfl) .word)) .word store (store ++ [w 7]) 3
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
