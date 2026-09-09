import Solcore.Frontend.LocalComputationProperties
import Solcore.Frontend.LocalComputationEvaluationProperties
import Solcore.Frontend.LocalComputationExecutionProperties
import Solcore.Frontend.LocalComputationInsertionProperties
import Solcore.Frontend.TypedLetReturnTree

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
    .cons .unit (.cons (.closure (.cons .cellRef .nil) (.loadCell (.var rfl) .word)) (.cons .unit (.cons .unit .nil))), ?_, rfl, ?_, rfl⟩
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
