import Solcore.Frontend.LocalComputationReturnTreeTypingProperties
import Solcore.Frontend.LocalComputationReturnTreeCostProperties
import Solcore.Frontend.LocalComputationReturnTreeEmbeddingProperties
import Solcore.Core.FuelResumptionProperties

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
