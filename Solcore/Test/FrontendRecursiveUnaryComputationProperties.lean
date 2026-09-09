import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Core.FuelResumptionProperties

/-! Arbitrary original prefix/call depths retain actual delayed bodies and captures.
Store invariance below belongs only to this explicitly store-free delay fixture. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveUnaryComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Unary", by decide⟩], by decide⟩⟩, 58⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "unary.sol"⟩, 0, 1024⟩
private def ty : Bool → Core.Ty | false => .bool | true => .word
private def op : Bool → Core.UnaryOp | false => .boolNot | true => .wordNot
private def sourceOp : Bool → Syntax.UnaryOp | false => .logicalNot | true => .bitNot
private def inputs (mode : Bool) : LocalTypeInputs :=
  ⟨[⟨"f", id 0, .function (ty mode) (ty mode)⟩, ⟨"x", id 1, ty mode⟩], by change [id 0, id 1].Nodup; decide⟩
private def ref (function : Bool) : Syntax.Expr := ⟨span, .identifier ⟨span, if function then "f" else "x"⟩⟩
private def unary (mode : Bool) (child : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .unary ⟨⟨span.source, 0, 1⟩, sourceOp mode⟩ child⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref false
  | n + 1 => ⟨span, .call (ref true) ⟨span, [calls n]⟩⟩
private def callCore : Nat → Core.Expr | 0 => .var 1 | n + 1 => .apply (.var 0) (callCore n)
private def source (mode : Bool) : Nat → Nat → Syntax.Expr
  | 0, n => calls n | r + 1, n => unary mode (source mode r n)
private def core (mode : Bool) : Nat → Nat → Core.Expr
  | 0, n => callCore n | r + 1, n => .unary (op mode) (core mode r n)
private theorem oldLeaf (mode function : Bool) :
    LocalComputationElaborates (inputs mode).names (inputs mode).context (ref function)
      (.var (if function then 0 else 1)) (if function then .function (ty mode) (ty mode) else ty mode) :=
  .pure (.identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases function <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl)))
private theorem leafTyped (mode function : Bool) :
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (ref function)
      (if function then .function (ty mode) (ty mode) else ty mode) :=
  .pure (.identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl)))
private theorem callElab (mode : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs mode).names (inputs mode).context (calls n) (callCore n) (ty mode) := by
  induction n with
  | zero => exact (oldLeaf mode false).toRecursiveLocalComputation
  | succ n ih => exact .application (oldLeaf mode true).toRecursiveLocalComputation ih
private theorem elaboration (mode : Bool) (r n : Nat) :
    RecursiveLocalComputationElaborates (inputs mode).names (inputs mode).context (source mode r n) (core mode r n) (ty mode) := by
  induction r with
  | zero => exact callElab mode n
  | succ r ih => cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private theorem typing (mode : Bool) (r n : Nat) :
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (source mode r n) (ty mode) := by
  induction r with
  | zero =>
      induction n with
      | zero => exact leafTyped mode false
      | succ n ih => exact .application (leafTyped mode true) ih
  | succ r ih => cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private def delay : Nat → Nat → Core.Expr
  | 0, i => .var i | m + 1, i => .letE (.var 0) (delay m (i + 1))
private def booleanResult : Nat → Bool → Bool | 0, b => b | r + 1, b => !(booleanResult r b)
private def wordResult : Nat → Core.Word → Core.Word | 0, w => w | r + 1, w => (wordResult r w).bitNot
private def result (mode : Bool) (r : Nat) (b : Bool) (w : Core.Word) : Core.Value :=
  if mode then .word (wordResult r w) else .bool (booleanResult r b)
private def env (mode : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) : Resolved.Environment :=
  [(id 0, .closure (ty mode) (ty mode) (delay m 0) captures), (id 1, result mode 0 b w)]
private def charge (r n m : Nat) := 2 * r + n * (3 * m + 5) + 1
private theorem atomCost (mode function : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (ref function)
      (if function then .closure (ty mode) (ty mode) (delay m 0) captures else result mode 0 b w) s 1 :=
  .identifier (id := id (if function then 0 else 1)) (LocalNameTable.lookup?_iff.mp (by cases function <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases function <;> rfl))
private theorem delayed (m i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m i) environment, frames, s⟩ ⟨.ret value, frames, s⟩ := by
  induction m generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i + 1) (head :: head :: rest) frames (by simpa using found))))
private theorem callCost (mode : Bool) (n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (calls n) (result mode 0 b w) s (charge 0 n m) := by
  induction n with
  | zero => simpa [charge, calls] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost mode false m b w captures s)
  | succ n ih =>
      have count : charge 0 (n + 1) m = 1 + charge 0 n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (.pure (atomCost mode true m b w captures s)) ih
        (delayed m 0 (result mode 0 b w :: captures) (result mode 0 b w) s [] rfl)
private theorem callPath (mode : Bool) (n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge 0 n m) ⟨.eval (callCore n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode 0 b w), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.mul_zero, Nat.zero_mul, Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge 0 (n + 1) m = 1 + charge 0 n m + (3 * m + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _)
        (delayed m 0 (result mode 0 b w :: captures) (result mode 0 b w) s [] rfl)
private theorem counted (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode r n) (result mode r b w) s (charge r n m) := by
  induction r with
  | zero => exact callCost mode n m b w captures s
  | succ r ih =>
      have count : charge (r + 1) n m = charge r n m + 2 := by simp [charge, Nat.mul_add]; omega
      rw [count]; cases mode <;> first | exact .logicalNot ih | exact .bitNot ih
private theorem manual (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge r n m) ⟨.eval (core mode r n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  induction r generalizing frames with
  | zero => exact callPath mode n m b w captures s frames
  | succ r ih =>
      have count : charge (r + 1) n m = charge r n m + 2 := by simp [charge, Nat.mul_add]; omega
      rw [count]; exact CostStepComposition.unary (ih _) (by cases mode <;> rfl)

theorem arbitrary_prefix_and_call_static (mode : Bool) (r n : Nat) :
    elaborateRecursiveLocalComputation? (inputs mode).names (inputs mode).context (source mode r n) = some (core mode r n, ty mode) ∧
    RecursiveLocalComputationHasType (inputs mode).names (inputs mode).context (source mode r n) (ty mode) ∧
    Core.HasType (inputs mode).context.values (core mode r n) (ty mode) :=
  ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration mode r n),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp (typing mode r n)),
    (elaboration mode r n).core_hasType⟩

theorem actual_raw_and_exact_path (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word)
    (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs mode).names (env mode m b w captures) s (source mode r n) (result mode r b w) s ∧
    Core.Evaluates (env mode m b w captures).values s (core mode r n) (result mode r b w) s ∧
    Core.Steps (charge r n m) ⟨.eval (core mode r n) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, counted mode r n m b w captures s⟩
  have fromManual := ((elaboration mode r n).evaluatesWithCost_iff_steps (environment := env mode m b w captures) rfl).mpr (manual mode r n m b w captures s [])
  exact ⟨raw, ((elaboration mode r n).evaluates_iff rfl).mp raw,
    fromManual.toStepsWithContinuation (elaboration mode r n) rfl frames⟩

theorem actual_cost_jointly_unique (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word)
    (captures : Core.Environment) (s : Core.Store) {value : Core.Value} {finalStore : Core.Store} {cost : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode r n) value finalStore cost) :
    value = result mode r b w ∧ finalStore = s ∧ cost = 2 * r + n * (3 * m + 5) + 1 :=
  other.deterministic (counted mode r n m b w captures s)

theorem pure_and_recursive_unary_overlap (mode : Bool) (m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    LocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 := by
  have old : LocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 0) (result mode 1 b w) s 3 := by
    cases mode <;> first | exact .pure (.logicalNot (atomCost false false m b w captures s)) | exact .pure (.bitNot (atomCost true false m b w captures s))
  have new := counted mode 1 0 m b w captures s
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old, same.2.2 ▸ new⟩

theorem arbitrary_caller_insertion (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env mode m b w captures).values) :
    RecursiveLocalComputationFragment ((core mode r n).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (charge r n m) ⟨.eval ((core mode r n).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have fragment := (elaboration mode r n).core_fragment
  have original := Core.steps_from_initial_sound (manual mode r n m b w captures s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (charge r n m) (.initial (core mode r n) (leading ++ suffix) s) (.final (result mode r b w) s) := by
    rw [split]; exact manual mode r n m b w captures s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => same ▸ (paths frames).2⟩

private def checkpoint (mode : Bool) (r : Nat) (b : Bool) (w : Core.Word) (s : Core.Store) : Core.State :=
  ⟨.ret (result mode r b w), [.unaryApply (op mode)], s⟩
theorem genuine_operand_finished_checkpoint (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    Core.runStateful (charge r n m + 1) (.initial (core mode (r + 1) n) (env mode m b w captures).values s) = .outOfFuel (checkpoint mode r b w s) := by
  have childPrefix : Core.Steps (charge r n m + 1) (.initial (core mode (r + 1) n) (env mode m b w captures).values s) (checkpoint mode r b w s) :=
    .cons .enterUnary (manual mode r n m b w captures s [.unaryApply (op mode)])
  exact Core.runStateful_outOfFuel_complete childPrefix (Core.advance_next_iff.mpr
    (Core.Transition.applyUnary (result := result mode (r + 1) b w) (by cases mode <;> rfl)))

theorem all_fuels_residual_and_full_resume (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core mode r n) (env mode m b w captures).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core mode r n) (env mode m b w captures).values s) = .done (result mode r b w) s ↔ charge r n m ≤ fuel) ∧
    spent < charge r n m ∧ Core.Steps (charge r n m - spent) cp (.final (result mode r b w) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent + additional) (.initial (core mode r n) (env mode m b w captures).values s) := by
  have path := manual mode r n m b w captures s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (mode : Bool) (limit : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    ∃ m, RecursiveLocalComputationEvaluatesWithCost (inputs mode).names (env mode m b w captures) s (source mode 1 1) (result mode 1 b w) s (charge 1 1 m) ∧ limit < charge 1 1 m := by
  exact ⟨limit, counted mode 1 1 limit b w captures s, by simp [charge]; omega⟩

private def body (mode : Bool) (r n : Nat) : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "r"⟩ none (some (source mode r n))⟩, ⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "r"⟩⟩)⟩]⟩
private theorem bodyElab (mode : Bool) (r n : Nat) : RecursiveComputationReturnTreeElaborates [] owner (inputs mode)
    (body mode r n) (.letE (core mode r n) (.var 0)) (ty mode) :=
  .inferred (elaboration mode r n)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs mode).names (env mode m b w captures) s (body mode r n) (result mode r b w) s (charge r n m + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted mode r n m b w captures s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge r n m + 3) ⟨.eval (.letE (core mode r n) (.var 0)) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual mode r n m b w captures s (.letBody (.var 0) (env mode m b w captures).values :: frames)) (.cons (.var rfl) .refl)

theorem shared_body_original_source_and_exact_cost (mode : Bool) (r n m : Nat) (b : Bool) (w : Core.Word) (captures : Core.Environment) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs mode) (body mode r n) = some (.letE (core mode r n) (.var 0), ty mode) ∧
    Core.HasType (inputs mode).context.values (.letE (core mode r n) (.var 0)) (ty mode) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs mode).names (env mode m b w captures) s (body mode r n) (result mode r b w) s (charge r n m + 3) ∧
    Core.Steps (charge r n m + 3) ⟨.eval (.letE (core mode r n) (.var 0)) (env mode m b w captures).values, frames, s⟩ ⟨.ret (result mode r b w), frames, s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab mode r n) (environment := env mode m b w captures) rfl).mpr (bodyManual mode r n m b w captures s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab mode r n),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab mode r n), costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost mode r n m b w captures s) (bodyElab mode r n) rfl frames⟩

end Tests.FrontendRecursiveUnaryComputation
