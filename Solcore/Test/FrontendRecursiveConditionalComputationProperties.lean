import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Core.FuelResumptionProperties

/-! Original conditional children have independent static and actual certificates.
Only the selected actual branch contributes a path or a cost. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveConditionalComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Conditional", by decide⟩], by decide⟩⟩, 57⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "conditional.sol"⟩, 0, 1024⟩
private inductive Key | p | x | f | g | y | c
private def index : Key → Nat | .p => 0 | .x => 1 | .f => 2 | .g => 3 | .y => 4 | .c => 5
private def name : Key → String | .p => "p" | .x => "x" | .f => "f" | .g => "g" | .y => "y" | .c => "c"
private def typeOf (a : Core.Ty) : Key → Core.Ty | .p => .function a .bool | .f | .g => .function a a | .c => .bool | _ => a
private def inputs (a : Core.Ty) : LocalTypeInputs := ⟨[⟨"p", id 0, .function a .bool⟩, ⟨"x", id 1, a⟩,
  ⟨"f", id 2, .function a a⟩, ⟨"g", id 3, .function a a⟩, ⟨"y", id 4, a⟩, ⟨"c", id 5, .bool⟩], by
    change [id 0, id 1, id 2, id 3, id 4, id 5].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span, .identifier ⟨span, name key⟩⟩
private def call (fn arg : Syntax.Expr) : Syntax.Expr := ⟨span, .call fn ⟨span, [arg]⟩⟩
private def branch (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n + 1 => call (ref (if side then .g else .f)) (branch side n)
private def branchCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 4 else 1)
  | n + 1 => .apply (.var (if side then 3 else 2)) (branchCore side n)
private def conditional (guard yes no : Syntax.Expr) : Syntax.Expr :=
  ⟨span, .conditional guard ⟨span.source, 400, 401⟩ yes ⟨span.source, 700, 701⟩ no⟩
private def source (n k : Nat) := conditional (call (ref .p) (ref .x)) (branch false n) (branch true k)
private def core (n k : Nat) := Core.Expr.ifE (.apply (.var 0) (.var 1)) (branchCore false n) (branchCore true k)
private theorem oldLeaf (a : Core.Ty) (key : Key) :
    LocalComputationElaborates (inputs a).names (inputs a).context (ref key) (.var (index key)) (typeOf a key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leaf (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (ref key) (.var (index key)) (typeOf a key) :=
  (oldLeaf a key).toRecursiveLocalComputation
private theorem leafTyped (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (ref key) (typeOf a key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem branchElab (a : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (branch side n) (branchCore side n) a := by
  induction n with
  | zero => cases side <;> exact leaf a _
  | succ n ih => exact .application (by cases side <;> exact leaf a _) ih
private theorem branchTyped (a : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (branch side n) a := by
  induction n with
  | zero => cases side <;> exact leafTyped a _
  | succ n ih => exact .application (by cases side <;> exact leafTyped a _) ih
private theorem elaboration (a : Core.Ty) (n k : Nat) :
    RecursiveLocalComputationElaborates (inputs a).names (inputs a).context (source n k) (core n k) a :=
  .conditional (.application (leaf a .p) (leaf a .x)) (branchElab a false n) (branchElab a true k)
private def delay : Nat → Nat → Core.Expr
  | 0, i => .var i
  | n + 1, i => .letE (.var 0) (delay n (i + 1))
private structure Actual where
  choice : Bool
  x : Core.Value
  y : Core.Value
  guardDelay : Nat
  leftDelay : Nat
  rightDelay : Nat
  guardCapture : Core.Environment
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def actual (a : Core.Ty) (v : Actual) : Key → Core.Value
  | .p => .closure a .bool (delay v.guardDelay 1) (.bool v.choice :: v.guardCapture)
  | .f => .closure a a (delay v.leftDelay 0) v.leftCapture
  | .g => .closure a a (delay v.rightDelay 0) v.rightCapture
  | .x => v.x | .y => v.y | .c => .bool v.choice
private def env (a : Core.Ty) (v : Actual) : Resolved.Environment :=
  [(id 0, actual a v .p), (id 1, v.x), (id 2, actual a v .f), (id 3, actual a v .g), (id 4, v.y), (id 5, .bool v.choice)]
private def branchValue (v : Actual) (side : Bool) := if side then v.y else v.x
private def branchDelay (v : Actual) (side : Bool) := if side then v.rightDelay else v.leftDelay
private def branchCapture (v : Actual) (side : Bool) := if side then v.rightCapture else v.leftCapture
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private def guardCost (v : Actual) := 3 * v.guardDelay + 6
private def cost (v : Actual) (n k : Nat) := guardCost v + (if v.choice then charge n v.leftDelay else charge k v.rightDelay) + 2
private def result (v : Actual) := if v.choice then v.x else v.y
private theorem atomCost (a : Core.Ty) (v : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs a).names (env a v) s (ref key) (actual a v key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (n i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3 * n + 1) ⟨.eval (delay n i) environment, frames, s⟩ ⟨.ret value, frames, s⟩ := by
  induction n generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i + 1) (head :: head :: rest) frames (by simpa using found))))
private theorem branchCosted (a : Core.Ty) (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (branch side n) (branchValue v side) s (charge n (branchDelay v side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [charge, branch, branchValue, actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a v .x s)
      · simpa [charge, branch, branchValue, actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a v .y s)
  | succ n ih =>
      have count : charge (n + 1) (branchDelay v side) = 1 + charge n (branchDelay v side) + (3 * branchDelay v side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost a v _ s)) ih
        (delayed (branchDelay v side) 0 (branchValue v side :: branchCapture v side) (branchValue v side) s [] rfl)
private theorem branchPath (a : Core.Ty) (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (branchDelay v side)) ⟨.eval (branchCore side n) (env a v).values, frames, s⟩ ⟨.ret (branchValue v side), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var (value := branchValue v side) (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n + 1) (branchDelay v side) = 1 + charge n (branchDelay v side) + (3 * branchDelay v side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (branchDelay v side) 0 (branchValue v side :: branchCapture v side) (branchValue v side) s [] rfl)
private theorem guardCosted (a : Core.Ty) (v : Actual) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (call (ref .p) (ref .x)) (.bool v.choice) s (guardCost v) := by
  have count : guardCost v = 1 + 1 + (3 * v.guardDelay + 1) + 3 := by simp [guardCost]; omega
  rw [count]; exact .application (.pure (atomCost a v .p s)) (.pure (atomCost a v .x s))
    (delayed v.guardDelay 1 (v.x :: .bool v.choice :: v.guardCapture) (.bool v.choice) s [] rfl)
private theorem guardPath (a : Core.Ty) (v : Actual) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (guardCost v) ⟨.eval (.apply (.var 0) (.var 1)) (env a v).values, frames, s⟩ ⟨.ret (.bool v.choice), frames, s⟩ := by
  have count : guardCost v = 1 + 1 + (3 * v.guardDelay + 1) + 3 := by simp [guardCost]; omega
  rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (.cons (.var rfl) .refl)
    (delayed v.guardDelay 1 (v.x :: .bool v.choice :: v.guardCapture) (.bool v.choice) s [] rfl)
private theorem counted (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source n k) (result v) s (cost v n k) := by
  cases chosen : v.choice
  · simpa [source, conditional, cost, result, chosen, branchValue, branchDelay] using RecursiveLocalComputationEvaluatesWithCost.ifFalse
      (chosen ▸ guardCosted a v s) (branchCosted a v true k s)
  · simpa [source, conditional, cost, result, chosen, branchValue, branchDelay] using RecursiveLocalComputationEvaluatesWithCost.ifTrue
      (chosen ▸ guardCosted a v s) (branchCosted a v false n s)
private theorem manual (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost v n k) ⟨.eval (core n k) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  cases chosen : v.choice
  · simpa [core, cost, result, chosen, branchValue, branchDelay] using CostStepComposition.ifFalse
      (chosen ▸ guardPath a v s (.ifBranches (branchCore false n) (branchCore true k) (env a v).values :: frames)) (branchPath a v true k s frames)
  · simpa [core, cost, result, chosen, branchValue, branchDelay] using CostStepComposition.ifTrue
      (chosen ▸ guardPath a v s (.ifBranches (branchCore false n) (branchCore true k) (env a v).values :: frames)) (branchPath a v false n s frames)

theorem arbitrary_type_original_three_children (a : Core.Ty) (n k : Nat) :
    elaborateRecursiveLocalComputation? (inputs a).names (inputs a).context (source n k) = some (core n k, a) ∧
    RecursiveLocalComputationHasType (inputs a).names (inputs a).context (source n k) a ∧
    Core.HasType (inputs a).context.values (core n k) a := by
  have typed : RecursiveLocalComputationHasType (inputs a).names (inputs a).context (source n k) a :=
    .conditional (.application (leafTyped a .p) (leafTyped a .x)) (branchTyped a false n) (branchTyped a true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration a n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),
    (elaboration a n k).core_hasType⟩

theorem arbitrary_actual_selected_path (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs a).names (env a v) s (source n k) (result v) s ∧
    Core.Evaluates (env a v).values s (core n k) (result v) s ∧
    Core.Steps (cost v n k) ⟨.eval (core n k) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have guard := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, guardCosted a v s⟩
  have raw : RecursiveLocalComputationEvaluates (inputs a).names (env a v) s (source n k) (result v) s := by
    cases chosen : v.choice
    · simpa [source, conditional, result, chosen, branchValue] using RecursiveLocalComputationEvaluates.ifFalse
        (chosen ▸ guard) (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, branchCosted a v true k s⟩)
    · simpa [source, conditional, result, chosen, branchValue] using RecursiveLocalComputationEvaluates.ifTrue
        (chosen ▸ guard) (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, branchCosted a v false n s⟩)
  have costed := ((elaboration a n k).evaluatesWithCost_iff_steps (environment := env a v) rfl).mpr (manual a v n k s [])
  exact ⟨raw, ((elaboration a n k).evaluates_iff rfl).mp raw, costed.toStepsWithContinuation (elaboration a n k) rfl frames⟩

theorem actual_cost_unique_without_unselected_charge (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source n k) value finalStore steps) :
    value = result v ∧ finalStore = s ∧ steps = guardCost v + (if v.choice then charge n v.leftDelay else charge k v.rightDelay) + 2 :=
  other.deterministic (counted a v n k s)

theorem unselected_depth_does_not_contribute (v : Actual) (n k ignored : Nat) :
    (v.choice = true → cost v n k = cost v n ignored) ∧
    (v.choice = false → cost v n k = cost v ignored k) := by
  constructor <;> intro chosen <;> simp [cost, chosen]

theorem unselected_source_is_not_a_raw_premise (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store)
    (skipped : Syntax.Expr) (chosen : v.choice = true) :
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s
      (conditional (call (ref .p) (ref .x)) (branch false n) skipped) v.x s (guardCost v + charge n v.leftDelay + 2) :=
  .ifTrue (chosen ▸ guardCosted a v s) (branchCosted a v false n s)

theorem pure_and_recursive_conditional_overlap (a : Core.Ty) (v : Actual) (s : Core.Store) :
    LocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
  have old : LocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
    cases chosen : v.choice
    · simp [conditional, result, chosen]; exact .pure (.ifFalse (by simpa [actual, chosen] using atomCost a v .c s) (atomCost a v .y s))
    · simp [conditional, result, chosen]; exact .pure (.ifTrue (by simpa [actual, chosen] using atomCost a v .c s) (atomCost a v .x s))
  have new : RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (conditional (ref .c) (ref .x) (ref .y)) (result v) s 4 := by
    cases chosen : v.choice
    · simp [conditional, result, chosen]; exact .ifFalse (.pure (by simpa [actual, chosen] using atomCost a v .c s)) (.pure (atomCost a v .y s))
    · simp [conditional, result, chosen]; exact .ifTrue (.pure (by simpa [actual, chosen] using atomCost a v .c s)) (.pure (atomCost a v .x s))
  have equality := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old, equality.2.2 ▸ new⟩

theorem arbitrary_caller_insertion (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env a v).values) :
    RecursiveLocalComputationFragment ((core n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost v n k) ⟨.eval ((core n k).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have fragment := (elaboration a n k).core_fragment
  have original := Core.steps_from_initial_sound (manual a v n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost v n k) (.initial (core n k) (leading ++ suffix) s) (.final (result v) s) := by rw [split]; exact manual a v n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => same ▸ (paths frames).2⟩

private def checkpoint (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool v.choice), [.ifBranches (branchCore false n) (branchCore true k) (env a v).values], s⟩
theorem actual_guard_checkpoint (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (guardCost v + 1) (.initial (core n k) (env a v).values s) = .outOfFuel (checkpoint a v n k s) := by
  have guardPrefix : Core.Steps (guardCost v + 1) (.initial (core n k) (env a v).values s) (checkpoint a v n k s) :=
    .cons .enterIf (guardPath a v s [.ifBranches (branchCore false n) (branchCore true k) (env a v).values])
  cases chosen : v.choice
  · exact Core.runStateful_outOfFuel_complete guardPrefix (Core.advance_next_iff.mpr (by simpa [checkpoint, chosen] using Core.Transition.chooseFalse (thenBranch := branchCore false n) (elseBranch := branchCore true k) (environment := (env a v).values) (continuation := []) (store := s)))
  · exact Core.runStateful_outOfFuel_complete guardPrefix (Core.advance_next_iff.mpr (by simpa [checkpoint, chosen] using Core.Transition.chooseTrue (thenBranch := branchCore false n) (elseBranch := branchCore true k) (environment := (env a v).values) (continuation := []) (store := s)))

theorem all_fuels_genuine_residual_and_full_resume (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core n k) (env a v).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core n k) (env a v).values s) = .done (result v) s ↔ cost v n k ≤ fuel) ∧
    spent < cost v n k ∧ Core.Steps (cost v n k - spent) cp (.final (result v) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent + additional) (.initial (core n k) (env a v).values s) := by
  have path := manual a v n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem same_source_actual_guard_cost_is_unbounded (a : Core.Ty) (limit : Nat) (x y : Core.Value) (s : Core.Store) :
    ∃ v : Actual, RecursiveLocalComputationEvaluatesWithCost (inputs a).names (env a v) s (source 1 1) x s (cost v 1 1) ∧ limit < cost v 1 1 := by
  let v : Actual := ⟨true, x, y, limit, 0, 0, [], [], []⟩
  refine ⟨v, counted a v 1 1 s, ?_⟩
  simp [cost, guardCost, charge, v]; omega

private def body (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span, .letDecl ⟨span, "r"⟩ none (some (source n k))⟩, ⟨span, .returnStmt (some ⟨span, .identifier ⟨span, "r"⟩⟩)⟩]⟩
private theorem bodyElab (a : Core.Ty) (n k : Nat) : RecursiveComputationReturnTreeElaborates [] owner (inputs a)
    (body n k) (.letE (core n k) (.var 0)) a :=
  .inferred (elaboration a n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCosted (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names (env a v) s (body n k) (result v) s (cost v n k + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted a v n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost v n k + 3) ⟨.eval (.letE (core n k) (.var 0)) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual a v n k s (.letBody (.var 0) (env a v).values :: frames)) (.cons (.var rfl) .refl)

theorem shared_body_exact_source_and_cost (a : Core.Ty) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs a) (body n k) = some (.letE (core n k) (.var 0), a) ∧
    Core.HasType (inputs a).context.values (.letE (core n k) (.var 0)) a ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs a).names (env a v) s (body n k) (result v) s (cost v n k + 3) ∧
    Core.Steps (cost v n k + 3) ⟨.eval (.letE (core n k) (.var 0)) (env a v).values, frames, s⟩ ⟨.ret (result v), frames, s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab a n k) (environment := env a v) rfl).mpr (bodyManual a v n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab a n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab a n k), costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCosted a v n k s) (bodyElab a n k) rfl frames⟩

end Tests.FrontendRecursiveConditionalComputation
