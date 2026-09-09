import Solcore.Frontend.DirectWordBinaryProperties
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

/-! Symbolic original binary operands and actual delayed closure bodies.
Primitive success is supplied independently; checking never supplies raw values. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveBinaryComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Binary", by decide⟩], by decide⟩⟩, 56⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "binary.sol"⟩, 0, 1024⟩
private def operatorSpan : Syntax.SourceSpan := ⟨span.source, 500, 501⟩
private def inputs : LocalTypeInputs := ⟨[⟨"f", id 0, .function .word .word⟩, ⟨"x", id 1, .word⟩,
  ⟨"g", id 2, .function .word .word⟩, ⟨"y", id 3, .word⟩], by decide⟩
private def fn (side : Bool) := if side then "g" else "f"
private def seed (side : Bool) := if side then "y" else "x"
private def fi (side : Bool) := if side then 2 else 0
private def xi (side : Bool) := if side then 3 else 1
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (seed side)
  | n + 1 => ⟨span, .call (ref (fn side)) ⟨span, [calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (xi side)
  | n + 1 => .apply (.var (fi side)) (callCore side n)
private def source (sourceOp : Syntax.BinaryOp) (n k : Nat) : Syntax.Expr :=
  ⟨span, .binary (calls false n) ⟨operatorSpan, sourceOp⟩ (calls true k)⟩
private def core (op : Core.BinaryOp) (n k : Nat) : Core.Expr := .binary op (callCore false n) (callCore true k)
private def body (sourceOp : Syntax.BinaryOp) (n k : Nat) : Syntax.Block :=
  ⟨span, [⟨span, .letDecl ⟨span, "r"⟩ none (some (source sourceOp n k))⟩, ⟨span, .returnStmt (some (ref "r"))⟩]⟩
private def bodyCore (op : Core.BinaryOp) (n k : Nat) : Core.Expr := .letE (core op n k) (.var 0)
private theorem leaf (side : Bool) (function : Bool) :
    LocalComputationElaborates inputs.names inputs.context (ref (if function then fn side else seed side))
      (.var (if function then fi side else xi side)) (if function then .function .word .word else .word) := by
  let index := if function then fi side else xi side
  exact .pure (resolved := .var (id index)) (.identifier (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> cases function <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
private theorem callsElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .word := by
  induction n with
  | zero => exact (leaf side false).toRecursiveLocalComputation
  | succ n ih => exact .application (leaf side true).toRecursiveLocalComputation ih
private theorem callsTyped (side : Bool) (n : Nat) : RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .word := by
  have atom (function : Bool) : RecursiveLocalComputationHasType inputs.names inputs.context
      (ref (if function then fn side else seed side)) (if function then .function .word .word else .word) :=
    .pure (.identifier (id := id (if function then fi side else xi side))
      (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
  induction n with
  | zero => exact atom false
  | succ n ih => exact .application (atom true) ih
private theorem elaboration {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source sourceOp n k) (core op n k) op.resultType :=
  .binary operator (by cases operator <;> exact callsElab false n) (by cases operator <;> exact callsElab true k)
private theorem bodyElab {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body sourceOp n k) (bodyCore op n k) op.resultType :=
  .inferred (elaboration operator n k) (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private def delay : Nat → Nat → Core.Expr
  | 0, index => .var index
  | n + 1, index => .letE (.var 0) (delay n (index + 1))
private structure Actual where
  x : Core.Word
  y : Core.Word
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def value (a : Actual) (side : Bool) : Core.Value := .word (if side then a.y else a.x)
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def closure (a : Actual) (side : Bool) : Core.Value := .closure .word .word (delay (depth a side) 0) (capture a side)
private def env (a : Actual) : Resolved.Environment := [(id 0, closure a false), (id 1, value a false), (id 2, closure a true), (id 3, value a true)]
private def charge (n m : Nat) := n * (3 * m + 5) + 1
private def cost (a : Actual) (n k : Nat) := charge n a.m + charge k a.t + 3
private theorem delayed (m index : Nat) (v : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (v :: rest)[index]? = some v) :
    Core.Steps (3 * m + 1) ⟨.eval (delay m index) (v :: rest), frames, s⟩ ⟨.ret v, frames, s⟩ := by
  induction m generalizing index rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay, Nat.mul_add, Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (index + 1) (v :: rest) frames (by simpa using found))))
private theorem callsCost (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (calls side n) (value a side) s (charge n (depth a side)) := by
  have atom (function : Bool) : LocalComputationEvaluatesWithCost inputs.names (env a) s
      (ref (if function then fn side else seed side)) (if function then closure a side else value a side) s 1 :=
    .pure (.identifier (id := id (if function then fi side else xi side))
      (LocalNameTable.lookup?_iff.mp (by cases side <;> cases function <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> cases function <;> rfl)))
  induction n with
  | zero => simpa [charge, calls] using (atom false).toRecursiveLocalComputation
  | succ n ih =>
      have count : charge (n + 1) (depth a side) = 1 + charge n (depth a side) + (3 * depth a side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact .application (atom true).toRecursiveLocalComputation ih (delayed (depth a side) 0 (value a side) (capture a side) s [] rfl)
private theorem callsPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env a).values, frames, s⟩ ⟨.ret (value a side), frames, s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge, Nat.zero_mul, Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n + 1) (depth a side) = 1 + charge n (depth a side) + (3 * depth a side + 1) + 3 := by simp [charge, Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _) (delayed (depth a side) 0 (value a side) (capture a side) s [] rfl)
private theorem counted {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op)
    (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source sourceOp n k) result s (cost a n k) :=
  .binary operator (callsCost a false n s) (callsCost a true k s) applied
private theorem manual {op : Core.BinaryOp} (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    Core.Steps (cost a n k) ⟨.eval (core op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ :=
  CostStepComposition.binary (callsPath a false n s _) (callsPath a true k s _) applied

theorem original_operator_and_whole_static {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    directWordBinary? sourceOp = some op ∧
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source sourceOp n k) = some (core op n k, op.resultType) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source sourceOp n k) op.resultType ∧
    Core.HasType inputs.context.values (core op n k) op.resultType := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source sourceOp n k) op.resultType :=
    .binary operator (by cases operator <;> exact callsTyped false n) (by cases operator <;> exact callsTyped true k)
  exact ⟨directWordBinary?_iff.mpr operator, elaborateRecursiveLocalComputation?_iff.mpr (elaboration operator n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed), (elaboration operator n k).core_hasType⟩

theorem raw_and_exact_core_agree {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source sourceOp n k) result s ∧
    Core.Evaluates (env a).values s (core op n k) result s ∧
    Core.Steps (cost a n k) ⟨.eval (core op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ := by
  have raw : RecursiveLocalComputationEvaluates inputs.names (env a) s (source sourceOp n k) result s :=
    .binary operator (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, callsCost a false n s⟩)
      (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_, callsCost a true k s⟩) applied
  have exactCost := ((elaboration operator n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr
    (manual a n k s result applied [])
  exact ⟨raw, ((elaboration operator n k).evaluates_iff rfl).mp raw,
    exactCost.toStepsWithContinuation (elaboration operator n k) rfl frames⟩

theorem independent_actual_cost_unique {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result)
    {other : Core.Value} {finalStore : Core.Store} {otherCost : Nat}
    (otherEvaluation : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source sourceOp n k) other finalStore otherCost) :
    other = result ∧ finalStore = s ∧ otherCost = n * (3 * a.m + 5) + k * (3 * a.t + 5) + 5 := by
  obtain ⟨sameValue, sameStore, sameCost⟩ := otherEvaluation.deterministic (counted operator a n k s result applied)
  exact ⟨sameValue, sameStore, by simp only [cost, charge] at sameCost; omega⟩

theorem arbitrary_inserted_slot_preserves_paths {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading ++ suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core op n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a n k) ⟨.eval ((core op n k).weakenAt leading.length) (leading ++ inserted :: suffix), frames, s⟩
      ⟨.ret result, frames, s⟩ := by
  have fragment := (elaboration operator n k).core_fragment
  have original := Core.steps_from_initial_sound (manual a n k s result applied [])
  rw [← split] at original
  have transported := (fragment.evaluates_insert_iff leading suffix inserted).mpr original
  have reflected := (fragment.evaluates_insert_iff leading suffix inserted).mp transported
  obtain ⟨commonCost, paths⟩ := fragment.insertion_paths leading suffix inserted reflected
  have known : Core.Steps (cost a n k) (.initial (core op n k) (leading ++ suffix) s) (.final result s) := by
    rw [split]; exact manual a n k s result applied []
  have sameCost := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length, fun frames => sameCost ▸ (paths frames).2⟩

private def between (a : Actual) (op : Core.BinaryOp) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (value a false), [.binaryRight op (callCore true k) (env a).values], s⟩
private def pending (a : Actual) (op : Core.BinaryOp) (s : Core.Store) : Core.State :=
  ⟨.ret (value a true), [.binaryApply op (value a false)], s⟩
theorem genuine_operand_checkpoints (a : Actual) (op : Core.BinaryOp) (n k : Nat) (s : Core.Store)
    (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    Core.runStateful (charge n a.m + 1) (.initial (core op n k) (env a).values s) = .outOfFuel (between a op k s) ∧
    Core.runStateful (charge n a.m + charge k a.t + 2) (.initial (core op n k) (env a).values s) = .outOfFuel (pending a op s) := by
  constructor
  · apply Core.runStateful_outOfFuel_complete (next := ⟨.eval (callCore true k) (env a).values, [.binaryApply op (value a false)], s⟩)
    · simpa [Core.State.initial, core, between, depth, Nat.add_comm] using Core.Steps.cons .enterBinary (callsPath a false n s [.binaryRight op (callCore true k) (env a).values])
    · exact Core.advance_next_iff.mpr .enterBinaryRight
  · apply Core.runStateful_outOfFuel_complete (next := .final result s)
    · simpa [Core.State.initial, core, pending, depth, Nat.add_assoc, Nat.add_left_comm] using Core.Steps.cons .enterBinary
        ((callsPath a false n s [.binaryRight op (callCore true k) (env a).values]).trans
          (.cons .enterBinaryRight (callsPath a true k s [.binaryApply op (value a false)])))
    · exact Core.advance_next_iff.mpr (.applyBinary applied)

theorem all_fuels_and_full_checkpoint_resume (a : Actual) (op : Core.BinaryOp) (n k : Nat) (s : Core.Store)
    (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result)
    (fuel spent additional : Nat) (checkpoint : Core.State)
    (exhausted : Core.runStateful spent (.initial (core op n k) (env a).values s) = .outOfFuel checkpoint) :
    (Core.runStateful fuel (.initial (core op n k) (env a).values s) = .done result s ↔ cost a n k ≤ fuel) ∧
    spent < cost a n k ∧ Core.Steps (cost a n k - spent) checkpoint (.final result s) ∧
    Core.runStateful additional checkpoint = Core.runStateful (spent + additional) (.initial (core op n k) (env a).values s) := by
  have path := manual a n k s result applied []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff, residual.1, residual.2, Core.runStateful_resume exhausted additional⟩

theorem inferred_original_body_static {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (n k : Nat) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body sourceOp n k) = some (bodyCore op n k, op.resultType) ∧
    RecursiveComputationReturnTreeHasType [] owner inputs (body sourceOp n k) op.resultType ∧
    Core.HasType inputs.context.values (bodyCore op n k) op.resultType := by
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab operator n k),
    (computationReturnTreeHasType_iff_elaborates (ChildHasType := RecursiveLocalComputationHasType)
      (ChildElab := RecursiveLocalComputationElaborates) recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_, bodyElab operator n k⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab operator n k)⟩

private theorem bodyCounted {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp} (operator : DirectWordBinary sourceOp op)
    (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value) (applied : op.apply (value a false) (value a true) = some result) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body sourceOp n k) result s (cost a n k + 3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost, body, ref, Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted operator a n k s result applied)
    (.expression (.pure (.identifier .head .head)))
private theorem bodyManual {op : Core.BinaryOp} (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) :
    Core.Steps (cost a n k + 3) ⟨.eval (bodyCore op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ := by
  simpa [bodyCore, Nat.add_assoc] using CostStepComposition.letE (manual a n k s result applied (.letBody (.var 0) (env a).values :: frames))
    (Core.Steps.cons (.var rfl) .refl)

theorem shared_body_transports_actual_cost {sourceOp : Syntax.BinaryOp} {op : Core.BinaryOp}
    (operator : DirectWordBinary sourceOp op) (a : Actual) (n k : Nat) (s : Core.Store) (result : Core.Value)
    (applied : op.apply (value a false) (value a true) = some result) (frames : List Core.Frame) (fuel : Nat) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body sourceOp n k) result s (cost a n k + 3) ∧
    Core.Steps (cost a n k + 3) ⟨.eval (bodyCore op n k) (env a).values, frames, s⟩ ⟨.ret result, frames, s⟩ ∧
    (Core.runStateful fuel (.initial (bodyCore op n k) (env a).values s) = .done result s ↔ cost a n k + 3 ≤ fuel) := by
  have reflected := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab operator n k) (environment := env a) rfl).mpr
      (bodyManual a n k s result applied [])
  exact ⟨reflected, ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
    (bodyCounted operator a n k s result applied) (bodyElab operator n k) rfl frames,
    (bodyManual a n k s result applied []).runStateful_done_iff⟩

theorem fixed_source_actual_body_cost_is_unbounded (limit : Nat) (x y : Core.Word) (s : Core.Store) :
    ∃ a : Actual, RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s
      (body .add 1 1) (.word (x + y)) s (cost a 1 1 + 3) ∧ limit < cost a 1 1 + 3 := by
  let a : Actual := ⟨x, y, limit, 0, [], []⟩
  refine ⟨a, bodyCounted .add a 1 1 s (.word (x + y)) rfl, ?_⟩
  simp [cost, charge, a]; omega

theorem pending_continuation_is_not_a_safety_claim (s : Core.Store) :
    Core.Steps 5 ⟨.eval (core .wordGt 0 0) (env ⟨.zero, .zero, 0, 0, [], []⟩).values, [.unaryApply .wordNot], s⟩
      ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ ∧
    Core.runStateful 0 ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ =
      .fault (.invalidUnaryOperand .wordNot (.bool false)) ⟨.ret (.bool false), [.unaryApply .wordNot], s⟩ :=
  ⟨manual ⟨.zero, .zero, 0, 0, [], []⟩ 0 0 s (.bool false) rfl [.unaryApply .wordNot], rfl⟩

end Tests.FrontendRecursiveBinaryComputation
