import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationEmbeddingProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.RecursiveComputationReturnTreeEmbeddingProperties
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Core.FuelResumptionProperties

/-! Original two-binding comparisons have separate static, actual and manual paths.
Unchanged stores below belong only to the explicit store-free delayed bodies. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveOrderedComparison
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Comparison",by decide⟩],by decide⟩⟩,60⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"ordering.sol"⟩,0,1024⟩
private inductive Key | f | x | g | y | c
private def index : Key → Nat | .f => 0 | .x => 1 | .g => 2 | .y => 3 | .c => 4
private def name : Key → String | .f => "f" | .x => "x" | .g => "g" | .y => "y" | .c => "c"
private def typeOf : Key → Core.Ty | .f | .g => .function .word .word | .c => .bool | _ => .word
private def inputs : LocalTypeInputs := ⟨[⟨"f",id 0,.function .word .word⟩,⟨"x",id 1,.word⟩,
  ⟨"g",id 2,.function .word .word⟩,⟨"y",id 3,.word⟩,⟨"c",id 4,.bool⟩],by change [id 0,id 1,id 2,id 3,id 4].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def comparison (isGe : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isGe then .greaterEqual else .less⟩ right⟩
private def source (isGe : Bool) (n k : Nat) := comparison isGe (calls false n) (calls true k)
private def comparisonCore : Core.Expr := .binary .wordGt (.var 0) (.var 1)
private def tailCore (k : Nat) : Core.Expr := .letE ((callCore true k).weakenAt 0) comparisonCore
private def ordered (n k : Nat) : Core.Expr := .letE (callCore false n) (tailCore k)
private def core (isGe : Bool) (n k : Nat) : Core.Expr := if isGe then .unary .boolNot (ordered n k) else ordered n k
private theorem oldLeaf (key : Key) :
    LocalComputationElaborates inputs.names inputs.context (ref key) (.var (index key)) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (key : Key) :
    RecursiveLocalComputationHasType inputs.names inputs.context (ref key) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callsElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .word := by
  induction n with
  | zero => cases side <;> exact (oldLeaf _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf _).toRecursiveLocalComputation) ih
private theorem callsTyped (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .word := by
  induction n with
  | zero => cases side <;> exact leafTyped _
  | succ n ih => exact .application (by cases side <;> exact leafTyped _) ih
private theorem elaboration (isGe : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isGe n k) (core isGe n k) .bool := by
  cases isGe; exact .less (callsElab false n) (callsElab true k); exact .greaterEqual (callsElab false n) (callsElab true k)
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  x : Core.Word
  y : Core.Word
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def childWord (a : Actual) (side : Bool) := if side then a.y else a.x
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def actual (a : Actual) : Key → Core.Value
  | .f => .closure .word .word (delay a.m 0) a.leftCapture | .x => .word a.x
  | .g => .closure .word .word (delay a.t 0) a.rightCapture | .y => .word a.y | .c => .bool true
private def env (a : Actual) : Resolved.Environment :=
  [(id 0,actual a .f),(id 1,.word a.x),(id 2,actual a .g),(id 3,.word a.y),(id 4,.bool true)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def cost (isGe : Bool) (a : Actual) (n k : Nat) := charge n a.m+charge k a.t+(if isGe then 11 else 9)
private def compared (a : Actual) := decide (a.x < a.y)
private def result (isGe : Bool) (a : Actual) := Core.Value.bool (if isGe then !(compared a) else compared a)
private theorem atomCost (a : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names (env a) s (ref key) (actual a key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (value : Core.Value) (rest : Core.Environment) (s : Core.Store) (frames : List Core.Frame)
    (found : (value::rest)[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) (value::rest),frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i rest frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
        (.cons (.var rfl) (.cons .bindLet (ih (i+1) (value::rest) frames (by simpa using found))))
private theorem callsCost (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (calls side n) (.word (childWord a side)) s (charge n (depth a side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .x s)
      · simpa [calls,charge,actual,childWord] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost a .y s)
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost a _ s)) ih
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem callsPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env a).values,frames,s⟩ ⟨.ret (.word (childWord a side)),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl)
private theorem shiftedPath (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (bound : Core.Value) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval ((callCore side n).weakenAt 0) (bound::(env a).values),frames,s⟩ ⟨.ret (.word (childWord a side)),frames,s⟩ := by
  induction n generalizing frames with
  | zero => cases side <;> simp only [charge,Nat.zero_mul,Nat.zero_add,callCore,Core.Expr.weakenAt] <;> exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]
      have body := delayed (depth a side) 0 (.word (childWord a side)) (capture a side) s [] rfl
      cases side <;> simp only [callCore,Core.Expr.weakenAt] <;>
        exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _) body
private theorem counted (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe n k) (result isGe a) s (cost isGe a n k) := by
  cases isGe; exact .less (callsCost a false n s) (callsCost a true k s); exact .greaterEqual (callsCost a false n s) (callsCost a true k s)
private theorem orderedManual (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n a.m+charge k a.t+9) ⟨.eval (ordered n k) (env a).values,frames,s⟩ ⟨.ret (.bool (compared a)),frames,s⟩ := by
  simpa [ordered,tailCore,comparisonCore,depth,childWord,Nat.add_assoc] using
    CostStepComposition.letE (callsPath a false n s _)
      (CostStepComposition.letE (shiftedPath a true k s (.word a.x) _)
        (CostStepComposition.binary (op := .wordGt) (.cons (.var rfl) .refl) (.cons (.var rfl) .refl) rfl))
private theorem manual (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isGe a n k) ⟨.eval (core isGe n k) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  cases isGe
  · exact orderedManual a n k s frames
  · simpa [cost,core,result,Nat.add_assoc] using CostStepComposition.unary (op := .boolNot) (orderedManual a n k s _) rfl

theorem original_ordered_word_static (isGe : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isGe n k) = some (core isGe n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isGe n k) .bool ∧ Core.HasType inputs.context.values (core isGe n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isGe n k) .bool := by
    cases isGe; exact .less (callsTyped false n) (callsTyped true k); exact .greaterEqual (callsTyped false n) (callsTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isGe n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isGe n k).core_hasType⟩

theorem actual_words_and_exact_paths (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source isGe n k) (result isGe a) s ∧
    Core.Evaluates (env a).values s (core isGe n k) (result isGe a) s ∧
    Core.Steps (cost isGe a n k) ⟨.eval (core isGe n k) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isGe a n k s⟩
  have fromManual := ((elaboration isGe n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr (manual isGe a n k s [])
  exact ⟨raw,((elaboration isGe n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isGe n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe n k) value finalStore steps) :
    value = result isGe a ∧ finalStore = s ∧ steps = charge n a.m+charge k a.t+(if isGe then 11 else 9) :=
  other.deterministic (counted isGe a n k s)

theorem arbitrary_caller_insertion (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core isGe n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost isGe a n k) ⟨.eval ((core isGe n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have literal : RecursiveLocalComputationFragment (ordered n k) :=
    .letE (callsElab false n).core_fragment
      (.letE ((callsElab true k).core_fragment.weakenAt 0) (.pure (.binary .var .var)))
  have fragment : RecursiveLocalComputationFragment (core isGe n k) := by
    cases isGe; exact literal; exact .unary literal
  have original := Core.steps_from_initial_sound (manual isGe a n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost isGe a n k) (.initial (core isGe n k) (leading++suffix) s) (.final (result isGe a) s) := by rw [split]; exact manual isGe a n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩
private def outer (isGe : Bool) : List Core.Frame := if isGe then [.unaryApply .boolNot] else []
private def first (isGe : Bool) (a : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),.letBody (tailCore k) (env a).values::outer isGe,s⟩
private def second (isGe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.y),.letBody comparisonCore (.word a.x::(env a).values)::outer isGe,s⟩
private def pending (isGe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),.binaryApply .wordGt (.word a.y)::outer isGe,s⟩
private theorem beginPath (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) {steps : Nat} {cp : Core.State}
    (path : Core.Steps steps ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ cp) :
    Core.Steps (steps+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) cp := by
  cases isGe
  · simpa [core,outer,Core.State.initial] using path
  · simpa [core,outer,Core.State.initial,Nat.add_comm] using Core.Steps.cons .enterUnary path
theorem generated_bindings_and_comparison_checkpoints (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+1+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (first isGe a k s) ∧
    Core.runStateful (charge n a.m+charge k a.t+3+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (second isGe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+8+(if isGe then 1 else 0)) (.initial (core isGe n k) (env a).values s) = .outOfFuel (pending isGe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+10) (.initial (core true n k) (env a).values s) =
      .outOfFuel ⟨.ret (.bool (compared a)),[.unaryApply .boolNot],s⟩ := by
  have p1 : Core.Steps (charge n a.m+1) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (first isGe a k s) := by
    simpa [ordered,first,depth,childWord,Nat.add_comm] using Core.Steps.cons .enterLet (callsPath a false n s _)
  have p2 : Core.Steps (charge n a.m+charge k a.t+3) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (second isGe a s) := by
    have count : charge n a.m+charge k a.t+3 = (charge n a.m+1)+((charge k a.t+1)+1) := by omega
    rw [count]
    exact p1.trans (.cons .bindLet (.cons .enterLet (shiftedPath a true k s (.word a.x) _)))
  have p3 : Core.Steps (charge n a.m+charge k a.t+8) ⟨.eval (ordered n k) (env a).values,outer isGe,s⟩ (pending isGe a s) := by
    simpa [second,pending,comparisonCore,Nat.add_assoc] using
      p2.trans (.cons .bindLet (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons (.var rfl) .refl)))))
  refine ⟨Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p1) (Core.advance_next_iff.mpr .bindLet),
    Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p2) (Core.advance_next_iff.mpr .bindLet),
    Core.runStateful_outOfFuel_complete (beginPath isGe a n k s p3) (Core.advance_next_iff.mpr (.applyBinary rfl)),?_⟩
  apply Core.runStateful_outOfFuel_complete
  · simpa [core,Core.State.initial,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary (orderedManual a n k s [.unaryApply .boolNot])
  · exact Core.advance_next_iff.mpr (.applyUnary rfl)

theorem all_fuels_residual_and_full_resume (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isGe n k) (env a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isGe n k) (env a).values s) = .done (result isGe a) s ↔ cost isGe a n k ≤ fuel) ∧
    spent < cost isGe a n k ∧ Core.Steps (cost isGe a n k-spent) cp (.final (result isGe a) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isGe n k) (env a).values s) := by
  have path := manual isGe a n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (isGe : Bool) (limit : Nat) (x y : Core.Word) (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe 1 1) (result isGe a) s (cost isGe a 1 1) ∧ limit < cost isGe a 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  exact ⟨a,counted isGe a 1 1 s,by cases isGe <;> simp [cost,charge,a] <;> omega⟩
private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_with_skipped_original_operand (isGe : Bool) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
  have old : LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe
    · exact .pure (.less (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
    · exact .pure (.greaterEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isGe (guarded skipped) (ref .y)) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe
    · exact .less (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
    · exact .greaterEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old,same.2.2 ▸ new⟩
private def body (isGe : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isGe n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isGe : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isGe n k) (.letE (core isGe n k) (.var 0)) .bool :=
  .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) (elaboration isGe n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe n k) (result isGe a) s (cost isGe a n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isGe a n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isGe a n k+3) ⟨.eval (.letE (core isGe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isGe a n k s (.letBody (.var 0) (env a).values::frames)) (.cons (.var rfl) .refl)
private theorem oldElab (isGe : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isGe 0 0) (core isGe 0 0) .bool := by
  cases oldLeaf .x with
  | pure lr ll lt =>
      cases oldLeaf .y with
      | pure rr rl rt =>
          cases isGe
          · exact .pure (.less lr rr) (.wordLt ll rl) (.wordLt lt rt)
          · exact .pure (.greaterEqual lr rr) (.unary (.wordLt ll rl)) (.unary (.wordLt lt rt))
      | application child => cases child
  | application child => cases child
theorem old_original_body_embeddings (isGe : Bool) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isGe 0 0) (.letE (core isGe 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe 0 0) (result isGe a) s (if isGe then 16 else 14) := by
  have oldStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isGe 0 0) (.letE (core isGe 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) (oldElab isGe)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have child : LocalComputationEvaluatesWithCost inputs.names (env a) s (source isGe 0 0) (result isGe a) s (if isGe then 13 else 11) := by
    cases isGe; exact .pure (.less (atomCost a .x s) (atomCost a .y s)); exact .pure (.greaterEqual (atomCost a .x s) (atomCost a .y s))
  have oldCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe 0 0) (result isGe a) s (if isGe then 16 else 14) := by
    cases isGe <;> exact .inferred child (.expression (.pure (.identifier .head .head)))
  exact ⟨oldStatic.toRecursiveComputationReturnTree,oldCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isGe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isGe n k) = some (.letE (core isGe n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isGe n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isGe n k) (result isGe a) s (cost isGe a n k+3) ∧
    Core.Steps (cost isGe a n k+3) ⟨.eval (.letE (core isGe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isGe a),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isGe n k) (environment := env a) rfl).mpr (bodyManual isGe a n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isGe n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isGe n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isGe a n k s) (bodyElab isGe n k) rfl frames⟩

end Tests.FrontendRecursiveOrderedComparison
