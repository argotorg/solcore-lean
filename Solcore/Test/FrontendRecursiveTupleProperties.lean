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

/-! Flat tuples of arbitrary length have literal right-associated paths, without
a terminal Unit. Store invariance below is only for the explicit delayed bodies;
arbitrary static component tags do not constrain the actual opaque payloads. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveTuple
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Tuple",by decide⟩],by decide⟩⟩,64⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"tuple.sol"⟩,0,1024⟩
private def tupleSpan : Syntax.SourceSpan := ⟨span.source,1,1023⟩
private inductive Key | f | x | g | y | c
private def index : Key → Nat | .f => 0 | .x => 1 | .g => 2 | .y => 3 | .c => 4
private def name : Key → String | .f => "f" | .x => "x" | .g => "g" | .y => "y" | .c => "c"
private def typeOf (A B : Core.Ty) : Key → Core.Ty
  | .f => .function A A | .x => A | .g => .function B B | .y => B | .c => .bool
private def inputs (A B : Core.Ty) : LocalTypeInputs := ⟨[⟨"f",id 0,.function A A⟩,⟨"x",id 1,A⟩,
  ⟨"g",id 2,.function B B⟩,⟨"y",id 3,B⟩,⟨"c",id 4,.bool⟩],by change [id 0,id 1,id 2,id 3,id 4].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .y else .x)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def tailElements (left right : Syntax.Expr) : Nat → List Syntax.Expr
  | 0 => [right] | r+1 => left :: tailElements left right r
private def elements (left right : Syntax.Expr) (r : Nat) := left :: tailElements left right r
private def tuple (left right : Syntax.Expr) (r : Nat) : Syntax.Expr := ⟨span,.tuple ⟨tupleSpan,elements left right r⟩⟩
private def source (r n k : Nat) := tuple (calls false n) (calls true k) r
private def chain {α : Type} (pair : α → α → α) (left right : α) : Nat → α
  | 0 => pair left right | r+1 => pair left (chain pair left right r)
private def core (r n k : Nat) := chain Core.Expr.pair (callCore false n) (callCore true k) r
private def type (A B : Core.Ty) (r : Nat) := chain Core.Ty.product A B r
private theorem oldLeaf (A B : Core.Ty) (key : Key) :
    LocalComputationElaborates (inputs A B).names (inputs A B).context (ref key) (.var (index key)) (typeOf A B key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (A B : Core.Ty) (key : Key) :
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (ref key) (typeOf A B key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callsElab (A B : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates (inputs A B).names (inputs A B).context (calls side n) (callCore side n) (if side then B else A) := by
  induction n with
  | zero => cases side <;> exact (oldLeaf A B _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf A B _).toRecursiveLocalComputation) ih
private theorem callsTyped (A B : Core.Ty) (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (calls side n) (if side then B else A) := by
  induction n with
  | zero => cases side <;> exact leafTyped A B _
  | succ n ih => exact .application (by cases side <;> exact leafTyped A B _) ih
private theorem elaboration (A B : Core.Ty) (r n k : Nat) :
    RecursiveLocalComputationElaborates (inputs A B).names (inputs A B).context (source r n k) (core r n k) (type A B r) := by
  induction r with
  | zero => exact .pair (callsElab A B false n) (callsElab A B true k)
  | succ r ih => cases r <;> exact .many (callsElab A B false n) ih
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  x : Core.Value
  y : Core.Value
  m : Nat
  t : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def payload (a : Actual) (side : Bool) := if side then a.y else a.x
private def depth (a : Actual) (side : Bool) := if side then a.t else a.m
private def capture (a : Actual) (side : Bool) := if side then a.rightCapture else a.leftCapture
private def actual (A B : Core.Ty) (a : Actual) : Key → Core.Value
  | .f => .closure A A (delay a.m 0) a.leftCapture | .x => a.x
  | .g => .closure B B (delay a.t 0) a.rightCapture | .y => a.y | .c => .bool true
private def env (A B : Core.Ty) (a : Actual) : Resolved.Environment :=
  [(id 0,actual A B a .f),(id 1,a.x),(id 2,actual A B a .g),(id 3,a.y),(id 4,.bool true)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def cost (a : Actual) (r n k : Nat) := (r+1)*(charge n a.m+3)+charge k a.t
private def result (a : Actual) (r : Nat) := chain Core.Value.pair a.x a.y r
private theorem atomCost (A B : Core.Ty) (a : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost (inputs A B).names (env A B a) s (ref key) (actual A B a key) s 1 :=
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
private theorem callsCost (A B : Core.Ty) (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (calls side n) (payload a side) s (charge n (depth a side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,payload,charge,actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost A B a .x s)
      · simpa [calls,payload,charge,actual] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost A B a .y s)
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (parameterType := if side then B else A) (resultType := if side then B else A)
        (.pure (by cases side; exact atomCost A B a .f s; exact atomCost A B a .g s)) ih
        (delayed (depth a side) 0 (payload a side) (capture a side) s [] rfl)
private theorem callsPath (A B : Core.Ty) (a : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (depth a side)) ⟨.eval (callCore side n) (env A B a).values,frames,s⟩ ⟨.ret (payload a side),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (depth a side) = 1+charge n (depth a side)+(3*depth a side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (parameterType := if side then B else A) (resultType := if side then B else A)
        (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (depth a side) 0 (payload a side) (capture a side) s [] rfl)
private theorem counted (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r n k) (result a r) s (cost a r n k) := by
  induction r with
  | zero => simpa [source,tuple,elements,tailElements,result,chain,payload,cost,depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      RecursiveLocalComputationEvaluatesWithCost.pair (callsCost A B a false n s) (callsCost A B a true k s)
  | succ r ih =>
      have count : cost a (r+1) n k = charge n a.m+cost a r n k+3 := by simp [cost,Nat.add_mul]; omega
      rw [count]; cases r <;> exact .many (callsCost A B a false n s) ih
private theorem pairPath {environment : Core.Environment} {s t u : Core.Store} {left right : Core.Expr}
    {x y : Core.Value} {frames : List Core.Frame} {l r : Nat}
    (lp : Core.Steps l ⟨.eval left environment,.pairRight right environment::frames,s⟩ ⟨.ret x,.pairRight right environment::frames,t⟩)
    (rp : Core.Steps r ⟨.eval right environment,.pairApply x::frames,t⟩ ⟨.ret y,.pairApply x::frames,u⟩) :
    Core.Steps (l+r+3) ⟨.eval (.pair left right) environment,frames,s⟩ ⟨.ret (.pair x y),frames,u⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair (lp.trans (.cons .enterPairRight (rp.trans (.cons .applyPair .refl))))
private theorem manual (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a r n k) ⟨.eval (core r n k) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  induction r generalizing frames with
  | zero => simpa [core,result,chain,payload,cost,depth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using pairPath (frames := frames) (callsPath A B a false n s _) (callsPath A B a true k s _)
  | succ r ih =>
      have count : cost a (r+1) n k = charge n a.m+cost a r n k+3 := by simp [cost,Nat.add_mul]; omega
      rw [count]; exact pairPath (callsPath A B a false n s _) (ih _)

theorem original_flat_tuple_static (A B : Core.Ty) (r n k : Nat) :
    (elements (calls false n) (calls true k) r).length = r+2 ∧
    elaborateRecursiveLocalComputation? (inputs A B).names (inputs A B).context (source r n k) = some (core r n k,type A B r) ∧
    RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (source r n k) (type A B r) ∧
    Core.HasType (inputs A B).context.values (core r n k) (type A B r) := by
  have typed : RecursiveLocalComputationHasType (inputs A B).names (inputs A B).context (source r n k) (type A B r) := by
    induction r with
    | zero => exact .pair (callsTyped A B false n) (callsTyped A B true k)
    | succ r ih => cases r <;> exact .many (callsTyped A B false n) ih
  have length : (elements (calls false n) (calls true k) r).length = r+2 := by
    clear typed
    simp only [elements,List.length_cons]
    have tail : (tailElements (calls false n) (calls true k) r).length = r+1 := by induction r <;> simp_all [tailElements]
    omega
  exact ⟨length,elaborateRecursiveLocalComputation?_iff.mpr (elaboration A B r n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration A B r n k).core_hasType⟩

theorem actual_opaque_values_and_exact_paths (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates (inputs A B).names (env A B a) s (source r n k) (result a r) s ∧
    Core.Evaluates (env A B a).values s (core r n k) (result a r) s ∧
    Core.Steps (cost a r n k) ⟨.eval (core r n k) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted A B a r n k s⟩
  have fromManual := ((elaboration A B r n k).evaluatesWithCost_iff_steps (environment := env A B a) rfl).mpr (manual A B a r n k s [])
  exact ⟨raw,((elaboration A B r n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration A B r n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r n k) value finalStore steps) :
    value = result a r ∧ finalStore = s ∧ steps = (r+1)*(charge n a.m+3)+charge k a.t :=
  other.deterministic (counted A B a r n k s)

theorem arbitrary_caller_insertion (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env A B a).values) :
    RecursiveLocalComputationFragment ((core r n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a r n k) ⟨.eval ((core r n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have fragment : RecursiveLocalComputationFragment (core r n k) := by
    induction r with
    | zero => exact .pair (callsElab A B false n).core_fragment (callsElab A B true k).core_fragment
    | succ r ih => exact .pair (callsElab A B false n).core_fragment ih
  have original := Core.steps_from_initial_sound (manual A B a r n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost a r n k) (.initial (core r n k) (leading++suffix) s) (.final (result a r) s) := by rw [split]; exact manual A B a r n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def tailCore (r n k : Nat) := match r with | 0 => callCore true k | r+1 => core r n k
private def tailValue (a : Actual) (r : Nat) := match r with | 0 => a.y | r+1 => result a r
private def tailCost (a : Actual) (r n k : Nat) := match r with | 0 => charge k a.t | r+1 => cost a r n k
private def first (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret a.x,[.pairRight (tailCore r n k) (env A B a).values],s⟩
private def second (a : Actual) (r : Nat) (s : Core.Store) : Core.State := ⟨.ret (tailValue a r),[.pairApply a.x],s⟩
theorem actual_pair_frames_are_checkpoints (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+1) (.initial (core r n k) (env A B a).values s) = .outOfFuel (first A B a r n k s) ∧
    Core.runStateful (cost a r n k-1) (.initial (core r n k) (env A B a).values s) = .outOfFuel (second a r s) := by
  have p1 : Core.Steps (charge n a.m+1) (.initial (core r n k) (env A B a).values s) (first A B a r n k s) := by
    have path := Core.Steps.cons .enterPair (callsPath A B a false n s [.pairRight (tailCore r n k) (env A B a).values])
    cases r <;> simpa [core,chain,tailCore,first,Core.State.initial,payload,depth] using path
  have tail : Core.Steps (tailCost a r n k) ⟨.eval (tailCore r n k) (env A B a).values,[.pairApply a.x],s⟩ (second a r s) := by
    cases r; exact callsPath A B a true k s _; exact manual A B a _ n k s _
  have count : cost a r n k-1 = (charge n a.m+1)+(tailCost a r n k+1) := by
    cases r <;> simp [cost,tailCost,Nat.add_mul] <;> omega
  refine ⟨Core.runStateful_outOfFuel_complete p1 (Core.advance_next_iff.mpr .enterPairRight),?_⟩
  apply Core.runStateful_outOfFuel_complete (by rw [count]; exact p1.trans (.cons .enterPairRight tail))
  exact Core.advance_next_iff.mpr .applyPair

theorem all_fuels_residual_and_full_resume (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core r n k) (env A B a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core r n k) (env A B a).values s) = .done (result a r) s ↔ cost a r n k ≤ fuel) ∧
    spent < cost a r n k ∧ Core.Steps (cost a r n k-spent) cp (.final (result a r) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core r n k) (env A B a).values s) := by
  have path := manual A B a r n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (A B : Core.Ty) (r limit : Nat) (x y : Core.Value)
    (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (source r 1 1) (result a r) s (cost a r 1 1) ∧ limit < cost a r 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  refine ⟨a,counted A B a r 1 1 s,?_⟩
  have enough : 3*limit+9 ≤ (r+1)*(3*limit+9) := by induction r <;> simp_all [Nat.add_mul] <;> omega
  simp [cost,charge,a,Nat.add_assoc]; omega
private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_keeps_unselected_original_syntax (A B : Core.Ty) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 ∧
    RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 := by
  have old : LocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 :=
    .pure (.pair (.ifTrue (atomCost A B a .c s) (atomCost A B a .x s)) (atomCost A B a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost (inputs A B).names (env A B a) s (tuple (guarded skipped) (ref .y) 0) (.pair a.x a.y) s 8 :=
    .pair (.ifTrue (.pure (atomCost A B a .c s)) (.pure (atomCost A B a .x s))) (.pure (atomCost A B a .y s))
  exact ⟨old,(new.deterministic old.toRecursiveLocalComputation).2.2 ▸ new⟩
private def body (r n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source r n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (A B : Core.Ty) (r n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs A B) (body r n k) (.letE (core r n k) (.var 0)) (type A B r) :=
  .inferred (elaboration A B r n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body r n k) (result a r) s (cost a r n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted A B a r n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a r n k+3) ⟨.eval (.letE (core r n k) (.var 0)) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual A B a r n k s (.letBody (.var 0) (env A B a).values::frames)) (.cons (.var rfl) .refl)
theorem old_original_body_embeddings (A B : Core.Ty) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs A B) (body 0 0 0) (.letE (core 0 0 0) (.var 0)) (.product A B) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body 0 0 0) (.pair a.x a.y) s 8 := by
  have old : LocalComputationElaborates (inputs A B).names (inputs A B).context (source 0 0 0) (core 0 0 0) (.product A B) := by
    cases oldLeaf A B .x with
    | pure lr ll lt =>
        cases oldLeaf A B .y with
        | pure rr rl rt => exact .pure (.pair lr rr) (.pair ll rl) (.pair lt rt)
        | application child => cases child
    | application child => cases child
  have static : LocalComputationReturnTreeElaborates [] owner (inputs A B) (body 0 0 0) (.letE (core 0 0 0) (.var 0)) (.product A B) :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) old (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have counted : LocalComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body 0 0 0) (.pair a.x a.y) s 8 :=
    .inferred (.pure (.pair (atomCost A B a .x s) (atomCost A B a .y s))) (.expression (.pure (.identifier .head .head)))
  exact ⟨static.toRecursiveComputationReturnTree,counted.toRecursiveComputationReturnTree⟩
theorem shared_body_original_source_and_actual_cost (A B : Core.Ty) (a : Actual) (r n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner (inputs A B) (body r n k) = some (.letE (core r n k) (.var 0),type A B r) ∧
    Core.HasType (inputs A B).context.values (.letE (core r n k) (.var 0)) (type A B r) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs A B).names (env A B a) s (body r n k) (result a r) s (cost a r n k+3) ∧
    Core.Steps (cost a r n k+3) ⟨.eval (.letE (core r n k) (.var 0)) (env A B a).values,frames,s⟩ ⟨.ret (result a r),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab A B r n k) (environment := env A B a) rfl).mpr (bodyManual A B a r n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab A B r n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab A B r n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost A B a r n k s) (bodyElab A B r n k) rfl frames⟩

end Tests.FrontendRecursiveTuple
