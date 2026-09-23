import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Core.FuelResumptionProperties

/-! Fixed short-circuit source retains arbitrary actual RHS values and captures.
Only this explicitly store-free delay fixture has an unchanged final store. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveLazyComputation
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Lazy", by decide⟩], by decide⟩⟩, 59⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner, n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lazy.sol"⟩, 0, 1024⟩
private inductive Key | f | c | g | x
private def index : Key → Nat | .f => 0 | .c => 1 | .g => 2 | .x => 3
private def name : Key → String | .f => "f" | .c => "c" | .g => "g" | .x => "x"
private def typeOf : Key → Core.Ty | .f | .g => .function .bool .bool | _ => .bool
private def inputs : LocalTypeInputs := ⟨[⟨"f",id 0,.function .bool .bool⟩,⟨"c",id 1,.bool⟩,
  ⟨"g",id 2,.function .bool .bool⟩,⟨"x",id 3,.bool⟩], by change [id 0,id 1,id 2,id 3].Nodup; decide⟩
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls (side : Bool) : Nat → Syntax.Expr
  | 0 => ref (if side then .x else .c)
  | n+1 => ⟨span,.call (ref (if side then .g else .f)) ⟨span,[calls side n]⟩⟩
private def callCore (side : Bool) : Nat → Core.Expr
  | 0 => .var (if side then 3 else 1)
  | n+1 => .apply (.var (if side then 2 else 0)) (callCore side n)
private def lazySource (isOr : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isOr then .logicalOr else .logicalAnd⟩ right⟩
private def source (isOr : Bool) (n k : Nat) := lazySource isOr (calls false n) (calls true k)
private def core (isOr : Bool) (n k : Nat) : Core.Expr :=
  if isOr then .ifE (callCore false n) (.bool true) (callCore true k) else .ifE (callCore false n) (callCore true k) (.bool false)
private theorem oldLeaf (key : Key) :
    LocalComputationElaborates inputs.names inputs.context (ref key) (.var (index key)) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem leafTyped (key : Key) :
    RecursiveLocalComputationHasType inputs.names inputs.context (ref key) (typeOf key) :=
  .pure (.identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callElab (side : Bool) (n : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (calls side n) (callCore side n) .bool := by
  induction n with
  | zero => cases side <;> exact (oldLeaf _).toRecursiveLocalComputation
  | succ n ih => exact .application (by cases side <;> exact (oldLeaf _).toRecursiveLocalComputation) ih
private theorem callTyped (side : Bool) (n : Nat) :
    RecursiveLocalComputationHasType inputs.names inputs.context (calls side n) .bool := by
  induction n with
  | zero => cases side <;> exact leafTyped _
  | succ n ih => exact .application (by cases side <;> exact leafTyped _) ih
private theorem elaboration (isOr : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isOr n k) (core isOr n k) .bool := by
  cases isOr
  · exact .logicalAnd (callElab false n) (callElab true k)
  · exact .logicalOr (callElab false n) (callElab true k)
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  choice : Bool
  right : Core.Value
  leftDelay : Nat
  rightDelay : Nat
  leftCapture : Core.Environment
  rightCapture : Core.Environment
private def actual (v : Actual) : Key → Core.Value
  | .f => .closure .bool .bool (delay v.leftDelay 0) v.leftCapture
  | .c => .bool v.choice
  | .g => .closure .bool .bool (delay v.rightDelay 0) v.rightCapture
  | .x => v.right
private def env (v : Actual) : Resolved.Environment :=
  [(id 0,actual v .f),(id 1,.bool v.choice),(id 2,actual v .g),(id 3,v.right)]
private def childValue (v : Actual) (side : Bool) := if side then v.right else Core.Value.bool v.choice
private def childDelay (v : Actual) (side : Bool) := if side then v.rightDelay else v.leftDelay
private def childCapture (v : Actual) (side : Bool) := if side then v.rightCapture else v.leftCapture
private def charge (n m : Nat) := n*(3*m+5)+1
private def selected (isOr choice : Bool) := choice != isOr
private def result (isOr : Bool) (v : Actual) := if selected isOr v.choice then v.right else Core.Value.bool v.choice
private def cost (isOr : Bool) (v : Actual) (n k : Nat) :=
  charge n v.leftDelay + if selected isOr v.choice then charge k v.rightDelay+2 else 3
private theorem atomCost (v : Actual) (key : Key) (s : Core.Store) :
    LocalExpressionEvaluatesWithCost inputs.names (env v) s (ref key) (actual v key) s 1 :=
  .identifier (id := id (index key)) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl))
private theorem delayed (m i : Nat) (environment : Core.Environment) (value : Core.Value) (s : Core.Store) (frames : List Core.Frame)
    (found : environment[i]? = some value) :
    Core.Steps (3*m+1) ⟨.eval (delay m i) environment,frames,s⟩ ⟨.ret value,frames,s⟩ := by
  induction m generalizing i environment frames with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases environment with
      | nil => simp at found
      | cons head rest =>
          simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i+1) (head::head::rest) frames (by simpa using found))))
private theorem callCost (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (calls side n) (childValue v side) s (charge n (childDelay v side)) := by
  induction n with
  | zero =>
      cases side
      · simpa [calls,charge,actual,childValue] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost v .c s)
      · simpa [calls,charge,actual,childValue] using RecursiveLocalComputationEvaluatesWithCost.pure (atomCost v .x s)
  | succ n ih =>
      have count : charge (n+1) (childDelay v side) = 1+charge n (childDelay v side)+(3*childDelay v side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (.pure (by cases side <;> exact atomCost v _ s)) ih
        (delayed (childDelay v side) 0 (childValue v side::childCapture v side) (childValue v side) s [] rfl)
private theorem callPath (v : Actual) (side : Bool) (n : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (charge n (childDelay v side)) ⟨.eval (callCore side n) (env v).values,frames,s⟩ ⟨.ret (childValue v side),frames,s⟩ := by
  induction n generalizing frames with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var (by cases side <;> rfl)) .refl
  | succ n ih =>
      have count : charge (n+1) (childDelay v side) = 1+charge n (childDelay v side)+(3*childDelay v side+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var (by cases side <;> rfl)) .refl) (ih _)
        (delayed (childDelay v side) 0 (childValue v side::childCapture v side) (childValue v side) s [] rfl)
private theorem counted (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr n k) (result isOr v) s (cost isOr v n k) := by
  cases isOr <;> cases chosen : v.choice
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay] using RecursiveLocalComputationEvaluatesWithCost.andFalse (by simpa [childValue,childDelay,chosen] using callCost v false n s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using RecursiveLocalComputationEvaluatesWithCost.andTrue (by simpa [childValue,childDelay,chosen] using callCost v false n s) (callCost v true k s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using RecursiveLocalComputationEvaluatesWithCost.orFalse (by simpa [childValue,childDelay,chosen] using callCost v false n s) (callCost v true k s)
  · simpa [source,lazySource,result,cost,selected,chosen,childValue,childDelay] using RecursiveLocalComputationEvaluatesWithCost.orTrue (by simpa [childValue,childDelay,chosen] using callCost v false n s)
private theorem manual (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isOr v n k) ⟨.eval (core isOr n k) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  cases isOr <;> cases chosen : v.choice
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifFalse (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (.cons .bool .refl)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifTrue (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (callPath v true k s frames)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifFalse (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (callPath v true k s frames)
  · simpa [core,result,cost,selected,chosen,childValue,childDelay,Nat.add_assoc] using CostStepComposition.ifTrue (by simpa [childValue,childDelay,chosen] using callPath v false n s _) (.cons .bool .refl)

theorem original_bool_static_children (isOr : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isOr n k) = some (core isOr n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isOr n k) .bool ∧ Core.HasType inputs.context.values (core isOr n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isOr n k) .bool := by
    cases isOr; exact .logicalAnd (callTyped false n) (callTyped true k); exact .logicalOr (callTyped false n) (callTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isOr n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isOr n k).core_hasType⟩

theorem actual_rhs_value_and_exact_paths (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env v) s (source isOr n k) (result isOr v) s ∧
    Core.Evaluates (env v).values s (core isOr n k) (result isOr v) s ∧
    Core.Steps (cost isOr v n k) ⟨.eval (core isOr n k) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isOr v n k s⟩
  have fromManual := ((elaboration isOr n k).evaluatesWithCost_iff_steps (environment := env v) rfl).mpr (manual isOr v n k s [])
  exact ⟨raw,((elaboration isOr n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isOr n k) rfl frames⟩

theorem actual_value_store_and_cost_unique (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr n k) value finalStore steps) :
    value = result isOr v ∧ finalStore = s ∧ steps = cost isOr v n k :=
  other.deterministic (counted isOr v n k s)

theorem skipped_original_rhs_has_no_raw_premise (isOr : Bool) (v : Actual) (n : Nat) (s : Core.Store)
    (skipped : Syntax.Expr) (choice : v.choice = isOr) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (lazySource isOr (calls false n) skipped) (.bool isOr) s (charge n v.leftDelay+3) := by
  cases isOr
  · exact .andFalse (by simpa [childValue,childDelay,choice] using callCost v false n s)
  · exact .orTrue (by simpa [childValue,childDelay,choice] using callCost v false n s)

theorem arbitrary_caller_insertion (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env v).values) :
    RecursiveLocalComputationFragment ((core isOr n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost isOr v n k) ⟨.eval ((core isOr n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have fragment := (elaboration isOr n k).core_fragment
  have original := Core.steps_from_initial_sound (manual isOr v n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost isOr v n k) (.initial (core isOr n k) (leading++suffix) s) (.final (result isOr v) s) := by rw [split]; exact manual isOr v n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def checkpoint (isOr : Bool) (v : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool v.choice),[if isOr then .ifBranches (.bool true) (callCore true k) (env v).values else .ifBranches (callCore true k) (.bool false) (env v).values],s⟩
theorem genuine_left_completed_checkpoint (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n v.leftDelay+1) (.initial (core isOr n k) (env v).values s) = .outOfFuel (checkpoint isOr v k s) := by
  have beforeChoice : Core.Steps (charge n v.leftDelay+1) (.initial (core isOr n k) (env v).values s) (checkpoint isOr v k s) := by
    cases isOr <;> exact .cons .enterIf (callPath v false n s _)
  cases isOr <;> cases chosen : v.choice
  all_goals apply Core.runStateful_outOfFuel_complete beforeChoice; apply Core.advance_next_iff.mpr; simp only [checkpoint,chosen,Bool.false_eq_true,↓reduceIte]; first | exact .chooseFalse | exact .chooseTrue

theorem all_fuels_residual_and_full_resume (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isOr n k) (env v).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isOr n k) (env v).values s) = .done (result isOr v) s ↔ cost isOr v n k ≤ fuel) ∧
    spent < cost isOr v n k ∧ Core.Steps (cost isOr v n k-spent) cp (.final (result isOr v) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isOr n k) (env v).values s) := by
  have path := manual isOr v n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem selected_rhs_cost_unbounded_but_skipping_ignores_it (isOr : Bool) (limit : Nat) (value : Core.Value) (captures : Core.Environment) (s : Core.Store) :
    (∃ v : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 1 1) value s (cost isOr v 1 1) ∧ limit < cost isOr v 1 1) ∧
    ∀ v : Actual, v.choice = isOr → ∀ k m, cost isOr {v with rightDelay := m} 1 k = charge 1 v.leftDelay+3 := by
  constructor
  · let v : Actual := ⟨!isOr,value,0,limit,[],captures⟩
    refine ⟨v,?_,?_⟩
    · simpa [result,selected,v] using counted isOr v 1 1 s
    · cases isOr <;> simp [cost,selected,charge,v] <;> omega
  · intro v choice k m; simp [cost,selected,choice]

private def body (isOr : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isOr n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isOr : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isOr n k) (.letE (core isOr n k) (.var 0)) .bool :=
  .inferred (elaboration isOr n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr n k) (result isOr v) s (cost isOr v n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isOr v n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost isOr v n k+3) ⟨.eval (.letE (core isOr n k) (.var 0)) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isOr v n k s (.letBody (.var 0) (env v).values::frames)) (.cons (.var rfl) .refl)

private theorem oldElab (isOr : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isOr 0 0) (core isOr 0 0) .bool := by
  cases oldLeaf .c with
  | pure leftResolution leftLowered leftTyped =>
      cases oldLeaf .x with
      | pure rightResolution rightLowered rightTyped =>
          cases isOr
          · exact .pure (.logicalAnd leftResolution rightResolution) (.ifE leftLowered rightLowered .bool) (.ifE leftTyped rightTyped .bool)
          · exact .pure (.logicalOr leftResolution rightResolution) (.ifE leftLowered .bool rightLowered) (.ifE leftTyped .bool rightTyped)
      | application child => cases child
  | application child => cases child
private theorem oldCost (isOr : Bool) (v : Actual) (s : Core.Store) :
    LocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 := by
  cases isOr <;> cases chosen : v.choice
  · simpa [source,lazySource,result,selected,chosen,calls] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.andFalse (by simpa [actual,chosen] using atomCost v .c s))
  · simpa [source,lazySource,result,selected,chosen,calls,actual] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.andTrue (by simpa [actual,chosen] using atomCost v .c s) (atomCost v .x s))
  · simpa [source,lazySource,result,selected,chosen,calls,actual] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.orFalse (by simpa [actual,chosen] using atomCost v .c s) (atomCost v .x s))
  · simpa [source,lazySource,result,selected,chosen,calls] using LocalComputationEvaluatesWithCost.pure
      (LocalExpressionEvaluatesWithCost.orTrue (by simpa [actual,chosen] using atomCost v .c s))

theorem old_pure_overlap_and_original_body_embeddings (isOr : Bool) (v : Actual) (s : Core.Store) :
    LocalComputationElaborates inputs.names inputs.context (source isOr 0 0) (core isOr 0 0) .bool ∧
    LocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 ∧
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isOr 0 0) (.letE (core isOr 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr 0 0) (result isOr v) s 7 := by
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env v) s (source isOr 0 0) (result isOr v) s 4 := by
    simpa [cost,charge] using counted isOr v 0 0 s
  have same := new.deterministic (oldCost isOr v s).toRecursiveLocalComputation
  have originalStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isOr 0 0) (.letE (core isOr 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","c","g","x"]; decide) (oldElab isOr)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have originalCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr 0 0) (result isOr v) s 7 :=
    .inferred (oldCost isOr v s) (.expression (.pure (.identifier .head .head)))
  exact ⟨oldElab isOr,oldCost isOr v s,same.2.2 ▸ new,originalStatic.toRecursiveComputationReturnTree,originalCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isOr : Bool) (v : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isOr n k) = some (.letE (core isOr n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isOr n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env v) s (body isOr n k) (result isOr v) s (cost isOr v n k+3) ∧
    Core.Steps (cost isOr v n k+3) ⟨.eval (.letE (core isOr n k) (.var 0)) (env v).values,frames,s⟩ ⟨.ret (result isOr v),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isOr n k) (environment := env v) rfl).mpr (bodyManual isOr v n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isOr n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isOr n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isOr v n k s) (bodyElab isOr n k) rfl frames⟩

end Tests.FrontendRecursiveLazyComputation
