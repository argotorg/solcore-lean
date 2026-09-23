import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Core.FuelResumptionProperties

/-! Original ordered comparisons have separate static, actual and manual paths.
Unchanged stores below belong only to the explicit store-free delayed bodies. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveNegatedComparison
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"Comparison",by decide⟩],by decide⟩⟩,60⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"comparison.sol"⟩,0,1024⟩
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
private def comparison (isLe : Bool) (left right : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.binary left ⟨⟨span.source,500,502⟩,if isLe then .lessEqual else .notEqual⟩ right⟩
private def op (isLe : Bool) : Core.BinaryOp := if isLe then .wordGt else .wordEq
private def source (isLe : Bool) (n k : Nat) := comparison isLe (calls false n) (calls true k)
private def core (isLe : Bool) (n k : Nat) : Core.Expr := .unary .boolNot (.binary (op isLe) (callCore false n) (callCore true k))
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
private theorem elaboration (isLe : Bool) (n k : Nat) :
    RecursiveLocalComputationElaborates inputs.names inputs.context (source isLe n k) (core isLe n k) .bool := by
  cases isLe; exact .notEqual (callsElab false n) (callsElab true k); exact .lessEqual (callsElab false n) (callsElab true k)
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
private def cost (a : Actual) (n k : Nat) := charge n a.m+charge k a.t+5
private def compared (isLe : Bool) (a : Actual) := if isLe then decide (a.x > a.y) else a.x == a.y
private def result (isLe : Bool) (a : Actual) := Core.Value.bool (!(compared isLe a))
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
private theorem counted (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe n k) (result isLe a) s (cost a n k) := by
  cases isLe; exact .notEqual (callsCost a false n s) (callsCost a true k s); exact .lessEqual (callsCost a false n s) (callsCost a true k s)
private theorem manual (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a n k) ⟨.eval (core isLe n k) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  simpa [cost,depth,core,result,Nat.add_assoc] using CostStepComposition.unary (op := .boolNot)
    (CostStepComposition.binary (op := op isLe) (result := .bool (compared isLe a))
      (callsPath a false n s _) (callsPath a true k s _) (by cases isLe <;> rfl)) rfl

theorem original_ordered_word_static (isLe : Bool) (n k : Nat) :
    elaborateRecursiveLocalComputation? inputs.names inputs.context (source isLe n k) = some (core isLe n k,.bool) ∧
    RecursiveLocalComputationHasType inputs.names inputs.context (source isLe n k) .bool ∧ Core.HasType inputs.context.values (core isLe n k) .bool := by
  have typed : RecursiveLocalComputationHasType inputs.names inputs.context (source isLe n k) .bool := by
    cases isLe; exact .notEqual (callsTyped false n) (callsTyped true k); exact .lessEqual (callsTyped false n) (callsTyped true k)
  exact ⟨elaborateRecursiveLocalComputation?_iff.mpr (elaboration isLe n k),
    recursiveLocalComputationHasType_iff_elaborates.mpr (recursiveLocalComputationHasType_iff_elaborates.mp typed),(elaboration isLe n k).core_hasType⟩

theorem actual_words_and_exact_paths (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    RecursiveLocalComputationEvaluates inputs.names (env a) s (source isLe n k) (result isLe a) s ∧
    Core.Evaluates (env a).values s (core isLe n k) (result isLe a) s ∧
    Core.Steps (cost a n k) ⟨.eval (core isLe n k) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have raw := recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,counted isLe a n k s⟩
  have fromManual := ((elaboration isLe n k).evaluatesWithCost_iff_steps (environment := env a) rfl).mpr (manual isLe a n k s [])
  exact ⟨raw,((elaboration isLe n k).evaluates_iff rfl).mp raw,fromManual.toStepsWithContinuation (elaboration isLe n k) rfl frames⟩

theorem actual_value_store_cost_jointly_unique (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    {value : Core.Value} {finalStore : Core.Store} {steps : Nat}
    (other : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe n k) value finalStore steps) :
    value = result isLe a ∧ finalStore = s ∧ steps = charge n a.m+charge k a.t+5 :=
  other.deterministic (counted isLe a n k s)

theorem arbitrary_caller_insertion (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix = (env a).values) :
    RecursiveLocalComputationFragment ((core isLe n k).weakenAt leading.length) ∧
    ∀ frames, Core.Steps (cost a n k) ⟨.eval ((core isLe n k).weakenAt leading.length) (leading++inserted::suffix),frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have fragment := (elaboration isLe n k).core_fragment
  have original := Core.steps_from_initial_sound (manual isLe a n k s [])
  rw [← split] at original
  have back := (fragment.evaluates_insert_iff leading suffix inserted).mp ((fragment.evaluates_insert_iff leading suffix inserted).mpr original)
  obtain ⟨commonCost,paths⟩ := fragment.insertion_paths leading suffix inserted back
  have known : Core.Steps (cost a n k) (.initial (core isLe n k) (leading++suffix) s) (.final (result isLe a) s) := by rw [split]; exact manual isLe a n k s []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt leading.length,fun frames => same ▸ (paths frames).2⟩

private def between (isLe : Bool) (a : Actual) (k : Nat) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.x),[.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot],s⟩
private def pending (isLe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.word a.y),[.binaryApply (op isLe) (.word a.x),.unaryApply .boolNot],s⟩
private def negation (isLe : Bool) (a : Actual) (s : Core.Store) : Core.State :=
  ⟨.ret (.bool (compared isLe a)),[.unaryApply .boolNot],s⟩
theorem three_genuine_operand_and_negation_checkpoints (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    Core.runStateful (charge n a.m+2) (.initial (core isLe n k) (env a).values s) = .outOfFuel (between isLe a k s) ∧
    Core.runStateful (charge n a.m+charge k a.t+3) (.initial (core isLe n k) (env a).values s) = .outOfFuel (pending isLe a s) ∧
    Core.runStateful (charge n a.m+charge k a.t+4) (.initial (core isLe n k) (env a).values s) = .outOfFuel (negation isLe a s) := by
  constructor
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,between,depth,childWord,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary
        (.cons .enterBinary (callsPath a false n s [.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot]))
    · exact Core.advance_next_iff.mpr .enterBinaryRight
  constructor
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,pending,depth,childWord,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary (.cons .enterBinary
        ((callsPath a false n s [.binaryRight (op isLe) (callCore true k) (env a).values,.unaryApply .boolNot]).trans
          (.cons .enterBinaryRight (callsPath a true k s [.binaryApply (op isLe) (.word a.x),.unaryApply .boolNot]))))
    · exact Core.advance_next_iff.mpr (.applyBinary (result := .bool (compared isLe a)) (by cases isLe <;> rfl))
  · apply Core.runStateful_outOfFuel_complete
    · simpa [Core.State.initial,core,negation,depth,Nat.add_assoc,Nat.add_left_comm] using Core.Steps.cons .enterUnary
        (CostStepComposition.binary (op := op isLe) (result := .bool (compared isLe a))
          (callsPath a false n s _) (callsPath a true k s _) (by cases isLe <;> rfl))
    · exact Core.advance_next_iff.mpr (.applyUnary (result := result isLe a) rfl)

theorem all_fuels_residual_and_full_resume (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core isLe n k) (env a).values s) = .outOfFuel cp) :
    (Core.runStateful fuel (.initial (core isLe n k) (env a).values s) = .done (result isLe a) s ↔ cost a n k ≤ fuel) ∧
    spent < cost a n k ∧ Core.Steps (cost a n k-spent) cp (.final (result isLe a) s) ∧
    Core.runStateful additional cp = Core.runStateful (spent+additional) (.initial (core isLe n k) (env a).values s) := by
  have path := manual isLe a n k s []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

theorem fixed_source_actual_body_cost_is_unbounded (isLe : Bool) (limit : Nat) (x y : Core.Word) (leftCapture rightCapture : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe 1 1) (result isLe a) s (cost a 1 1) ∧ limit < cost a 1 1 := by
  let a : Actual := ⟨x,y,limit,0,leftCapture,rightCapture⟩
  exact ⟨a,counted isLe a 1 1 s,by simp [cost,charge,a]; omega⟩

private def guarded (skipped : Syntax.Expr) : Syntax.Expr :=
  ⟨span,.conditional (ref .c) ⟨span.source,100,101⟩ (ref .x) ⟨span.source,400,401⟩ skipped⟩
theorem pure_overlap_with_skipped_original_operand (isLe : Bool) (a : Actual) (s : Core.Store) (skipped : Syntax.Expr) :
    LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 ∧
    RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
  have old : LocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
    cases isLe
    · exact .pure (.notEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
    · exact .pure (.lessEqual (.ifTrue (atomCost a .c s) (atomCost a .x s)) (atomCost a .y s))
  have new : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a) s (comparison isLe (guarded skipped) (ref .y)) (result isLe a) s 10 := by
    cases isLe
    · exact .notEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
    · exact .lessEqual (.ifTrue (.pure (atomCost a .c s)) (.pure (atomCost a .x s))) (.pure (atomCost a .y s))
  have same := new.deterministic old.toRecursiveLocalComputation
  exact ⟨old,same.2.2 ▸ new⟩

private def body (isLe : Bool) (n k : Nat) : Syntax.Block := ⟨span,
  [⟨span,.letDecl ⟨span,"r"⟩ none (some (source isLe n k))⟩,⟨span,.returnStmt (some ⟨span,.identifier ⟨span,"r"⟩⟩)⟩]⟩
private theorem bodyElab (isLe : Bool) (n k : Nat) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isLe n k) (.letE (core isLe n k) (.var 0)) .bool :=
  .inferred (elaboration isLe n k)
    (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
private theorem bodyCost (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe n k) (result isLe a) s (cost a n k+3) := by
  simpa [RecursiveComputationReturnTreeEvaluatesWithCost,body,Nat.add_assoc] using ComputationReturnTreeEvaluatesWithCost.inferred
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (counted isLe a n k s) (.expression (.pure (.identifier .head .head)))
private theorem bodyManual (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    Core.Steps (cost a n k+3) ⟨.eval (.letE (core isLe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  simpa [Nat.add_assoc] using CostStepComposition.letE (manual isLe a n k s (.letBody (.var 0) (env a).values::frames)) (.cons (.var rfl) .refl)
private theorem oldElab (isLe : Bool) :
    LocalComputationElaborates inputs.names inputs.context (source isLe 0 0) (core isLe 0 0) .bool := by
  cases oldLeaf .x with
  | pure lr ll lt =>
      cases oldLeaf .y with
      | pure rr rl rt =>
          cases isLe
          · exact .pure (.notEqual lr rr) (.unary (.binary ll rl)) (.unary (.binary lt rt))
          · exact .pure (.lessEqual lr rr) (.unary (.binary ll rl)) (.unary (.binary lt rt))
      | application child => cases child
  | application child => cases child
theorem old_original_body_embeddings (isLe : Bool) (a : Actual) (s : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (body isLe 0 0) (.letE (core isLe 0 0) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe 0 0) (result isLe a) s 10 := by
  have oldStatic : LocalComputationReturnTreeElaborates [] owner inputs (body isLe 0 0) (.letE (core isLe 0 0) (.var 0)) .bool :=
    .inferred (by change ¬"r" ∈ ["f","x","g","y","c"]; decide) (oldElab isLe)
      (.expression (.pure (.identifier .head) (.var .head) (.var .head)))
  have child : LocalComputationEvaluatesWithCost inputs.names (env a) s (source isLe 0 0) (result isLe a) s 7 := by
    cases isLe; exact .pure (.notEqual (atomCost a .x s) (atomCost a .y s)); exact .pure (.lessEqual (atomCost a .x s) (atomCost a .y s))
  have oldCost : LocalComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe 0 0) (result isLe a) s 10 :=
    .inferred child (.expression (.pure (.identifier .head .head)))
  exact ⟨oldStatic.toRecursiveComputationReturnTree,oldCost.toRecursiveComputationReturnTree⟩

theorem shared_body_original_source_and_actual_cost (isLe : Bool) (a : Actual) (n k : Nat) (s : Core.Store) (frames : List Core.Frame) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (body isLe n k) = some (.letE (core isLe n k) (.var 0),.bool) ∧
    Core.HasType inputs.context.values (.letE (core isLe n k) (.var 0)) .bool ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (body isLe n k) (result isLe a) s (cost a n k+3) ∧
    Core.Steps (cost a n k+3) ⟨.eval (.letE (core isLe n k) (.var 0)) (env a).values,frames,s⟩ ⟨.ret (result isLe a),frames,s⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyElab isLe n k) (environment := env a) rfl).mpr (bodyManual isLe a n k s [])
  exact ⟨(elaborateComputationReturnTree?_iff (checkChild := elaborateRecursiveLocalComputation?)
      (ChildElab := RecursiveLocalComputationElaborates) elaborateRecursiveLocalComputation?_iff).mpr (bodyElab isLe n k),
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (bodyElab isLe n k),costed,
    ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
      RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
      RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (bodyCost isLe a n k s) (bodyElab isLe n k) rfl frames⟩

end Tests.FrontendRecursiveNegatedComparison
