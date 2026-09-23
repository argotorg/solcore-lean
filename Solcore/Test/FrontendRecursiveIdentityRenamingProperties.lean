import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

/-! Independent original syntax, arbitrary static types and unchecked actual
captures precede relabeling. Only the explicit delay fixture preserves stores;
the original mixed tuple has no named binder or fresh-identity allocation. -/
set_option autoImplicit false
namespace Tests.FrontendRecursiveIdentityRenaming
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"RecursiveIdentitySymbols",by decide⟩],by decide⟩⟩,126⟩
private def foreign : Resolved.DeclarationId := { owner with declarationIndex := 903 }
private def span : Syntax.SourceSpan := ⟨⟨.main,"recursive-identity-symbols.sol"⟩,17,300⟩
private inductive Key | f | x | c | w
private def index : Key → Nat | .f => 0 | .x => 1 | .c => 2 | .w => 3
private def ident : Key → Resolved.LocalId
  | .f => ⟨owner,91⟩ | .x => ⟨foreign,700⟩ | .c => ⟨foreign,4⟩ | .w => ⟨owner,33⟩
private def name : Key → String | .f => "f" | .x => "x" | .c => "c" | .w => "w"
private def typeOf (a : Core.Ty) : Key → Core.Ty | .f => .function a a | .x => a | .c => .bool | .w => .word
private def names : LocalNameTable := [("f",ident .f),("x",ident .x),("c",ident .c),("w",ident .w),("f",ident .x)]
private def context (a : Core.Ty) : Resolved.Context :=
  [(ident .f,.function a a),(ident .x,a),(ident .c,.bool),(ident .w,.word),(ident .f,.bool)]
private def ref (key : Key) : Syntax.Expr := ⟨span,.identifier ⟨span,name key⟩⟩
private def calls : Nat → Syntax.Expr
  | 0 => ref .x | n+1 => ⟨span,.call (ref .f) ⟨span,[calls n]⟩⟩
private def callCore : Nat → Core.Expr | 0 => .var 1 | n+1 => .apply (.var 0) (callCore n)
private def complemented : Syntax.Expr := ⟨span,.unary ⟨span,.bitNot⟩ (ref .w)⟩
private def conditional : Syntax.Expr := ⟨span,.conditional (ref .c) span complemented span complemented⟩
private def source (n : Nat) : Syntax.Expr := ⟨span,.tuple ⟨span,[⟨span,.group (calls n)⟩,conditional,ref .c]⟩⟩
private def choiceCore : Core.Expr := .ifE (.var 2) (.unary .wordNot (.var 3)) (.unary .wordNot (.var 3))
private def tailCore : Core.Expr := .pair choiceCore (.var 2)
private def core (n : Nat) : Core.Expr := .pair (callCore n) tailCore
private theorem leaf (a : Core.Ty) (key : Key) :
    RecursiveLocalComputationElaborates names (context a) (ref key) (.var (index key)) (typeOf a key) :=
  .pure (.identifier (id := ident key) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases key <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem callElab (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (calls n) (callCore n) a := by
  induction n with | zero => exact leaf a .x | succ n ih => exact .application (leaf a .f) ih
private theorem original (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (source n) (core n) (.product a (.product .word .bool)) :=
  .many (.group (callElab a n)) (.pair (.conditional (leaf a .c) (.bitNot (leaf a .w)) (.bitNot (leaf a .w))) (leaf a .c))
private def delay : Nat → Nat → Core.Expr | 0,i => .var i | m+1,i => .letE (.var 0) (delay m (i+1))
private structure Actual where
  payload : Core.Value
  word : Core.Word
  choice : Bool
  depth : Nat
  captures : Core.Environment
  hidden : Core.Value
private def actual (a : Core.Ty) (v : Actual) : Key → Core.Value
  | .f => .closure a a (delay v.depth 0) v.captures | .x => v.payload | .c => .bool v.choice | .w => .word v.word
private def env (a : Core.Ty) (v : Actual) : Resolved.Environment :=
  [(ident .f,actual a v .f),(ident .x,v.payload),(ident .c,.bool v.choice),(ident .w,.word v.word),(ident .f,v.hidden)]
private def charge (n m : Nat) := n*(3*m+5)+1
private def result (v : Actual) : Core.Value := .pair v.payload (.pair (.word v.word.bitNot) (.bool v.choice))
private theorem atomCost (a : Core.Ty) (v : Actual) (key : Key) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (ref key) (actual a v key) s 1 :=
  .pure (.identifier (id := ident key) (LocalNameTable.lookup?_iff.mp (by cases key <;> rfl))
    (Resolved.LocalScope.lookup?_iff.mp (by cases key <;> rfl)))
private theorem delayed (m i : Nat) (e : Core.Environment) (v : Core.Value) (s : Core.Store) (k : List Core.Frame)
    (found : e[i]?=some v) : Core.Steps (3*m+1) ⟨.eval (delay m i) e,k,s⟩ ⟨.ret v,k,s⟩ := by
  induction m generalizing i e k with
  | zero => exact .cons (.var found) .refl
  | succ m ih =>
      cases e with
      | nil => simp at found
      | cons head rest =>
          simpa [delay,Nat.mul_add,Nat.add_assoc] using Core.Steps.cons .enterLet
            (.cons (.var rfl) (.cons .bindLet (ih (i+1) (head::head::rest) k (by simpa using found))))
private theorem callCost (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (calls n) v.payload s (charge n v.depth) := by
  induction n with
  | zero => simpa only [calls,actual,charge,Nat.zero_mul,Nat.zero_add] using atomCost a v .x s
  | succ n ih =>
      have count : charge (n+1) v.depth=1+charge n v.depth+(3*v.depth+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact .application (atomCost a v .f s) ih (delayed v.depth 0 (v.payload::v.captures) v.payload s [] rfl)
private theorem callPath (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n v.depth) ⟨.eval (callCore n) (env a v).values,k,s⟩ ⟨.ret v.payload,k,s⟩ := by
  induction n generalizing k with
  | zero => simp only [charge,Nat.zero_mul,Nat.zero_add]; exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : charge (n+1) v.depth=1+charge n v.depth+(3*v.depth+1)+3 := by simp [charge,Nat.add_mul]; omega
      rw [count]; exact CostStepComposition.apply (.cons (.var rfl) .refl) (ih _)
        (delayed v.depth 0 (v.payload::v.captures) v.payload s [] rfl)
private theorem branchCost (a : Core.Ty) (v : Actual) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s conditional (.word v.word.bitNot) s 6 := by
  cases chosen : v.choice
  · exact .ifFalse (by simpa [actual,chosen] using atomCost a v .c s) (.bitNot (atomCost a v .w s))
  · exact .ifTrue (by simpa [actual,chosen] using atomCost a v .c s) (.bitNot (atomCost a v .w s))
private theorem raw (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) :
    RecursiveLocalComputationEvaluatesWithCost names (env a v) s (source n) (result v) s (charge n v.depth+13) := by
  exact .many (.group (callCost a v n s)) (.pair (branchCost a v s) (atomCost a v .c s))
private theorem pairPath {e : Core.Environment} {s t u : Core.Store} {left right : Core.Expr}
    {v w : Core.Value} {lc rc : Nat} (k : List Core.Frame)
    (l : Core.Steps lc ⟨.eval left e,.pairRight right e::k,s⟩ ⟨.ret v,.pairRight right e::k,t⟩)
    (r : Core.Steps rc ⟨.eval right e,.pairApply v::k,t⟩ ⟨.ret w,.pairApply v::k,u⟩) :
    Core.Steps (lc+rc+3) ⟨.eval (.pair left right) e,k,s⟩ ⟨.ret (.pair v w),k,u⟩ := by
  simpa only [Nat.add_assoc] using Core.Steps.cons .enterPair
    (l.trans (.cons .enterPairRight (r.trans (.cons .applyPair .refl))))
private theorem branchPath (a : Core.Ty) (v : Actual) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval choiceCore (env a v).values,k,s⟩ ⟨.ret (.word v.word.bitNot),k,s⟩ := by
  cases chosen : v.choice
  · exact CostStepComposition.ifFalse (.cons (.var (by simp [env,Resolved.LocalScope.values,chosen])) .refl)
      (CostStepComposition.unary (.cons (.var rfl) .refl) rfl)
  · exact CostStepComposition.ifTrue (.cons (.var (by simp [env,Resolved.LocalScope.values,chosen])) .refl)
      (CostStepComposition.unary (.cons (.var rfl) .refl) rfl)
private theorem manual (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps (charge n v.depth+13) ⟨.eval (core n) (env a v).values,k,s⟩ ⟨.ret (result v),k,s⟩ :=
  pairPath k (callPath a v n s _) (pairPath _ (branchPath a v s _) (.cons (.var rfl) .refl))

theorem arbitrary_types_and_depth_have_independent_original_meaning (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates names (context a) (source n) (core n) (.product a (.product .word .bool)) ∧
    RecursiveLocalComputationHasType names (context a) (source n) (.product a (.product .word .bool)) :=
  ⟨original a n,recursiveLocalComputationHasType_iff_elaborates.mpr ⟨_,original a n⟩⟩
theorem injective_relabeling_keeps_original_code_type_and_whole_check
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping) (a : Core.Ty) (n : Nat) :
    RecursiveLocalComputationElaborates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n) (core n) (.product a (.product .word .bool)) ∧
    RecursiveLocalComputationHasType (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n) (.product a (.product .word .bool)) ∧
    elaborateRecursiveLocalComputation? (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (context a))
      (source n)=some (core n,.product a (.product .word .bool)) :=
  ⟨(recursiveLocalComputationElaborates_mapIds_iff mapping injective).mpr (original a n),
    (recursiveLocalComputationHasType_mapIds_iff mapping injective).mpr (arbitrary_types_and_depth_have_independent_original_meaning a n).2,
    (elaborateRecursiveLocalComputation?_mapIds mapping injective names (context a) (source n)).trans
      (elaborateRecursiveLocalComputation?_iff.mpr (original a n))⟩
theorem unchecked_actual_captures_keep_value_store_cost_and_literal_path
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (env a v))
      s (source n) (result v) s (charge n v.depth+13) ∧
    RecursiveLocalComputationEvaluates (LocalNameTable.mapIds mapping names) (Resolved.LocalScope.mapIds mapping (env a v)) s (source n) (result v) s ∧
    Core.Steps (charge n v.depth+13) ⟨.eval (core n) (Resolved.LocalScope.mapIds mapping (env a v)).values,k,s⟩ ⟨.ret (result v),k,s⟩ := by
  exact ⟨(recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw a v n s),
    (recursiveLocalComputationEvaluates_mapIds_iff mapping injective).mpr (recursiveLocalComputationEvaluates_iff_exists_cost.mpr ⟨_,raw a v n s⟩),
    by simpa only [Resolved.LocalScope.values_mapIds] using manual a v n s k⟩
theorem same_actual_value_store_and_cost_are_jointly_unique
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (n : Nat) (s t : Core.Store) (value : Core.Value) (cost : Nat)
    (other : RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env a v)) s (source n) value t cost) :
    value=result v ∧ t=s ∧ cost=charge n v.depth+13 :=
  ((recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mp other).deterministic (raw a v n s)
/-- With literal Core fixed, erasing renamed environment IDs needs no injectivity.
Transport of source compilation above does require it. -/
theorem same_fuel_and_every_genuine_checkpoint_keep_full_resumption
    (mapping : Resolved.LocalId → Resolved.LocalId) (a : Core.Ty) (v : Actual) (n fuel extra : Nat) (s : Core.Store) :
    let start := Core.State.initial (core n) (Resolved.LocalScope.mapIds mapping (env a v)).values s
    (Core.runStateful fuel start=.done (result v) s ↔ charge n v.depth+13≤fuel) ∧
    ∀ cp, Core.runStateful fuel start=.outOfFuel cp →
      Core.runStateful extra cp=Core.runStateful (fuel+extra) (.initial (core n) (env a v).values s) := by
  simp only [Resolved.LocalScope.values_mapIds]
  exact ⟨(manual a v n s []).runStateful_done_iff,fun _ stopped => Core.runStateful_resume stopped extra⟩
theorem actual_left_child_is_saved_before_the_unchanged_pending_tuple
    (mapping : Resolved.LocalId → Resolved.LocalId) (a : Core.Ty) (v : Actual) (n : Nat) (s : Core.Store) (k : List Core.Frame) :
    let e := (Resolved.LocalScope.mapIds mapping (env a v)).values
    let start : Core.State := ⟨.eval (core n) e,k,s⟩
    let cp : Core.State := ⟨.ret v.payload,.pairRight tailCore e::k,s⟩
    Core.runStateful (charge n v.depth+1) start=.outOfFuel cp ∧
    ∀ extra, Core.runStateful extra cp=Core.runStateful (charge n v.depth+1+extra) start := by
  simp only [Resolved.LocalScope.values_mapIds]
  have path := Core.Steps.cons .enterPair (callPath a v n s (.pairRight tailCore (env a v).values::k))
  have stopped := Core.runStateful_outOfFuel_complete path (show Core.advance _=.next _ from rfl)
  exact ⟨stopped,Core.runStateful_resume stopped⟩
theorem fixed_original_source_does_not_bound_actual_cost
    (mapping : Resolved.LocalId → Resolved.LocalId) (injective : Function.Injective mapping)
    (a : Core.Ty) (v : Actual) (s : Core.Store) (bound : Nat) :
    ∃ m cost, bound<cost ∧ RecursiveLocalComputationEvaluatesWithCost (LocalNameTable.mapIds mapping names)
      (Resolved.LocalScope.mapIds mapping (env a { v with depth := m })) s (source 1) (result v) s cost := by
  refine ⟨bound,charge 1 bound+13,by simp [charge]; omega,?_⟩
  exact (recursiveLocalComputationEvaluatesWithCost_mapIds_iff mapping injective).mpr (raw a { v with depth := bound } 1 s)
end Tests.FrontendRecursiveIdentityRenaming
