import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.Computation
import Solcore.Core.FuelResumptionProperties

/-! Symbolic original groups and all wildcard rows retain their source spans.
Static scrutinee/result types are independent of the actual closure payloads.
Raw paths preserve captures/effects; no typed inhabitants or worlds are inferred. -/
set_option autoImplicit false
namespace Tests.FrontendTypeGeneralMatchCount
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"TypeGeneralMatchCount",by decide⟩],by decide⟩⟩,119⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-type-general-count.sol"⟩,0,128⟩
private def inputs (scrutineeType resultType : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"s",id 0,.function .word scrutineeType⟩,⟨"b",id 1,.function .word resultType⟩,⟨"x",id 2,.word⟩],
    by change [id 0,id 1,id 2].Nodup; decide⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call (side : Bool) : Syntax.Expr := ⟨span,.call (ref (if side then "b" else "s")) ⟨span,[ref "x"]⟩⟩
private def branch : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (call true))⟩]⟩
private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [],pattern => pattern
  | outer::rest,pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapped (spans : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) :
    WordMatchPatternClassifies (wrap spans ⟨span,.wildcard marker⟩) none := by
  induction spans with | nil => exact .wildcard rfl | cons _ _ ih => exact .group ih
private structure Suffix (scrutineeType resultType : Core.Ty) where
  original : List Syntax.MatchCase
  rows : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  ordered : rows.map Prod.fst = original
  tags : ∀ entry ∈ rows, entry.2.1 = none
  meanings : ∀ entry ∈ rows, WordMatchPatternClassifies entry.1.value.pattern none
  branches : ∀ entry ∈ rows, RecursiveComputationReturnTreeElaborates [] owner
    (inputs scrutineeType resultType) entry.1.value.body entry.2.2 resultType
private structure Shape where
  scrutineeType : Core.Ty
  resultType : Core.Ty
  groups : Nat → List Syntax.SourceSpan
  markers : Nat → Syntax.SourceSpan
  suffix : Suffix scrutineeType resultType
  hasDefault : Bool
private def locals (shape : Shape) := inputs shape.scrutineeType shape.resultType
private def wildcard (shape : Shape) (n : Nat) : Syntax.MatchCase :=
  ⟨span,⟨wrap (shape.groups n) ⟨span,.wildcard (shape.markers n)⟩,branch⟩⟩
private def cases : Nat → Shape → List Syntax.MatchCase
  | 0,shape => wildcard shape 0 :: shape.suffix.original
  | n+1,shape => wildcard shape (n+1) :: cases n shape
private def defaultBody (shape : Shape) : Option Syntax.Block := if shape.hasDefault then some branch else none
private theorem calleeElab (shape : Shape) (side : Bool) : RecursiveLocalComputationElaborates
    (locals shape).names (locals shape).context (ref (if side then "b" else "s"))
    (.var (if side then 1 else 0)) (.function .word (if side then shape.resultType else shape.scrutineeType)) :=
  .pure (.identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl)))
private theorem argumentElab (shape : Shape) : RecursiveLocalComputationElaborates
    (locals shape).names (locals shape).context (ref "x") (.var 2) .word :=
  .pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private def source (n : Nat) (shape : Shape) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨call false,[]⟩⟩ ⟨span,⟨cases n shape,defaultBody shape⟩⟩⟩]⟩
private def selectedCore : Core.Expr := .apply (.var 2) (.var 3)
private def core : Core.Expr := .letE (.apply (.var 0) (.var 2)) selectedCore
private def rows : Nat → Shape → List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  | 0,shape => (wildcard shape 0,none,.apply (.var 1) (.var 2)) :: shape.suffix.rows
  | n+1,shape => (wildcard shape (n+1),none,.apply (.var 1) (.var 2)) :: rows n shape
private theorem rowFacts (n : Nat) (shape : Shape) :
    (rows n shape).map Prod.fst = cases n shape ∧ ∀ entry ∈ rows n shape,
      entry.2.1 = none ∧ WordMatchPatternClassifies entry.1.value.pattern none ∧
      RecursiveComputationReturnTreeElaborates [] owner (locals shape) entry.1.value.body entry.2.2 shape.resultType := by
  induction n with
  | zero =>
      refine ⟨by simp [rows,cases,shape.suffix.ordered],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl,wrapped _ _,.expression (.application (calleeElab shape true) (argumentElab shape))⟩
      · exact ⟨shape.suffix.tags entry member,shape.suffix.meanings entry member,shape.suffix.branches entry member⟩
  | succ n ih =>
      refine ⟨by simp [rows,cases,ih.1],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl,wrapped _ _,.expression (.application (calleeElab shape true) (argumentElab shape))⟩
      · exact ih.2 entry member
private def defaultEntry (shape : Shape) : Option (Syntax.Block × Core.Expr) :=
  if shape.hasDefault then some (branch,.apply (.var 1) (.var 2)) else none
private theorem elaborated (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeElaborates [] owner (locals shape) (source n shape) core shape.resultType := by
  exact .wordMatch (defaultEntry := defaultEntry shape)
    (.application (calleeElab shape false) (argumentElab shape)) (rowFacts n shape).1
    (fun entry member => by rw [((rowFacts n shape).2 entry member).1]; exact ((rowFacts n shape).2 entry member).2.1)
    (.inr (fun entry member => ((rowFacts n shape).2 entry member).1))
    (fun entry member => ((rowFacts n shape).2 entry member).2.2)
    (by cases choice : shape.hasDefault <;> simp [defaultEntry,defaultBody,choice])
    (by intro entry member; cases choice : shape.hasDefault <;> simp [defaultEntry,choice] at member
        subst entry; exact .expression (.application (calleeElab shape true) (argumentElab shape)))
    (by cases n <;> simp [rows,selectedCore,Core.Expr.weakenAt])
private theorem chosen (n : Nat) (shape : Shape) (actual : Core.Value) :
    WordMatchChooses actual (cases n shape) (defaultBody shape) branch 0 := by
  cases n <;> exact .wildcard (wrapped _ _)

private structure Actual where
  argument : Core.Value
  scrutineeBody : Core.Expr
  branchBody : Core.Expr
  scrutineeCapture : Core.Environment
  branchCapture : Core.Environment
  initial : Core.Store
  middle : Core.Store
  final : Core.Store
  scrutineeValue : Core.Value
  result : Core.Value
  scrutineeCost : Nat
  branchCost : Nat
  scrutineePath : ∀ k, Core.Steps scrutineeCost ⟨.eval scrutineeBody (argument::scrutineeCapture),k,initial⟩ ⟨.ret scrutineeValue,k,middle⟩
  branchPath : ∀ k, Core.Steps branchCost ⟨.eval branchBody (argument::branchCapture),k,middle⟩ ⟨.ret result,k,final⟩
private def function (a : Actual) (shape : Shape) (side : Bool) : Core.Value :=
  .closure .word (if side then shape.resultType else shape.scrutineeType)
    (if side then a.branchBody else a.scrutineeBody) (if side then a.branchCapture else a.scrutineeCapture)
private def env (a : Actual) (shape : Shape) : Resolved.Environment :=
  [(id 0,function a shape false),(id 1,function a shape true),(id 2,a.argument)]
private def cost (a : Actual) := a.scrutineeCost+a.branchCost+12
private theorem rawCall (a : Actual) (shape : Shape) (side : Bool) :
    RecursiveLocalComputationEvaluatesWithCost (locals shape).names (env a shape)
      (if side then a.middle else a.initial) (call side) (if side then a.result else a.scrutineeValue)
      (if side then a.final else a.middle) ((if side then a.branchCost else a.scrutineeCost)+5) := by
  have found : LocalExpressionEvaluatesWithCost (locals shape).names (env a shape)
      (if side then a.middle else a.initial) (ref (if side then "b" else "s")) (function a shape side)
      (if side then a.middle else a.initial) 1 :=
    .identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl))
  simpa [call,ref,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using RecursiveLocalComputationEvaluatesWithCost.application
    (.pure found) (.pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl) (Resolved.LocalScope.lookup?_iff.mp rfl)))
    (by cases side; exact a.scrutineePath []; exact a.branchPath [])
private theorem counted (a : Actual) (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (locals shape).names (env a shape) a.initial
      (source n shape) a.result a.final (cost a) := by
  simpa [source,cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    ComputationReturnTreeEvaluatesWithCost.wordMatch (rawCall a shape false) (chosen n shape a.scrutineeValue) (.expression (rawCall a shape true))
private theorem invoke {body : Core.Expr} {returnType : Core.Ty}
    {captured environment : Core.Environment} {argument value : Core.Value}
    {initial final : Core.Store} {count i j : Nat}
    (callee : environment[i]? = some (.closure .word returnType body captured)) (arg : environment[j]? = some argument)
    (path : ∀ k, Core.Steps count ⟨.eval body (argument::captured),k,initial⟩ ⟨.ret value,k,final⟩) (k : List Core.Frame) :
    Core.Steps (count+5) ⟨.eval (.apply (.var i) (.var j)) environment,k,initial⟩ ⟨.ret value,k,final⟩ := by
  simpa [Nat.add_assoc] using Core.Steps.cons .enterApply
    (.cons (.var callee) (.cons .beginArgument (.cons (.var arg) (.cons .invokeClosure (path k)))))
private theorem manual (a : Actual) (shape : Shape) (k : List Core.Frame) :
    Core.Steps (cost a) ⟨.eval core (env a shape).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have arithmetic : (a.scrutineeCost+5)+(a.branchCost+5)+2=cost a := by unfold cost; omega
  rw [← arithmetic]
  exact CostStepComposition.letE (invoke (environment := (env a shape).values) (i := 0) (j := 2) rfl rfl a.scrutineePath _)
    (invoke (environment := a.scrutineeValue::(env a shape).values) (i := 2) (j := 3) rfl rfl a.branchPath k)

theorem original_typed_rows_keep_every_case_but_execute_zero_comparisons (n : Nat) (shape : Shape) (actual : Core.Value) :
    RecursiveComputationReturnTreeElaborates [] owner (locals shape) (source n shape) core shape.resultType ∧
    WordMatchChooses actual (cases n shape) (defaultBody shape) branch 0 ∧
    (cases n shape).length = n+1+shape.suffix.original.length := by
  refine ⟨elaborated n shape,chosen n shape actual,?_⟩
  induction n with
  | zero => simp [cases,Nat.add_comm]
  | succ n ih => change (cases n shape).length+1=(n+1)+1+shape.suffix.original.length; omega
theorem checker_and_both_typing_interfaces (n : Nat) (shape : Shape) :
    elaborateRecursiveComputationReturnTree? [] owner (locals shape) (source n shape)=some (core,shape.resultType) ∧
    RecursiveComputationReturnTreeHasType [] owner (locals shape) (source n shape) shape.resultType ∧
    Core.HasType (locals shape).context.values core shape.resultType :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (elaborated n shape),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaborated n shape⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (elaborated n shape)⟩
theorem actual_effects_and_independent_literal_paths (a : Actual) (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (locals shape).names (env a shape) a.initial (source n shape) a.result a.final (cost a) ∧
    ∀ k, Core.Steps (cost a) ⟨.eval core (env a shape).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨counted a n shape,manual a shape⟩
theorem shared_cost_kernel_preserves_the_zero_comparison_cost (a : Actual) (n : Nat) (shape : Shape) (k : List Core.Frame) :
    Core.Steps (cost a) ⟨.eval core (env a shape).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (elaborated n shape) (environment := env a shape) rfl).mpr (manual a shape [])
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
    RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation costed (elaborated n shape) rfl k
theorem cost_value_and_store_are_jointly_unique (a : Actual) (n : Nat) (shape : Shape)
    {value : Core.Value} {final : Core.Store} {count : Nat}
    (other : RecursiveComputationReturnTreeEvaluatesWithCost owner (locals shape).names (env a shape) a.initial (source n shape) value final count) :
    value=a.result ∧ final=a.final ∧ count=cost a :=
  ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationEvaluatesWithCost.deterministic other (counted a n shape)
theorem exact_literal_insertion_preserves_actual_values_and_captures (a : Actual) (n : Nat) (shape : Shape)
    (leading trailing : Core.Environment) (inserted : Core.Value) (split : leading++trailing=(env a shape).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment (core.weakenAt leading.length) ∧
    Core.Evaluates (leading++inserted::trailing) a.initial (core.weakenAt leading.length) a.result a.final ∧
    ∀ k, Core.Steps (cost a) ⟨.eval (core.weakenAt leading.length) (leading++inserted::trailing),k,a.initial⟩
      ⟨.ret a.result,k,a.final⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (elaborated n shape)
  have original := Core.steps_from_initial_sound (manual a shape [])
  rw [← split] at original
  obtain ⟨common,paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths fragment leading trailing inserted original
  have known : Core.Steps (cost a) (.initial core (leading++trailing) a.initial) (.final a.result a.final) := by rw [split]; exact manual a shape []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    (ComputationBodyFragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff fragment leading trailing inserted).mpr original,
    fun k => same ▸ (paths k).2⟩
theorem all_fuels_and_full_checkpoint_resumption (a : Actual) (n : Nat) (shape : Shape)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial core (env a shape).values a.initial)=.outOfFuel cp) :
    (Core.runStateful fuel (.initial core (env a shape).values a.initial)=.done a.result a.final ↔ cost a≤fuel) ∧
    ((∃ saved, Core.runStateful fuel (.initial core (env a shape).values a.initial)=.outOfFuel saved) ↔ fuel<cost a) ∧
    spent<cost a ∧ Core.Steps (cost a-spent) cp (.final a.result a.final) ∧
    Core.runStateful additional cp=Core.runStateful (spent+additional) (.initial core (env a shape).values a.initial) := by
  have path := shared_cost_kernel_preserves_the_zero_comparison_cost a n shape []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,path.runStateful_outOfFuel_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩
theorem the_actual_scrutinee_is_saved_once_before_the_first_wildcard
    (a : Actual) (shape : Shape) (k : List Core.Frame) :
    let start : Core.State := ⟨.eval core (env a shape).values,k,a.initial⟩
    let cp : Core.State := ⟨.ret a.scrutineeValue,.letBody selectedCore (env a shape).values::k,a.middle⟩
    Core.runStateful (a.scrutineeCost+6) start=.outOfFuel cp ∧
    ∀ additional, Core.runStateful additional cp=Core.runStateful (a.scrutineeCost+6+additional) start := by
  dsimp only
  have prefixPath := Core.Steps.cons .enterLet
    (invoke (environment := (env a shape).values) (i := 0) (j := 2) rfl rfl a.scrutineePath (.letBody selectedCore (env a shape).values::k))
  have exhausted := Core.runStateful_outOfFuel_complete prefixPath (show Core.advance _=.next _ from rfl)
  have arithmetic : a.scrutineeCost+5+1=a.scrutineeCost+6 := by omega
  rw [arithmetic] at exhausted
  exact ⟨exhausted,Core.runStateful_resume exhausted⟩
private def allocating : Core.Expr := .letE (.newCell .word (.var 0)) (.var 2)
private theorem allocationPath (word : Core.Word) (payload : Core.Value) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval allocating (.word word::payload::captured),k,s⟩ ⟨.ret payload,k,s++[.word word]⟩ :=
  CostStepComposition.letE (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))) (.cons (.var rfl) .refl)
private def effects (scrutinee result : Core.Value) (word : Core.Word) (left right : Core.Environment) (s : Core.Store) : Actual :=
  ⟨.word word,allocating,allocating,scrutinee::left,result::right,s,s++[.word word],(s++[.word word])++[.word word],scrutinee,result,6,6,
    allocationPath word scrutinee left s,allocationPath word result right (s++[.word word])⟩
theorem both_actual_calls_allocate_and_return_distinct_captured_payloads (n : Nat) (shape : Shape)
    (scrutinee result : Core.Value) (word : Core.Word) (left right : Core.Environment) (s : Core.Store) :
    let a := effects scrutinee result word left right s
    RecursiveComputationReturnTreeEvaluatesWithCost owner (locals shape).names (env a shape) s (source n shape) result
      (s++[.word word,.word word]) 24 ∧
    ∀ k, Core.Steps 24 ⟨.eval core (env a shape).values,k,s⟩ ⟨.ret result,k,s++[.word word,.word word]⟩ := by
  simpa [effects,cost,List.append_assoc] using actual_effects_and_independent_literal_paths (effects scrutinee result word left right s) n shape

private def delay : Nat → Nat → Core.Expr
  | 0,index => .var index
  | n+1,index => .letE .unit (delay n (index+1))
private theorem delayPath (n index : Nat) (environment : Core.Environment) {value : Core.Value}
    (found : environment[index]?=some value) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (delay n index) environment,k,store⟩ ⟨.ret value,k,store⟩ := by
  induction n generalizing index environment with
  | zero => exact .cons (.var found) .refl
  | succ n ih =>
      have arithmetic : 1+(3*n+1)+2=3*(n+1)+1 := by omega
      rw [← arithmetic]
      exact CostStepComposition.letE (.cons .unit .refl) (ih (index+1) (.unit::environment) (by simpa using found))
-- This delay-only fixture preserves its store; arbitrary Actual paths need not.
private def delayed (n : Nat) (scrutinee result : Core.Value) (left right : Core.Environment) (s : Core.Store) : Actual :=
  ⟨.word .zero,delay n 1,.var 1,scrutinee::left,result::right,s,s,s,scrutinee,result,3*n+1,1,
    delayPath n 1 _ rfl s,fun _ => .cons (.var rfl) .refl⟩
theorem one_fixed_original_source_has_unbounded_actual_body_cost (n bound : Nat) (shape : Shape)
    (scrutinee result : Core.Value) (left right : Core.Environment) (s : Core.Store) :
    ∃ a : Actual, bound<cost a ∧
      RecursiveComputationReturnTreeEvaluatesWithCost owner (locals shape).names (env a shape) s (source n shape) result s (cost a) ∧
      ∀ k, Core.Steps (cost a) ⟨.eval core (env a shape).values,k,s⟩ ⟨.ret result,k,s⟩ := by
  refine ⟨delayed bound scrutinee result left right s,?_,actual_effects_and_independent_literal_paths _ n shape⟩
  simp only [delayed,cost]; omega
end Tests.FrontendTypeGeneralMatchCount
