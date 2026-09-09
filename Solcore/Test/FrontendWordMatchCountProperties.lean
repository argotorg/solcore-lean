import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Core.FuelResumptionProperties

/-! Symbolic original ASTs, not parser-output claims. Separate actual closure
paths may change stores; no runtime typing or store invariance is presumed. -/
set_option autoImplicit false
namespace Tests.FrontendWordMatchCount
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MatchCount",by decide⟩],by decide⟩⟩,91⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-match.sol"⟩,0,128⟩
private def one : Core.Word := ⟨1,by decide⟩
private def inputs : LocalTypeInputs := ⟨[⟨"s",id 0,.function .word .word⟩,
  ⟨"b",id 1,.function .word .word⟩,⟨"x",id 2,.word⟩],by change [id 0,id 1,id 2].Nodup; decide⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call (side : Bool) : Syntax.Expr := ⟨span,.call (ref (if side then "b" else "s")) ⟨span,[ref "x"]⟩⟩
private def branch : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (call true))⟩]⟩
private def unused : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩
private def arm (hit : Bool) : Syntax.MatchCase :=
  ⟨span,⟨⟨span,.literal ⟨span,.decimal (if hit then "1" else "0")⟩⟩,if hit then branch else unused⟩⟩
private def cases : Nat → Bool → List Syntax.MatchCase
  | 0,hit => if hit then [arm true] else []
  | n+1,hit => arm false :: cases n hit
private def source (n : Nat) (hit : Bool) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨call false,[]⟩⟩ ⟨span,⟨cases n hit,some branch⟩⟩⟩]⟩
private def guard (word : Core.Word) : Core.Expr := .binary .wordEq (.var 0) (.word word)
private def selectedCore : Core.Expr := .apply (.var 2) (.var 3)
private def tree : Nat → Bool → Core.Expr
  | 0,hit => if hit then .ifE (guard one) selectedCore selectedCore else selectedCore
  | n+1,hit => .ifE (guard .zero) (.var 3) (tree n hit)
private def core (n : Nat) (hit : Bool) : Core.Expr := .letE (.apply (.var 0) (.var 2)) (tree n hit)
private def tests (n : Nat) (hit : Bool) : Nat := n + if hit then 1 else 0
private theorem meaning (hit : Bool) : WordMatchPatternDenotes (arm hit).value.pattern (if hit then one else .zero) :=
  ⟨_,rfl,interpretWordLiteral?_iff.mp (by cases hit <;> decide)⟩
private theorem calleeElab (side : Bool) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref (if side then "b" else "s")) (.var (if side then 1 else 0)) (.function .word .word) :=
  .pure (.identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl)))
private theorem argumentElab : RecursiveLocalComputationElaborates inputs.names inputs.context (ref "x") (.var 2) .word :=
  .pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private def rows : Nat → Bool → List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  | 0,hit => if hit then [(arm true,some one,.apply (.var 1) (.var 2))] else []
  | n+1,hit => (arm false,some .zero,.var 2) :: rows n hit
private theorem rowFacts (n : Nat) (hit : Bool) :
    (rows n hit).map Prod.fst = cases n hit ∧ ∀ entry ∈ rows n hit,
      (match entry.2.1 with
        | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
        | some word => WordMatchPatternDenotes entry.1.value.pattern word) ∧
      RecursiveComputationReturnTreeElaborates [] owner inputs entry.1.value.body entry.2.2 .word := by
  induction n with
  | zero =>
      cases hit
      · exact ⟨rfl,by intro entry member; cases member⟩
      · refine ⟨rfl,?_⟩; intro entry member
        have same := List.mem_singleton.mp member; subst entry
        exact ⟨meaning true,.expression (.application (calleeElab true) argumentElab)⟩
  | succ n ih =>
      refine ⟨by simp [rows,cases,ih.1],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨meaning false,.expression argumentElab⟩
      · exact ih.2 entry member
private theorem elaborated (n : Nat) (hit : Bool) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n hit) (core n hit) .word := by
  have folded : (rows n hit).foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun t => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) t))
      (some ((.apply (.var 1) (.var 2) : Core.Expr).weakenAt 0)) = some (tree n hit) := by
    induction n with
    | zero => cases hit <;> simp [tree,rows,selectedCore,guard,Core.Expr.weakenAt]
    | succ n ih => simpa [tree,rows,guard,Core.Expr.weakenAt] using congrArg (Option.map (Core.Expr.ifE (guard .zero) (.var 3))) ih
  exact .wordMatch (defaultEntry := some (branch,.apply (.var 1) (.var 2)))
    (.application (calleeElab false) argumentElab) (rowFacts n hit).1
    (fun entry member => by
      have meaning := ((rowFacts n hit).2 entry member).1; cases tag : entry.2.1 <;> simp only [tag] at meaning
      · exact .wildcard meaning.choose_spec
      · exact .literal meaning) (.inl rfl)
    (fun entry member => ((rowFacts n hit).2 entry member).2)
    rfl (by intro entry member; simp at member; subst entry
            exact .expression (.application (calleeElab true) argumentElab)) folded
private theorem chosen (n : Nat) (hit : Bool) : WordMatchChooses (.word one) (cases n hit) (some branch) branch (tests n hit) := by
  induction n with
  | zero => cases hit; exact .fallback; exact .hit (.literal (meaning true))
  | succ n ih => simpa [cases,tests,Nat.add_right_comm] using WordMatchChooses.miss (.literal (meaning false)) (by decide : one ≠ .zero) ih

private structure Actual where
  argument : Core.Value
  scrutineeBody : Core.Expr
  branchBody : Core.Expr
  scrutineeCapture : Core.Environment
  branchCapture : Core.Environment
  initial : Core.Store
  middle : Core.Store
  final : Core.Store
  result : Core.Value
  scrutineeCost : Nat
  branchCost : Nat
  scrutineePath : ∀ k, Core.Steps scrutineeCost ⟨.eval scrutineeBody (argument::scrutineeCapture),k,initial⟩ ⟨.ret (.word one),k,middle⟩
  branchPath : ∀ k, Core.Steps branchCost ⟨.eval branchBody (argument::branchCapture),k,middle⟩ ⟨.ret result,k,final⟩
private def function (a : Actual) (side : Bool) : Core.Value := .closure .word .word
  (if side then a.branchBody else a.scrutineeBody) (if side then a.branchCapture else a.scrutineeCapture)
private def env (a : Actual) : Resolved.Environment := [(id 0,function a false),(id 1,function a true),(id 2,a.argument)]
private def cost (a : Actual) (n : Nat) (hit : Bool) := (a.scrutineeCost+5)+(a.branchCost+5)+2+7*tests n hit
private theorem rawCall (a : Actual) (side : Bool) : RecursiveLocalComputationEvaluatesWithCost inputs.names (env a)
    (if side then a.middle else a.initial) (call side) (if side then a.result else .word one)
    (if side then a.final else a.middle) ((if side then a.branchCost else a.scrutineeCost)+5) := by
  have found : LocalExpressionEvaluatesWithCost inputs.names (env a)
      (if side then a.middle else a.initial) (ref (if side then "b" else "s")) (function a side)
      (if side then a.middle else a.initial) 1 :=
    .identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl))
      (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl))
  simpa [call,ref,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using RecursiveLocalComputationEvaluatesWithCost.application
    (.pure found) (.pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl) (Resolved.LocalScope.lookup?_iff.mp rfl)))
    (by cases side; exact a.scrutineePath []; exact a.branchPath [])
private theorem counted (a : Actual) (n : Nat) (hit : Bool) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n hit) a.result a.final (cost a n hit) :=
  .wordMatch (rawCall a false) (chosen n hit) (.expression (rawCall a true))
private theorem invoke {body : Core.Expr} {captured environment : Core.Environment} {argument value : Core.Value}
    {initial final : Core.Store} {count i j : Nat}
    (callee : environment[i]? = some (.closure .word .word body captured)) (arg : environment[j]? = some argument)
    (path : ∀ k, Core.Steps count ⟨.eval body (argument::captured),k,initial⟩ ⟨.ret value,k,final⟩) (k : List Core.Frame) :
    Core.Steps (count+5) ⟨.eval (.apply (.var i) (.var j)) environment,k,initial⟩ ⟨.ret value,k,final⟩ := by
  simpa [Nat.add_assoc] using Core.Steps.cons .enterApply
    (.cons (.var callee) (.cons .beginArgument (.cons (.var arg) (.cons .invokeClosure (path k)))))
private theorem treePath (a : Actual) (n : Nat) (hit : Bool) (k : List Core.Frame) :
    Core.Steps (a.branchCost+5+7*tests n hit) ⟨.eval (tree n hit) (.word one::(env a).values),k,a.middle⟩ ⟨.ret a.result,k,a.final⟩ := by
  have leaf := invoke (environment := .word one::(env a).values) (i := 2) (j := 3) rfl rfl a.branchPath k
  have test (word : Core.Word) (frames) : Core.Steps 5 ⟨.eval (guard word) (.word one::(env a).values),frames,a.middle⟩
      ⟨.ret (.bool (one == word)),frames,a.middle⟩ :=
    CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl) rfl
  induction n with
  | zero =>
      cases hit
      · exact leaf
      · have arithmetic : 5+(a.branchCost+5)+2=a.branchCost+5+7*tests 0 true := by simp [tests]; omega
        rw [← arithmetic]
        exact CostStepComposition.ifTrue (by simpa using test one _) leaf
  | succ n ih =>
      have arithmetic : 5+(a.branchCost+5+7*tests n hit)+2=a.branchCost+5+7*tests (n+1) hit := by unfold tests; omega
      have unequal : (one == Core.Word.zero)=false := by decide
      rw [← arithmetic]
      exact CostStepComposition.ifFalse (by simpa only [unequal] using test .zero _) ih
private theorem manual (a : Actual) (n : Nat) (hit : Bool) (k : List Core.Frame) :
    Core.Steps (cost a n hit) ⟨.eval (core n hit) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have arithmetic : (a.scrutineeCost+5)+(a.branchCost+5+7*tests n hit)+2=cost a n hit := by unfold cost; omega
  rw [← arithmetic]
  exact CostStepComposition.letE (invoke (environment := (env a).values) (i := 0) (j := 2) rfl rfl a.scrutineePath _) (treePath a n hit k)

theorem original_counted_source_and_independent_core (n : Nat) (hit : Bool) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n hit) (core n hit) .word ∧
    WordMatchChooses (.word one) (cases n hit) (some branch) branch (n + if hit then 1 else 0) :=
  ⟨elaborated n hit,chosen n hit⟩
theorem checker_and_both_typing_interfaces (n : Nat) (hit : Bool) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (source n hit)=some (core n hit,.word) ∧
    RecursiveComputationReturnTreeHasType [] owner inputs (source n hit) .word ∧
    Core.HasType inputs.context.values (core n hit) .word :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (elaborated n hit),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaborated n hit⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (elaborated n hit)⟩
theorem actual_effects_and_arbitrary_continuations (a : Actual) (n : Nat) (hit : Bool) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n hit) a.result a.final (cost a n hit) ∧
    ∀ k, Core.Steps (cost a n hit) ⟨.eval (core n hit) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨counted a n hit,manual a n hit⟩
theorem shared_cost_kernel_preserves_original_count (a : Actual) (n : Nat) (hit : Bool) (k : List Core.Frame) :
    Core.Steps (cost a n hit) ⟨.eval (core n hit) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (elaborated n hit) (environment := env a) rfl).mpr (manual a n hit [])
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
    RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation costed (elaborated n hit) rfl k
theorem cost_value_and_store_are_jointly_unique (a : Actual) (n : Nat) (hit : Bool)
    {value : Core.Value} {final : Core.Store} {count : Nat}
    (other : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n hit) value final count) :
    value=a.result ∧ final=a.final ∧ count=cost a n hit :=
  ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationEvaluatesWithCost.deterministic other (counted a n hit)
theorem generated_guards_and_actual_callers_survive_literal_insertion (a : Actual) (n : Nat) (hit : Bool)
    (leading suffix : Core.Environment) (inserted : Core.Value) (split : leading++suffix=(env a).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment ((core n hit).weakenAt leading.length) ∧
    Core.Evaluates (leading++inserted::suffix) a.initial ((core n hit).weakenAt leading.length) a.result a.final ∧
    ∀ k, Core.Steps (cost a n hit) ⟨.eval ((core n hit).weakenAt leading.length) (leading++inserted::suffix),k,a.initial⟩
      ⟨.ret a.result,k,a.final⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (elaborated n hit)
  have original := Core.steps_from_initial_sound (manual a n hit [])
  rw [← split] at original
  obtain ⟨common,paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths
    fragment leading suffix inserted original
  have known : Core.Steps (cost a n hit) (.initial (core n hit) (leading++suffix) a.initial) (.final a.result a.final) :=
    by rw [split]; exact manual a n hit []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    (ComputationBodyFragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff
      fragment leading suffix inserted).mpr original,fun k => same ▸ (paths k).2⟩
theorem all_fuels_and_full_checkpoint_resumption (a : Actual) (n : Nat) (hit : Bool) (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core n hit) (env a).values a.initial)=.outOfFuel cp) :
    (Core.runStateful fuel (.initial (core n hit) (env a).values a.initial)=.done a.result a.final ↔ cost a n hit≤fuel) ∧
    ((∃ saved, Core.runStateful fuel (.initial (core n hit) (env a).values a.initial)=.outOfFuel saved) ↔ fuel<cost a n hit) ∧
    spent<cost a n hit ∧ Core.Steps (cost a n hit-spent) cp (.final a.result a.final) ∧
    Core.runStateful additional cp=Core.runStateful (spent+additional) (.initial (core n hit) (env a).values a.initial) := by
  have path := shared_cost_kernel_preserves_original_count a n hit []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,path.runStateful_outOfFuel_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩

private theorem missPrefix (a : Actual) (passed remaining : Nat) (hit : Bool) (k : List Core.Frame) :
    Core.Steps (7*passed) ⟨.eval (tree (passed+remaining) hit) (.word one::(env a).values),k,a.middle⟩
      ⟨.eval (tree remaining hit) (.word one::(env a).values),k,a.middle⟩ := by
  induction passed with
  | zero => simpa using (Core.Steps.refl (state := ⟨.eval (tree remaining hit) (.word one::(env a).values),k,a.middle⟩))
  | succ passed ih =>
      have arithmetic : 7*(passed+1)=7*passed+7 := by omega
      rw [arithmetic,Nat.add_right_comm passed 1 remaining]
      simp only [tree]
      exact Core.Steps.cons .enterIf
        (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons .word
          (.cons (.applyBinary (by simp [Core.BinaryOp.apply,show (one == Core.Word.zero)=false from by decide]))
            (.cons .chooseFalse ih))))))
theorem each_visited_prefix_is_a_genuine_checkpoint (a : Actual) (passed remaining : Nat) (hit : Bool) (k : List Core.Frame) :
    let start : Core.State := ⟨.eval (core (passed+remaining) hit) (env a).values,k,a.initial⟩
    let cp : Core.State := ⟨.eval (tree remaining hit) (.word one::(env a).values),k,a.middle⟩
    Core.runStateful (a.scrutineeCost+7+7*passed) start=.outOfFuel cp ∧
    ∀ additional, Core.runStateful additional cp=Core.runStateful (a.scrutineeCost+7+7*passed+additional) start := by
  dsimp only
  have prefixPath := Core.Steps.cons .enterLet
    ((invoke (environment := (env a).values) (i := 0) (j := 2) rfl rfl a.scrutineePath _).trans
      (.cons .bindLet (missPrefix a passed remaining hit k)))
  have pending : ∃ next, Core.advance ⟨.eval (tree remaining hit) (.word one::(env a).values),k,a.middle⟩=.next next := by
    cases remaining <;> cases hit <;> exact ⟨_,rfl⟩
  have exhausted := Core.runStateful_outOfFuel_complete prefixPath pending.choose_spec
  have arithmetic : a.scrutineeCost+7+7*passed=(a.scrutineeCost+5+(7*passed+1))+1 := by omega
  rw [← arithmetic] at exhausted
  exact ⟨exhausted,Core.runStateful_resume exhausted⟩
theorem first_match_ignores_duplicate_and_malformed_later_rows (extra : List Syntax.MatchCase)
    (defaultBody : Syntax.Block) :
    WordMatchChooses (.word one) (arm true::arm true::⟨span,⟨⟨span,.error⟩,unused⟩⟩::extra) (some defaultBody) branch 1 :=
  .hit (.literal (meaning true))
theorem malformed_first_row_cannot_be_skipped (actual : Core.Value) (extra : List Syntax.MatchCase)
    (defaultBody selected : Syntax.Block) (count : Nat) :
    ¬ WordMatchChooses actual (⟨span,⟨⟨span,.error⟩,unused⟩⟩::extra) (some defaultBody) selected count := by
  intro choice
  cases choice with
  | wildcard meaning => cases meaning with | wildcard shape => cases shape
  | hit meaning | miss meaning _ _ =>
      cases meaning with | literal meaning => rcases meaning with ⟨literal,shape,_⟩; cases shape
theorem selected_body_and_visited_count_ignore_no_earlier_test (n : Nat) (hit : Bool)
    {selected : Syntax.Block} {count : Nat}
    (choice : WordMatchChooses (.word one) (cases n hit) (some branch) selected count) :
    selected=branch ∧ count=n+(if hit then 1 else 0) := choice.deterministic (chosen n hit)

private def allocating (word : Core.Word) : Core.Expr := .letE (.newCell .word (.var 0)) (.word word)
private theorem allocationPath (word result : Core.Word) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval (allocating result) (.word word::captured),k,s⟩ ⟨.ret (.word result),k,s++[.word word]⟩ :=
  CostStepComposition.letE (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))) (.cons .word .refl)
private def effects (word : Core.Word) (left right : Core.Environment) (s : Core.Store) : Actual :=
  ⟨.word word,allocating one,allocating word,left,right,s,s++[.word word],(s++[.word word])++[.word word],.word word,6,6,
    allocationPath word one left s,allocationPath word word right (s++[.word word])⟩
theorem both_actual_calls_allocate_with_exact_captures (n : Nat) (hit : Bool) (word : Core.Word)
    (left right : Core.Environment) (s : Core.Store) :
    let a := effects word left right s
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (source n hit) (.word word)
      (s++[.word word,.word word]) (24+7*tests n hit) ∧
    ∀ k, Core.Steps (24+7*tests n hit) ⟨.eval (core n hit) (env a).values,k,s⟩
      ⟨.ret (.word word),k,s++[.word word,.word word]⟩ := by
  simpa [effects,cost,List.append_assoc] using actual_effects_and_arbitrary_continuations (effects word left right s) n hit

end Tests.FrontendWordMatchCount
