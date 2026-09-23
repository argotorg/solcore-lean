import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.Computation
import Solcore.Core.FuelResumptionProperties

/-! Symbolic original syntax, not a parser-output claim. The independently typed
suffix remains in the source after selection. Actual closure paths may change
stores; no runtime typing is assumed. -/
set_option autoImplicit false
namespace Tests.FrontendWildcardMatchCount
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WildcardCount",by decide⟩],by decide⟩⟩,109⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-wildcard-count.sol"⟩,0,128⟩
private def one : Core.Word := ⟨1,by decide⟩
private def inputs : LocalTypeInputs := ⟨[⟨"s",id 0,.function .word .word⟩,
  ⟨"b",id 1,.function .word .word⟩,⟨"x",id 2,.word⟩],by change [id 0,id 1,id 2].Nodup; decide⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call (side : Bool) : Syntax.Expr := ⟨span,.call (ref (if side then "b" else "s")) ⟨span,[ref "x"]⟩⟩
private def branch : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (call true))⟩]⟩
private def unused : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩
private def miss : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,unused⟩⟩
private def wildcard (marker : Syntax.SourceSpan) : Syntax.MatchCase := ⟨span,⟨⟨span,.wildcard marker⟩,branch⟩⟩
private def cases : Nat → Syntax.SourceSpan → List Syntax.MatchCase → List Syntax.MatchCase
  | 0,marker,extra => wildcard marker :: extra
  | n+1,marker,extra => miss :: cases n marker extra
private theorem meaning : WordMatchPatternDenotes miss.value.pattern .zero :=
  ⟨⟨span,.decimal "0"⟩,rfl,.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩
private theorem calleeElab (side : Bool) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref (if side then "b" else "s")) (.var (if side then 1 else 0)) (.function .word .word) :=
  .pure (.identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl)))
private theorem argumentElab : RecursiveLocalComputationElaborates inputs.names inputs.context (ref "x") (.var 2) .word :=
  .pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private structure Suffix where
  original : List Syntax.MatchCase
  rows : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  ordered : rows.map Prod.fst = original
  meanings : ∀ entry ∈ rows, match entry.2.1 with
    | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
    | some word => WordMatchPatternDenotes entry.1.value.pattern word
  branches : ∀ entry ∈ rows, RecursiveComputationReturnTreeElaborates [] owner inputs entry.1.value.body entry.2.2 .word
private def repeatedSuffix : List (Bool × Syntax.SourceSpan) → Suffix
  | [] => ⟨[],[],rfl,by simp,by simp⟩
  | (isWild,marker)::rest =>
      let tail := repeatedSuffix rest
      ⟨(if isWild then wildcard marker else miss)::tail.original,
        ((if isWild then wildcard marker else miss),(if isWild then none else some .zero),
          (if isWild then .apply (.var 1) (.var 2) else .var 2))::tail.rows,
        by simp [tail.ordered],
        by intro entry member; rcases List.mem_cons.mp member with rfl | member
           · cases isWild; exact meaning; exact ⟨marker,rfl⟩
           · exact tail.meanings entry member,
        by intro entry member; rcases List.mem_cons.mp member with rfl | member
           · cases isWild
             · exact .expression argumentElab
             · exact .expression (.application (calleeElab true) argumentElab)
           · exact tail.branches entry member⟩
private def source (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨call false,[]⟩⟩ ⟨span,⟨cases n marker suffix.original,some branch⟩⟩⟩]⟩
private def guard : Core.Expr := .binary .wordEq (.var 0) (.word .zero)
private def selectedCore : Core.Expr := .apply (.var 2) (.var 3)
private def tree : Nat → Core.Expr
  | 0 => selectedCore
  | n+1 => .ifE guard (.var 3) (tree n)
private def core (n : Nat) : Core.Expr := .letE (.apply (.var 0) (.var 2)) (tree n)
private def rows : Nat → Syntax.SourceSpan → Suffix → List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  | 0,marker,suffix => (wildcard marker,none,.apply (.var 1) (.var 2)) :: suffix.rows
  | n+1,marker,suffix => (miss,some .zero,.var 2) :: rows n marker suffix
private theorem rowFacts (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    (rows n marker suffix).map Prod.fst = cases n marker suffix.original ∧ ∀ entry ∈ rows n marker suffix,
      (match entry.2.1 with
        | none => ∃ marker, entry.1.value.pattern.value = .wildcard marker
        | some word => WordMatchPatternDenotes entry.1.value.pattern word) ∧
      RecursiveComputationReturnTreeElaborates [] owner inputs entry.1.value.body entry.2.2 .word := by
  induction n with
  | zero =>
      refine ⟨by simp [rows,cases,suffix.ordered],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨⟨marker,rfl⟩,.expression (.application (calleeElab true) argumentElab)⟩
      · exact ⟨suffix.meanings entry member,suffix.branches entry member⟩
  | succ n ih =>
      refine ⟨by simp [rows,cases,ih.1],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨meaning,.expression argumentElab⟩
      · exact ih.2 entry member
private theorem elaborated (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n marker suffix) (core n) .word := by
  have folded : (rows n marker suffix).foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun t => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) t))
      (some ((.apply (.var 1) (.var 2) : Core.Expr).weakenAt 0)) = some (tree n) := by
    induction n with
    | zero => simp [tree,rows,selectedCore,Core.Expr.weakenAt]
    | succ n ih => simpa [tree,rows,guard,Core.Expr.weakenAt] using congrArg (Option.map (Core.Expr.ifE guard (.var 3))) ih
  exact .wordMatch (defaultEntry := some (branch,.apply (.var 1) (.var 2)))
    (.application (calleeElab false) argumentElab) (rowFacts n marker suffix).1
    (fun entry member => by
      have meaning := ((rowFacts n marker suffix).2 entry member).1; cases tag : entry.2.1 <;> simp only [tag] at meaning
      · exact .wildcard meaning.choose_spec
      · exact .literal meaning) (.inl rfl)
    (fun entry member => ((rowFacts n marker suffix).2 entry member).2)
    rfl (by intro entry member; simp at member; subst entry
            exact .expression (.application (calleeElab true) argumentElab)) folded
private theorem chosen (n : Nat) (marker : Syntax.SourceSpan) (extra : List Syntax.MatchCase) (fallback : Syntax.Block) :
    WordMatchChooses (.word one) (cases n marker extra) (some fallback) branch n := by
  induction n with
  | zero => exact .wildcard (.wildcard rfl)
  | succ n ih => exact .miss (.literal meaning) (by decide : one ≠ .zero) ih

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
private def cost (a : Actual) (n : Nat) := a.scrutineeCost+a.branchCost+12+7*n
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
private theorem counted (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial
      (source n marker suffix) a.result a.final (cost a n) := by
  simpa [source,cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    ComputationReturnTreeEvaluatesWithCost.wordMatch (rawCall a false) (chosen n marker suffix.original branch) (.expression (rawCall a true))
private theorem invoke {body : Core.Expr} {captured environment : Core.Environment} {argument value : Core.Value}
    {initial final : Core.Store} {count i j : Nat}
    (callee : environment[i]? = some (.closure .word .word body captured)) (arg : environment[j]? = some argument)
    (path : ∀ k, Core.Steps count ⟨.eval body (argument::captured),k,initial⟩ ⟨.ret value,k,final⟩) (k : List Core.Frame) :
    Core.Steps (count+5) ⟨.eval (.apply (.var i) (.var j)) environment,k,initial⟩ ⟨.ret value,k,final⟩ := by
  simpa [Nat.add_assoc] using Core.Steps.cons .enterApply
    (.cons (.var callee) (.cons .beginArgument (.cons (.var arg) (.cons .invokeClosure (path k)))))
private theorem treePath (a : Actual) (n : Nat) (k : List Core.Frame) :
    Core.Steps (a.branchCost+5+7*n) ⟨.eval (tree n) (.word one::(env a).values),k,a.middle⟩ ⟨.ret a.result,k,a.final⟩ := by
  induction n with
  | zero => exact invoke (environment := .word one::(env a).values) (i := 2) (j := 3) rfl rfl a.branchPath k
  | succ n ih =>
      have test (frames) : Core.Steps 5 ⟨.eval guard (.word one::(env a).values),frames,a.middle⟩
          ⟨.ret (.bool false),frames,a.middle⟩ :=
        CostStepComposition.binary (.cons (.var rfl) .refl) (.cons .word .refl)
          (by simp [Core.BinaryOp.apply,show (one == Core.Word.zero)=false from by decide])
      have arithmetic : 5+(a.branchCost+5+7*n)+2=a.branchCost+5+7*(n+1) := by omega
      rw [← arithmetic]
      exact CostStepComposition.ifFalse (test _) ih
private theorem manual (a : Actual) (n : Nat) (k : List Core.Frame) :
    Core.Steps (cost a n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have arithmetic : (a.scrutineeCost+5)+(a.branchCost+5+7*n)+2=cost a n := by unfold cost; omega
  rw [← arithmetic]
  exact CostStepComposition.letE (invoke (environment := (env a).values) (i := 0) (j := 2) rfl rfl a.scrutineePath _) (treePath a n k)

theorem original_prefix_wildcard_and_all_typed_suffix_rows (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n marker suffix) (core n) .word ∧
    WordMatchChooses (.word one) (cases n marker suffix.original) (some branch) branch n :=
  ⟨elaborated n marker suffix,chosen n marker suffix.original branch⟩
theorem checker_and_both_typing_interfaces (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (source n marker suffix)=some (core n,.word) ∧
    RecursiveComputationReturnTreeHasType [] owner inputs (source n marker suffix) .word ∧
    Core.HasType inputs.context.values (core n) .word :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (elaborated n marker suffix),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaborated n marker suffix⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (elaborated n marker suffix)⟩
theorem actual_effects_and_independent_literal_paths (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n marker suffix) a.result a.final (cost a n) ∧
    ∀ k, Core.Steps (cost a n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨counted a n marker suffix,manual a n⟩
theorem shared_cost_kernel_preserves_the_literal_count (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) (k : List Core.Frame) :
    Core.Steps (cost a n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (elaborated n marker suffix) (environment := env a) rfl).mpr (manual a n [])
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
    RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation costed (elaborated n marker suffix) rfl k
theorem cost_value_and_store_are_jointly_unique (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix)
    {value : Core.Value} {final : Core.Store} {count : Nat}
    (other : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n marker suffix) value final count) :
    value=a.result ∧ final=a.final ∧ count=cost a n :=
  ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationEvaluatesWithCost.deterministic other (counted a n marker suffix)
theorem exact_literal_insertion_preserves_actual_values_and_captures (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix)
    (leading trailing : Core.Environment) (inserted : Core.Value) (split : leading++trailing=(env a).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment ((core n).weakenAt leading.length) ∧
    Core.Evaluates (leading++inserted::trailing) a.initial ((core n).weakenAt leading.length) a.result a.final ∧
    ∀ k, Core.Steps (cost a n) ⟨.eval ((core n).weakenAt leading.length) (leading++inserted::trailing),k,a.initial⟩
      ⟨.ret a.result,k,a.final⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (elaborated n marker suffix)
  have original := Core.steps_from_initial_sound (manual a n [])
  rw [← split] at original
  obtain ⟨common,paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths fragment leading trailing inserted original
  have known : Core.Steps (cost a n) (.initial (core n) (leading++trailing) a.initial) (.final a.result a.final) := by rw [split]; exact manual a n []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    (ComputationBodyFragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff fragment leading trailing inserted).mpr original,
    fun k => same ▸ (paths k).2⟩
theorem all_fuels_and_full_checkpoint_resumption (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core n) (env a).values a.initial)=.outOfFuel cp) :
    (Core.runStateful fuel (.initial (core n) (env a).values a.initial)=.done a.result a.final ↔ cost a n≤fuel) ∧
    ((∃ saved, Core.runStateful fuel (.initial (core n) (env a).values a.initial)=.outOfFuel saved) ↔ fuel<cost a n) ∧
    spent<cost a n ∧ Core.Steps (cost a n-spent) cp (.final a.result a.final) ∧
    Core.runStateful additional cp=Core.runStateful (spent+additional) (.initial (core n) (env a).values a.initial) := by
  have path := shared_cost_kernel_preserves_the_literal_count a n marker suffix []
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨path.runStateful_done_iff,path.runStateful_outOfFuel_iff,residual.1,residual.2,Core.runStateful_resume exhausted additional⟩
private theorem missPrefix (a : Actual) (passed remaining : Nat) (k : List Core.Frame) :
    Core.Steps (7*passed) ⟨.eval (tree (passed+remaining)) (.word one::(env a).values),k,a.middle⟩
      ⟨.eval (tree remaining) (.word one::(env a).values),k,a.middle⟩ := by
  induction passed with
  | zero => simpa using (Core.Steps.refl (state := ⟨.eval (tree remaining) (.word one::(env a).values),k,a.middle⟩))
  | succ passed ih =>
      have arithmetic : 7*(passed+1)=7*passed+7 := by omega
      rw [arithmetic,Nat.add_right_comm passed 1 remaining]
      simp only [tree]
      exact Core.Steps.cons .enterIf (.cons .enterBinary (.cons (.var rfl) (.cons .enterBinaryRight (.cons .word
        (.cons (.applyBinary (by simp [Core.BinaryOp.apply,show (one == Core.Word.zero)=false from by decide])) (.cons .chooseFalse ih))))))
theorem each_visited_prefix_is_a_genuine_checkpoint (a : Actual) (passed remaining : Nat) (k : List Core.Frame) :
    let start : Core.State := ⟨.eval (core (passed+remaining)) (env a).values,k,a.initial⟩
    let cp : Core.State := ⟨.eval (tree remaining) (.word one::(env a).values),k,a.middle⟩
    Core.runStateful (a.scrutineeCost+7+7*passed) start=.outOfFuel cp ∧
    ∀ additional, Core.runStateful additional cp=Core.runStateful (a.scrutineeCost+7+7*passed+additional) start := by
  dsimp only
  have prefixPath := Core.Steps.cons .enterLet
    ((invoke (environment := (env a).values) (i := 0) (j := 2) rfl rfl a.scrutineePath _).trans (.cons .bindLet (missPrefix a passed remaining k)))
  have pending : ∃ next, Core.advance ⟨.eval (tree remaining) (.word one::(env a).values),k,a.middle⟩=.next next := by
    cases remaining <;> exact ⟨_,rfl⟩
  have exhausted := Core.runStateful_outOfFuel_complete prefixPath pending.choose_spec
  have arithmetic : a.scrutineeCost+7+7*passed=(a.scrutineeCost+5+(7*passed+1))+1 := by omega
  rw [← arithmetic] at exhausted
  exact ⟨exhausted,Core.runStateful_resume exhausted⟩
theorem first_wildcard_beats_duplicate_wildcards_and_any_later_rows (n : Nat) (marker later : Syntax.SourceSpan)
    (extra : List Syntax.MatchCase) (fallback : Syntax.Block) :
    WordMatchChooses (.word one) (cases n marker (⟨span,⟨⟨span,.wildcard later⟩,unused⟩⟩::miss::extra)) (some fallback) branch n ∧
    ∀ selected count, WordMatchChooses (.word one) (cases n marker (⟨span,⟨⟨span,.wildcard later⟩,unused⟩⟩::miss::extra)) (some fallback) selected count →
      selected=branch ∧ count=n :=
  ⟨chosen n marker _ fallback,fun _ _ other => other.deterministic (chosen n marker _ fallback)⟩
theorem arbitrarily_repeated_suffix_rows_are_checked_without_extra_comparisons
    (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (extra : List (Bool × Syntax.SourceSpan)) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n marker (repeatedSuffix extra)) (core n) .word ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial
      (source n marker (repeatedSuffix extra)) a.result a.final (a.scrutineeCost+a.branchCost+12+7*n) ∧
    ∀ k, Core.Steps (a.scrutineeCost+a.branchCost+12+7*n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨elaborated n marker (repeatedSuffix extra),actual_effects_and_independent_literal_paths a n marker (repeatedSuffix extra)⟩
private def allocating (word : Core.Word) : Core.Expr := .letE (.newCell .word (.var 0)) (.word word)
private theorem allocationPath (word result : Core.Word) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval (allocating result) (.word word::captured),k,s⟩ ⟨.ret (.word result),k,s++[.word word]⟩ :=
  CostStepComposition.letE (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))) (.cons .word .refl)
private def effects (word : Core.Word) (left right : Core.Environment) (s : Core.Store) : Actual :=
  ⟨.word word,allocating one,allocating word,left,right,s,s++[.word word],(s++[.word word])++[.word word],.word word,6,6,
    allocationPath word one left s,allocationPath word word right (s++[.word word])⟩
theorem both_actual_calls_allocate_with_exact_captures (n : Nat) (marker : Syntax.SourceSpan) (suffix : Suffix) (word : Core.Word)
    (left right : Core.Environment) (s : Core.Store) :
    let a := effects word left right s
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (source n marker suffix) (.word word)
      (s++[.word word,.word word]) (24+7*n) ∧
    ∀ k, Core.Steps (24+7*n) ⟨.eval (core n) (env a).values,k,s⟩ ⟨.ret (.word word),k,s++[.word word,.word word]⟩ := by
  simpa [effects,cost,List.append_assoc] using actual_effects_and_independent_literal_paths (effects word left right s) n marker suffix

end Tests.FrontendWildcardMatchCount
