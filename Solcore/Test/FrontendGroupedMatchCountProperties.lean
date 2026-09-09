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

/-! Original symbolic groups retain arbitrary, independent outer spans and the
wildcard marker. This is not a parser-span claim. Actual closure paths retain
their captures and store effects; no runtime typing is presumed. -/
set_option autoImplicit false
namespace Tests.FrontendGroupedMatchCount
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"GroupedMatchCount",by decide⟩],by decide⟩⟩,116⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-grouped-count.sol"⟩,0,128⟩
private def one : Core.Word := ⟨1,by decide⟩
private def inputs : LocalTypeInputs := ⟨[⟨"s",id 0,.function .word .word⟩,
  ⟨"b",id 1,.function .word .word⟩,⟨"x",id 2,.word⟩],by change [id 0,id 1,id 2].Nodup; decide⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def call (side : Bool) : Syntax.Expr := ⟨span,.call (ref (if side then "b" else "s")) ⟨span,[ref "x"]⟩⟩
private def branch : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (call true))⟩]⟩
private def unused : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "x"))⟩]⟩
private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [],pattern => pattern
  | outer::rest,pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapped {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) (spans : List Syntax.SourceSpan) :
    WordMatchPatternClassifies (wrap spans pattern) tag := by
  induction spans with | nil => exact meaning | cons _ _ ih => exact .group ih
private structure Suffix where
  original : List Syntax.MatchCase
  rows : List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  ordered : rows.map Prod.fst = original
  meanings : ∀ entry ∈ rows, WordMatchPatternClassifies entry.1.value.pattern entry.2.1
  branches : ∀ entry ∈ rows, RecursiveComputationReturnTreeElaborates [] owner inputs entry.1.value.body entry.2.2 .word
private structure Shape where
  literalGroups : Nat → List Syntax.SourceSpan
  wildcardGroups : List Syntax.SourceSpan
  marker : Syntax.SourceSpan
  suffix : Suffix
  hasDefault : Bool
private def miss (shape : Shape) (n : Nat) : Syntax.MatchCase :=
  ⟨span,⟨wrap (shape.literalGroups n) ⟨span,.literal ⟨span,.decimal "0"⟩⟩,unused⟩⟩
private def wildcard (shape : Shape) : Syntax.MatchCase :=
  ⟨span,⟨wrap shape.wildcardGroups ⟨span,.wildcard shape.marker⟩,branch⟩⟩
private def cases : Nat → Shape → List Syntax.MatchCase
  | 0,shape => wildcard shape :: shape.suffix.original
  | n+1,shape => miss shape n :: cases n shape
private def defaultBody (shape : Shape) : Option Syntax.Block := if shape.hasDefault then some branch else none
private theorem meaning (shape : Shape) (n : Nat) :
    WordMatchPatternClassifies (miss shape n).value.pattern (some .zero) :=
  wrapped (.literal ⟨⟨span,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩) _
private theorem calleeElab (side : Bool) : RecursiveLocalComputationElaborates inputs.names inputs.context
    (ref (if side then "b" else "s")) (.var (if side then 1 else 0)) (.function .word .word) :=
  .pure (.identifier (id := id (if side then 1 else 0)) (LocalNameTable.lookup?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.index?_iff.mp (by cases side <;> rfl)))
    (.var (Resolved.LocalScope.lookup?_iff.mp (by cases side <;> rfl)))
private theorem argumentElab : RecursiveLocalComputationElaborates inputs.names inputs.context (ref "x") (.var 2) .word :=
  .pure (.identifier (id := id 2) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private def source (n : Nat) (shape : Shape) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨call false,[]⟩⟩ ⟨span,⟨cases n shape,defaultBody shape⟩⟩⟩]⟩
private def guard : Core.Expr := .binary .wordEq (.var 0) (.word .zero)
private def selectedCore : Core.Expr := .apply (.var 2) (.var 3)
private def tree : Nat → Core.Expr
  | 0 => selectedCore
  | n+1 => .ifE guard (.var 3) (tree n)
private def core (n : Nat) : Core.Expr := .letE (.apply (.var 0) (.var 2)) (tree n)
private def rows : Nat → Shape → List (Syntax.MatchCase × (Option Core.Word × Core.Expr))
  | 0,shape => (wildcard shape,none,.apply (.var 1) (.var 2)) :: shape.suffix.rows
  | n+1,shape => (miss shape n,some .zero,.var 2) :: rows n shape
private theorem rowFacts (n : Nat) (shape : Shape) :
    (rows n shape).map Prod.fst = cases n shape ∧ ∀ entry ∈ rows n shape,
      WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧
      RecursiveComputationReturnTreeElaborates [] owner inputs entry.1.value.body entry.2.2 .word := by
  induction n with
  | zero =>
      refine ⟨by simp [rows,cases,shape.suffix.ordered],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨wrapped (.wildcard rfl) shape.wildcardGroups,.expression (.application (calleeElab true) argumentElab)⟩
      · exact ⟨shape.suffix.meanings entry member,shape.suffix.branches entry member⟩
  | succ n ih =>
      refine ⟨by simp [rows,cases,ih.1],?_⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨meaning shape n,.expression argumentElab⟩
      · exact ih.2 entry member
private def defaultEntry (shape : Shape) : Option (Syntax.Block × Core.Expr) :=
  if shape.hasDefault then some (branch,.apply (.var 1) (.var 2)) else none
private theorem elaborated (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n shape) (core n) .word := by
  have folded : (rows n shape).foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun t => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) t))
      ((defaultEntry shape).map (fun entry => entry.2.weakenAt 0)) = some (tree n) := by
    induction n with
    | zero => simp [tree,rows,selectedCore,Core.Expr.weakenAt]
    | succ n ih => simpa [tree,rows,guard,Core.Expr.weakenAt] using congrArg (Option.map (Core.Expr.ifE guard (.var 3))) ih
  exact .wordMatch (defaultEntry := defaultEntry shape)
    (.application (calleeElab false) argumentElab) (rowFacts n shape).1
    (fun entry member => ((rowFacts n shape).2 entry member).1)
    (fun entry member => ((rowFacts n shape).2 entry member).2)
    (by cases choice : shape.hasDefault <;> simp [defaultEntry,defaultBody,choice])
    (by intro entry member; cases choice : shape.hasDefault <;> simp [defaultEntry,choice] at member
        subst entry; exact .expression (.application (calleeElab true) argumentElab)) folded
private theorem chosen (n : Nat) (shape : Shape) :
    WordMatchChooses (.word one) (cases n shape) (defaultBody shape) branch n := by
  induction n with
  | zero => exact .wildcard (wrapped (.wildcard rfl) shape.wildcardGroups)
  | succ n ih => exact .miss (meaning shape n) (by decide : one ≠ .zero) ih

theorem arbitrary_original_group_spans_preserve_classification
    (spans : List Syntax.SourceSpan) {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) :
    WordMatchPatternClassifies (wrap spans pattern) tag ∧ interpretWordMatchPattern? (wrap spans pattern)=some tag :=
  ⟨wrapped meaning spans,interpretWordMatchPattern?_iff.mpr (wrapped meaning spans)⟩

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
private theorem counted (a : Actual) (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial
      (source n shape) a.result a.final (cost a n) := by
  simpa [source,cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    ComputationReturnTreeEvaluatesWithCost.wordMatch (rawCall a false) (chosen n shape) (.expression (rawCall a true))
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

theorem original_grouped_prefix_and_all_typed_suffix_rows (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n shape) (core n) .word ∧
    WordMatchChooses (.word one) (cases n shape) (defaultBody shape) branch n :=
  ⟨elaborated n shape,chosen n shape⟩
theorem checker_and_both_typing_interfaces (n : Nat) (shape : Shape) :
    elaborateRecursiveComputationReturnTree? [] owner inputs (source n shape)=some (core n,.word) ∧
    RecursiveComputationReturnTreeHasType [] owner inputs (source n shape) .word ∧
    Core.HasType inputs.context.values (core n) .word :=
  ⟨(elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (elaborated n shape),
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaborated n shape⟩,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType (elaborated n shape)⟩
theorem actual_effects_and_independent_literal_paths (a : Actual) (n : Nat) (shape : Shape) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n shape) a.result a.final (cost a n) ∧
    ∀ k, Core.Steps (cost a n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨counted a n shape,manual a n⟩
theorem shared_cost_kernel_preserves_the_literal_count (a : Actual) (n : Nat) (shape : Shape) (k : List Core.Frame) :
    Core.Steps (cost a n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ := by
  have costed := (ComputationReturnTreeElaborates.evaluatesWithCost_iff_steps
    (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates)
    (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt
    RecursiveLocalComputationFragment.evaluates_insert_iff RecursiveLocalComputationElaborates.evaluates_iff
    recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (elaborated n shape) (environment := env a) rfl).mpr (manual a n [])
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment)
    (ChildElab := RecursiveLocalComputationElaborates) RecursiveLocalComputationElaborates.core_fragment
    RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths
    RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation costed (elaborated n shape) rfl k
theorem cost_value_and_store_are_jointly_unique (a : Actual) (n : Nat) (shape : Shape)
    {value : Core.Value} {final : Core.Store} {count : Nat}
    (other : RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial (source n shape) value final count) :
    value=a.result ∧ final=a.final ∧ count=cost a n :=
  ComputationReturnTreeEvaluatesWithCost.deterministic (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
    RecursiveLocalComputationEvaluatesWithCost.deterministic other (counted a n shape)
theorem exact_literal_insertion_preserves_actual_values_and_captures (a : Actual) (n : Nat) (shape : Shape)
    (leading trailing : Core.Environment) (inserted : Core.Value) (split : leading++trailing=(env a).values) :
    ComputationBodyFragment RecursiveLocalComputationFragment ((core n).weakenAt leading.length) ∧
    Core.Evaluates (leading++inserted::trailing) a.initial ((core n).weakenAt leading.length) a.result a.final ∧
    ∀ k, Core.Steps (cost a n) ⟨.eval ((core n).weakenAt leading.length) (leading++inserted::trailing),k,a.initial⟩
      ⟨.ret a.result,k,a.final⟩ := by
  have fragment := ComputationReturnTreeElaborates.core_fragment (F := RecursiveLocalComputationFragment)
    RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt (elaborated n shape)
  have original := Core.steps_from_initial_sound (manual a n [])
  rw [← split] at original
  obtain ⟨common,paths⟩ := ComputationBodyFragment.insertion_paths RecursiveLocalComputationFragment.insertion_paths fragment leading trailing inserted original
  have known : Core.Steps (cost a n) (.initial (core n) (leading++trailing) a.initial) (.final a.result a.final) := by rw [split]; exact manual a n []
  have same := ((paths []).1.final_unique known).1
  exact ⟨fragment.weakenAt RecursiveLocalComputationFragment.weakenAt _,
    (ComputationBodyFragment.evaluates_insert_iff RecursiveLocalComputationFragment.evaluates_insert_iff fragment leading trailing inserted).mpr original,
    fun k => same ▸ (paths k).2⟩
theorem all_fuels_and_full_checkpoint_resumption (a : Actual) (n : Nat) (shape : Shape)
    (fuel spent additional : Nat) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (core n) (env a).values a.initial)=.outOfFuel cp) :
    (Core.runStateful fuel (.initial (core n) (env a).values a.initial)=.done a.result a.final ↔ cost a n≤fuel) ∧
    ((∃ saved, Core.runStateful fuel (.initial (core n) (env a).values a.initial)=.outOfFuel saved) ↔ fuel<cost a n) ∧
    spent<cost a n ∧ Core.Steps (cost a n-spent) cp (.final a.result a.final) ∧
    Core.runStateful additional cp=Core.runStateful (spent+additional) (.initial (core n) (env a).values a.initial) := by
  have path := shared_cost_kernel_preserves_the_literal_count a n shape []
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
private def allocating (word : Core.Word) : Core.Expr := .letE (.newCell .word (.var 0)) (.word word)
private theorem allocationPath (word result : Core.Word) (captured : Core.Environment) (s : Core.Store) (k : List Core.Frame) :
    Core.Steps 6 ⟨.eval (allocating result) (.word word::captured),k,s⟩ ⟨.ret (.word result),k,s++[.word word]⟩ :=
  CostStepComposition.letE (.cons .enterNewCell (.cons (.var rfl) (.cons .applyNewCell .refl))) (.cons .word .refl)
private def effects (word : Core.Word) (left right : Core.Environment) (s : Core.Store) : Actual :=
  ⟨.word word,allocating one,allocating word,left,right,s,s++[.word word],(s++[.word word])++[.word word],.word word,6,6,
    allocationPath word one left s,allocationPath word word right (s++[.word word])⟩
theorem both_actual_calls_allocate_with_exact_captures (n : Nat) (shape : Shape) (word : Core.Word)
    (left right : Core.Environment) (s : Core.Store) :
    let a := effects word left right s
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) s (source n shape) (.word word)
      (s++[.word word,.word word]) (24+7*n) ∧
    ∀ k, Core.Steps (24+7*n) ⟨.eval (core n) (env a).values,k,s⟩ ⟨.ret (.word word),k,s++[.word word,.word word]⟩ := by
  simpa [effects,cost,List.append_assoc] using actual_effects_and_independent_literal_paths (effects word left right s) n shape

theorem literal_only_suffix_stays_unlowerable_but_grouped_wildcard_recovers (n : Nat) (shape : Shape)
    (literalOnly : ∀ entry ∈ shape.suffix.rows, ∃ word, entry.2.1 = some word) :
    shape.suffix.rows.foldr (fun entry tail => match entry.2.1 with
      | none => some (entry.2.2.weakenAt 0)
      | some word => tail.map (fun t => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) t))
      (none : Option Core.Expr) = none ∧
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n {shape with hasDefault := false}) (core n) .word := by
  refine ⟨?_,elaborated n _⟩
  generalize shape.suffix.rows = entries at *
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨word,tag⟩ := literalOnly entry (by simp)
      simp only [List.foldr_cons,tag,ih (fun item member => literalOnly item (by simp [member])),Option.map_none]
end Tests.FrontendGroupedMatchCount
