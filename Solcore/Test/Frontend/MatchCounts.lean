import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties
import Solcore.Syntax.Parser.Internal.TermBasics
import Solcore.Frontend.RecursiveComputationFunction
import Solcore.Frontend.RuntimeComputationFunction
import Solcore.Frontend.RuntimeArgumentConstruction
import Solcore.Frontend.RuntimeInputValidation
import Solcore.Frontend.LocalExpressionLookupProperties
import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.LocalName
import Solcore.Resolved.Renaming

/-!
# Match tests

Parsed match forms over words, wildcards, optionals, grouped patterns and general types: source costs,
scopes, effects, and raw lookup.
-/

section
-- leanmerge: from Solcore.Test.FrontendGroupedMatchBoundaryProperties
/-! Arbitrary original group spans are symbolic syntax, not parser-validity
claims. Independent source costs and literal paths precede the shared laws. -/
set_option autoImplicit false
namespace Tests.FrontendGroupedMatchBoundary
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment
open RecursiveLocalComputationEvaluatesWithCost

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"GroupedMatchBoundary",by decide⟩],by decide⟩⟩,115⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-grouped-match-boundary.sol"⟩,0,128⟩
private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [], pattern => pattern
  | outer::rest, pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapMeaning {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (groups : List Syntax.SourceSpan) (meaning : WordMatchPatternClassifies pattern tag) :
    WordMatchPatternClassifies (wrap groups pattern) tag := by
  induction groups with
  | nil => exact meaning
  | cons outer rest ih => exact .group ih
private theorem wrapChecks (groups : List Syntax.SourceSpan) (pattern : Syntax.Pattern) :
    interpretWordMatchPattern? (wrap groups pattern) = interpretWordMatchPattern? pattern := by
  induction groups with
  | nil => rfl
  | cons outer rest ih => simpa only [wrap,interpretWordMatchPattern?] using ih
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "y"))⟩]⟩
private def wild (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.wildcard marker⟩,returned⟩⟩
private def literal (groups : List Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.literal ⟨span,.decimal "0"⟩⟩,returned⟩⟩
private def source (cases : List Syntax.MatchCase) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨ref "x",[]⟩⟩ ⟨span,⟨cases,none⟩⟩⟩]⟩
private def inputs (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x",id 0,.word⟩,⟨"y",id 1,type⟩],by change [id 0,id 1].Nodup; decide⟩
private def environment (scrutinee result : Core.Value) : Resolved.Environment :=
  [(id 0,scrutinee),(id 1,result)]
private def core : Core.Expr := .letE (.var 0) (.var 2)
private theorem xElaborates (type : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs type).names (inputs type).context (ref "x") (.var 0) .word :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem yElaborates (type : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs type).names (inputs type).context (ref "y") (.var 1) type :=
  .pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private theorem literalMeaning (groups : List Syntax.SourceSpan) :
    WordMatchPatternClassifies (literal groups).value.pattern (some .zero) :=
  wrapMeaning groups (.literal ⟨⟨span,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩)
private theorem originalElaborates (type : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs type)
      (source [wild groups marker,literal groups]) core type := by
  refine ComputationReturnTreeElaborates.wordMatch
    (defaultEntry := none) (entries := [(wild groups marker,none,.var 1),(literal groups,some .zero,.var 1)])
    (xElaborates type) rfl ?_ (.inl rfl) ?_ rfl (by simp) ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact wrapMeaning groups (.wildcard rfl)
    · exact literalMeaning groups
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .expression (yElaborates type)
  · simp [Core.Expr.weakenAt]
private theorem counted (type : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan)
    (rest : List Syntax.MatchCase) (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source (wild groups marker::rest)) result store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := (inputs type).names) (environment := environment scrutinee result)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := ref "x") (cases := wild groups marker::rest) (defaultBody := none)
    (selected := returned) (scrutineeValue := scrutinee)
    (.pure (.identifier .head .head)) (.wildcard (wrapMeaning groups (.wildcard rfl)))
    (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
      (Resolved.LocalScope.lookup?_iff.mp rfl))))
private theorem literalPath (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))

theorem arbitrary_original_groups_preserve_exact_classification
    (groups : List Syntax.SourceSpan) (pattern : Syntax.Pattern) (tag : Option Core.Word) :
    interpretWordMatchPattern? (wrap groups pattern) = interpretWordMatchPattern? pattern ∧
    (WordMatchPatternClassifies (wrap groups pattern) tag ↔ WordMatchPatternClassifies pattern tag) := by
  refine ⟨wrapChecks groups pattern,?_⟩
  rw [← interpretWordMatchPattern?_iff,wrapChecks,interpretWordMatchPattern?_iff]

theorem grouped_wildcard_recovers_the_literal_only_suffix_at_any_result_type
    (type : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs type)
      (source [wild groups marker,literal groups]) core type ∧
    RecursiveComputationReturnTreeHasType [] owner (inputs type)
      (source [wild groups marker,literal groups]) type ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs type)
      (source [wild groups marker,literal groups]) = some (core,type) ∧
    Core.HasType ((inputs type).context.map Prod.snd) core type := by
  have elaboration := originalElaborates type groups marker
  exact ⟨elaboration,
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr elaboration,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType elaboration⟩

theorem groups_add_no_steps_for_arbitrary_actual_values_stores_and_pending_frames
    (type : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan)
    (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source [wild groups marker,literal groups]) result store 4 ∧
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ ∧
    Core.Steps 4 ⟨.eval core (environment scrutinee result).values,pending,store⟩ ⟨.ret result,pending,store⟩ := by
  refine ⟨counted type groups marker _ scrutinee result store,literalPath scrutinee result store pending,?_⟩
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths
    toStepsWithContinuation (counted type groups marker _ scrutinee result store)
    (originalElaborates type groups marker) rfl pending

theorem every_fuel_and_genuine_checkpoint_keeps_the_literal_four_step_path
    (scrutinee result : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (.initial core [scrutinee,result] store)=.done result store ↔ 4≤fuel) ∧
    (∀ spent saved, Core.runStateful spent (.initial core [scrutinee,result] store)=.outOfFuel saved →
      spent<4 ∧ Core.Steps (4-spent) saved (.final result store) ∧
      ∀ additional, Core.runStateful additional saved =
        Core.runStateful (spent+additional) (.initial core [scrutinee,result] store)) := by
  have path := literalPath scrutinee result store []
  refine ⟨path.runStateful_done_iff,?_⟩
  intro spent saved stopped
  have residual := path.residual_of_outOfFuel stopped
  exact ⟨residual.1,residual.2,Core.runStateful_resume stopped⟩

theorem a_grouped_literal_hit_does_not_supply_missing_static_coverage
    (groups : List Syntax.SourceSpan) (type : Core.Ty) (result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment (.word .zero) result)
      store (source [literal groups]) result store 11 ∧
    ∀ resultType, ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type)
      (source [literal groups]) resultType := by
  constructor
  · exact ComputationReturnTreeEvaluatesWithCost.wordMatch
      (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
      (owner := owner) (table := (inputs type).names) (environment := environment (.word .zero) result)
      (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (scrutinee := ref "x") (cases := [literal groups]) (defaultBody := none)
      (selected := returned) (scrutineeValue := .word .zero)
      (.pure (.identifier .head .head)) (.hit (literalMeaning groups))
      (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
        (Resolved.LocalScope.lookup?_iff.mp rfl))))
  · intro resultType typing
    cases typing with
    | wordMatch _ _ _ covered _ _ =>
        rcases covered with present | ⟨arm,member,meaning⟩
        · cases present
        · cases List.mem_singleton.mp member
          cases (literalMeaning groups).tag_unique meaning

theorem grouped_literals_still_require_actual_Words_before_later_catch_all
    (groups : List Syntax.SourceSpan) (flag : Bool) (rest : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) (selected : Syntax.Block) (tests : Nat) :
    ¬ WordMatchChooses (.bool flag) (literal groups::rest) defaultBody selected tests := by
  intro choice
  cases choice with
  | wildcard meaning => cases (literalMeaning groups).tag_unique meaning

theorem grouping_does_not_accept_binders_tuples_comptime_constructors_or_errors
    (groups : List Syntax.SourceSpan) (name : Syntax.Identifier)
    (elements : Syntax.DelimitedList Syntax.Pattern) (expression : Syntax.Expr) :
    interpretWordMatchPattern? (wrap groups ⟨span,.binder name⟩) = none ∧
    interpretWordMatchPattern? (wrap groups ⟨span,.tuple elements⟩) = none ∧
    interpretWordMatchPattern? (wrap groups ⟨span,.comptime span expression⟩) = none ∧
    interpretWordMatchPattern? (wrap groups ⟨span,.constructor none [] name none⟩) = none ∧
    interpretWordMatchPattern? (wrap groups ⟨span,.error⟩) = none := by
  simp only [wrapChecks,interpretWordMatchPattern?,and_self]

theorem an_unreachable_grouped_error_still_blocks_static_acceptance
    (type : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan)
    (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source [wild groups marker,⟨span,⟨wrap groups ⟨span,.error⟩,returned⟩⟩]) result store 4 ∧
    ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type)
      (source [wild groups marker,⟨span,⟨wrap groups ⟨span,.error⟩,returned⟩⟩]) type := by
  refine ⟨counted type groups marker _ scrutinee result store,?_⟩
  intro typing
  cases typing with
  | wordMatch _ patterns _ _ _ _ =>
      obtain ⟨tag,meaning⟩ := patterns ⟨span,⟨wrap groups ⟨span,.error⟩,returned⟩⟩ (by simp)
      have checked := interpretWordMatchPattern?_iff.mpr meaning
      simp only [wrapChecks,interpretWordMatchPattern?] at checked
      cases checked

end Tests.FrontendGroupedMatchBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendGroupedMatchCountProperties
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
    (fun entry member => ((rowFacts n shape).2 entry member).1) (.inl rfl)
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
end

section
-- leanmerge: from Solcore.Test.FrontendOptionalMatchBoundaryProperties
/-! Symbolic original syntax, not a parser-validity claim. An absent default
stays absent, and the branch result type need not be the scrutinee's Word type. -/
set_option autoImplicit false
namespace Tests.FrontendOptionalMatchBoundary
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment
open RecursiveLocalComputationEvaluatesWithCost

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OptionalMatchBoundary",by decide⟩],by decide⟩⟩,112⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-optional-match-boundary.sol"⟩,0,128⟩
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "y"))⟩]⟩
private def wildcard (marker : Syntax.SourceSpan) : Syntax.MatchCase := ⟨span,⟨⟨span,.wildcard marker⟩,returned⟩⟩
private def literal : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,returned⟩⟩
private def source (cases : List Syntax.MatchCase) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨ref "x",[]⟩⟩ ⟨span,⟨cases,none⟩⟩⟩]⟩
private def inputs (type : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x",id 0,.word⟩,⟨"y",id 1,type⟩],by change [id 0,id 1].Nodup; decide⟩
private def environment (scrutinee result : Core.Value) : Resolved.Environment :=
  [(id 0,scrutinee),(id 1,result)]
private def core : Core.Expr := .letE (.var 0) (.var 2)
private theorem xElaborates (type : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs type).names (inputs type).context (ref "x") (.var 0) .word :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem yElaborates (type : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs type).names (inputs type).context (ref "y") (.var 1) type :=
  .pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private theorem literalMeaning : WordMatchPatternDenotes literal.value.pattern .zero :=
  ⟨⟨span,.decimal "0"⟩,rfl,.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩
private theorem originalElaborates (type : Core.Ty) (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs type)
      (source [wildcard marker,literal]) core type := by
  refine ComputationReturnTreeElaborates.wordMatch
    (defaultEntry := none) (entries := [(wildcard marker,none,.var 1),(literal,some .zero,.var 1)])
    (xElaborates type) rfl ?_ (.inl rfl) ?_ rfl (by simp) ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact .wildcard rfl
    · exact .literal literalMeaning
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .expression (yElaborates type)
  · simp [Core.Expr.weakenAt]
private theorem counted (type : Core.Ty) (marker : Syntax.SourceSpan) (rest : List Syntax.MatchCase)
    (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source (wildcard marker::rest)) result store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := (inputs type).names) (environment := environment scrutinee result)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := ref "x") (cases := wildcard marker::rest) (defaultBody := none)
    (selected := returned) (scrutineeValue := scrutinee)
    (.pure (.identifier .head .head)) (.wildcard (.wildcard rfl))
    (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
      (Resolved.LocalScope.lookup?_iff.mp rfl))))
private theorem literalPath (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))
private theorem noLiteralCoverage (type resultType : Core.Ty) :
    ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type) (source [literal]) resultType := by
  intro typed
  cases typed with
  | wordMatch _ _ _ covered _ _ =>
      rcases covered with present | ⟨arm,member,meaning⟩
      · cases present
      · simp only [List.mem_singleton] at member
        subst arm
        cases (WordMatchPatternClassifies.literal literalMeaning).tag_unique meaning

theorem the_original_first_body_determines_an_arbitrary_result_type
    (type : Core.Ty) (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs type)
      (source [wildcard marker,literal]) core type ∧
    RecursiveComputationReturnTreeHasType [] owner (inputs type)
      (source [wildcard marker,literal]) type ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs type)
      (source [wildcard marker,literal]) = some (core,type) ∧
    Core.HasType ((inputs type).context.map Prod.snd) core type := by
  have elaboration := originalElaborates type marker
  exact ⟨elaboration,
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr elaboration,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType elaboration⟩

theorem absent_default_and_an_unreachable_literal_keep_actual_values_and_pending_frames
    (type : Core.Ty) (marker : Syntax.SourceSpan) (scrutinee result : Core.Value)
    (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source [wildcard marker,literal]) result store 4 ∧
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ ∧
    Core.Steps 4 ⟨.eval core (environment scrutinee result).values,pending,store⟩ ⟨.ret result,pending,store⟩ := by
  refine ⟨counted type marker _ scrutinee result store,literalPath scrutinee result store pending,?_⟩
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths
    toStepsWithContinuation (counted type marker _ scrutinee result store) (originalElaborates type marker) rfl pending

theorem every_real_checkpoint_retains_its_remaining_path_and_full_resumption
    (scrutinee result : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (.initial core [scrutinee,result] store)=.done result store ↔ 4≤fuel) ∧
    (∀ spent saved, Core.runStateful spent (.initial core [scrutinee,result] store)=.outOfFuel saved →
      spent<4 ∧ Core.Steps (4-spent) saved (.final result store) ∧
      ∀ additional, Core.runStateful additional saved =
        Core.runStateful (spent+additional) (.initial core [scrutinee,result] store)) := by
  have path := literalPath scrutinee result store []
  refine ⟨path.runStateful_done_iff,?_⟩
  intro spent saved stopped
  have residual := path.residual_of_outOfFuel stopped
  exact ⟨residual.1,residual.2,Core.runStateful_resume stopped⟩

theorem an_empty_original_arm_collection_has_no_raw_choice
    (value : Core.Value) (selected : Syntax.Block) (tests : Nat) :
    ¬ WordMatchChooses value [] none selected tests := by
  intro choice
  cases choice

theorem an_empty_original_arm_collection_has_no_type_or_compiled_fallback (type : Core.Ty) :
    (∀ resultType, ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type) (source []) resultType) ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs type) (source []) = none := by
  have noType (resultType : Core.Ty) :
      ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type) (source []) resultType := by
    intro typed
    cases typed with
    | wordMatch _ _ _ covered _ _ =>
        rcases covered with present | ⟨arm,member,_⟩
        · cases present
        · cases member
  refine ⟨noType,?_⟩
  cases accepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs type) (source []) with
  | none => rfl
  | some result =>
      have elaboration := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mp accepted
      exact False.elim (noType result.2
        ((computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩))

theorem a_raw_literal_hit_without_default_does_not_establish_static_coverage
    (type : Core.Ty) (result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment (.word .zero) result)
      store (source [literal]) result store 11 ∧
    ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type) (source [literal]) type := by
  constructor
  · exact ComputationReturnTreeEvaluatesWithCost.wordMatch
      (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
      (owner := owner) (table := (inputs type).names) (environment := environment (.word .zero) result)
      (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (scrutinee := ref "x") (cases := [literal]) (defaultBody := none)
      (selected := returned) (scrutineeValue := .word .zero)
      (.pure (.identifier .head .head)) (.hit (.literal literalMeaning))
      (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
        (Resolved.LocalScope.lookup?_iff.mp rfl))))
  · exact noLiteralCoverage type type

theorem a_nonexhaustive_raw_hit_does_not_create_a_compiled_fallback (type : Core.Ty) :
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs type)
      (source [literal]) = none := by
  cases accepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner
      (inputs type) (source [literal]) with
  | none => rfl
  | some result =>
      have elaboration := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mp accepted
      have typed := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr
        ⟨result.1,elaboration⟩
      exact False.elim (noLiteralCoverage type result.2 typed)

theorem a_malformed_unreachable_pattern_still_prevents_static_acceptance
    (type : Core.Ty) (marker : Syntax.SourceSpan) (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs type).names (environment scrutinee result)
      store (source [wildcard marker,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) result store 4 ∧
    ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type)
      (source [wildcard marker,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) type := by
  refine ⟨counted type marker _ scrutinee result store,?_⟩
  intro typed
  cases typed with
  | wordMatch _ patterns _ _ _ _ =>
      obtain ⟨tag,meaning⟩ := patterns ⟨span,⟨⟨span,.error⟩,returned⟩⟩ (by simp)
      have checked := interpretWordMatchPattern?_iff.mpr meaning
      simp [interpretWordMatchPattern?] at checked

theorem a_pending_frame_is_outside_the_original_four_transition_body
    (scrutinee result : Core.Value) (store : Core.Store) :
    Core.runStateful 4 ⟨.eval core [scrutinee,result],[.pairApply (.bool true)],store⟩ =
      .outOfFuel ⟨.ret result,[.pairApply (.bool true)],store⟩ ∧
    Core.runStateful 5 ⟨.eval core [scrutinee,result],[.pairApply (.bool true)],store⟩ =
      .done (.pair (.bool true) result) store := ⟨rfl,rfl⟩

end Tests.FrontendOptionalMatchBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendOptionalMatchCountProperties
/-! Symbolic original syntax, not a parser-output claim. The independently typed
suffix remains in the source after selection. No default block is invented.
Actual closure paths may change stores; no runtime typing is assumed. -/
set_option autoImplicit false
namespace Tests.FrontendOptionalMatchCount
open Solcore Solcore.Frontend
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OptionalCount",by decide⟩],by decide⟩⟩,113⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-optional-count.sol"⟩,0,128⟩
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
  ⟨span,[⟨span,.matchWith ⟨span,⟨call false,[]⟩⟩ ⟨span,⟨cases n marker suffix.original,none⟩⟩⟩]⟩
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
      (none : Option Core.Expr) = some (tree n) := by
    induction n with
    | zero => simp [tree,rows,selectedCore,Core.Expr.weakenAt]
    | succ n ih => simpa [tree,rows,guard,Core.Expr.weakenAt] using congrArg (Option.map (Core.Expr.ifE guard (.var 3))) ih
  exact .wordMatch (defaultEntry := none)
    (.application (calleeElab false) argumentElab) (rowFacts n marker suffix).1
    (fun entry member => by
      have meaning := ((rowFacts n marker suffix).2 entry member).1; cases tag : entry.2.1 <;> simp only [tag] at meaning
      · exact .wildcard meaning.choose_spec
      · exact .literal meaning) (.inl rfl)
    (fun entry member => ((rowFacts n marker suffix).2 entry member).2)
    rfl (by intro entry member; cases member) folded
private theorem chosen (n : Nat) (marker : Syntax.SourceSpan) (extra : List Syntax.MatchCase) :
    WordMatchChooses (.word one) (cases n marker extra) none branch n := by
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
    ComputationReturnTreeEvaluatesWithCost.wordMatch (rawCall a false) (chosen n marker suffix.original) (.expression (rawCall a true))
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
    WordMatchChooses (.word one) (cases n marker suffix.original) none branch n :=
  ⟨elaborated n marker suffix,chosen n marker suffix.original⟩
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
theorem arbitrarily_repeated_suffix_rows_are_checked_without_extra_comparisons
    (a : Actual) (n : Nat) (marker : Syntax.SourceSpan) (extra : List (Bool × Syntax.SourceSpan)) :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source n marker (repeatedSuffix extra)) (core n) .word ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (env a) a.initial
      (source n marker (repeatedSuffix extra)) a.result a.final (a.scrutineeCost+a.branchCost+12+7*n) ∧
    ∀ k, Core.Steps (a.scrutineeCost+a.branchCost+12+7*n) ⟨.eval (core n) (env a).values,k,a.initial⟩ ⟨.ret a.result,k,a.final⟩ :=
  ⟨elaborated n marker (repeatedSuffix extra),actual_effects_and_independent_literal_paths a n marker (repeatedSuffix extra)⟩
theorem literal_only_suffix_is_unlowerable_but_original_wildcard_recovers (count : Nat) (marker : Syntax.SourceSpan) :
    ((repeatedSuffix (List.replicate count (false,marker))).rows.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map (fun t => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) t))
      (none : Option Core.Expr)) = none ∧
    RecursiveComputationReturnTreeElaborates [] owner inputs
      (source 0 marker (repeatedSuffix (List.replicate count (false,marker)))) (core 0) .word := by
  refine ⟨?_,elaborated 0 marker _⟩
  induction count with
  | zero => rfl
  | succ count ih => simpa [List.replicate_succ,repeatedSuffix] using ih
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

end Tests.FrontendOptionalMatchCount
end

section
-- leanmerge: from Solcore.Test.FrontendParsedGroupedMatchEffects
/-! Original grouped patterns retain their nested spans and singleton trailing commas.
Independent raw choices and literal paths charge comparisons, not grouping depth. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedGroupedMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def tailCore (mode : Nat) : Core.Expr := if mode=1 then call 2 1 else
  .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 2 1)
    (if mode=0 then call 2 1 else if mode=2 then call 3 1 else
      .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 3 1)
        (.ifE (.binary .wordEq (.var 0) (.word (word 1))) (call 3 1) (call 2 1)))
private def core (mode : Nat) : Core.Expr := .letE (call 3 0) (tailCore mode)
private def sourceBody (mode : Nat) := match mode with
  | 0 => "match(f(x)){case (0){return r(x);}default{return r(x);}}"
  | 1 => "match(f(x)){case (((_,),)){return r(x);}case (((0,),)){return w(x);}}"
  | 2 => "match(f(x)){case ((0,)){return r(x);}case ((_)){return w(x);}case (1){return r(x);}}"
  | _ => "match(f(x)){case ((0)){return r(x);}case ((0x00,)){return w(x);}case (((1,))){return w(x);}case ((_)){return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => do let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a => do let fn ← path n f env s; let arg ← path n a env fn.final; match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b => do let l ← path n a env s; let r ← path n b env l.final; match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b => do let g ← path n c env s; match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨by rw [shape]; exact .literal ⟨literal,rfl,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span && decide (p.span.startByte<inner.span.startByte ∧ inner.span.endByte<p.span.endByte)) "original nested group ranges"; let c ← pattern inner; return ⟨c.1,⟨by rw [shape]; exact .group c.2.down⟩⟩
  | _ => throw (IO.userError "unsupported grouped or bare leaf")
termination_by sizeOf p
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && cs.all (fun c => armsSpan.contains c.span) && d.toList.all (fun b => armsSpan.contains b.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match and optional default ranges"
      let sc ← child i e; let bs ← arms i cs
      let dc : Σ de : Option (Syntax.Block × Core.Expr), PLift (de.map Prod.fst=d ∧ ∀ en ∈ de.toList, RecursiveComputationReturnTreeElaborates types owner i en.1 en.2 .word) ← match present : d with | none => pure ⟨none,⟨by simp [present]⟩⟩ | some b => do let c ← returned i b; pure ⟨some (b,c.core),⟨by refine ⟨present.symm,?_⟩; intro en h; cases List.mem_singleton.mp h; exact c.evidence⟩⟩
      match lowered : bs.1.foldr (fun en t => match en.2.1 with | none => some (en.2.2.weakenAt 0) | some v => t.map (fun t => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t)) (dc.1.map (fun en => en.2.weakenAt 0)) with
      | some t => if same : sc.1=.word then return ⟨.letE sc.2.core t,by rw [shape]; exact .wordMatch (defaultEntry := dc.1) (same ▸ sc.2.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) dc.2.down.1 dc.2.down.2 lowered⟩ else throw (IO.userError "scrutinee type")
      | none => throw (IO.userError "uncovered original arms")
  | _ => throw (IO.userError "original terminal grouped match")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs d selected.1 selected.2)) := do
  match shape : cs with
  | [] => match present : d with | some fallback => return ⟨(fallback,0),⟨by rw [shape,present]; exact .fallback⟩⟩ | none => throw (IO.userError "no raw fallback")
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (location : Nat := 2) : List TypedRuntimeArgument := [allocator,writer location,reader 1,⟨.word,w 14,.word⟩]
private def positive (mode : Nat) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody mode)
  check (match source.value.body.value with | [⟨_,.matchWith _ cs⟩] => cs.value.cases.all (fun c => match c.value.pattern.value with | .group _ => true | _ => false) | _ => false) "original outer group nodes remain present"
  let args ← (arguments location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core mode); let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core mode) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace original raw selection"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core mode) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core mode) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core mode) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 (call 3 0) env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore mode) env],scr.final⟩
  check (decide (scr.cost=13 ∧ Core.runStateful 14 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-14) cp=.done value final)) "one allocation and actual hidden-let saved environment"
  if mode=2 then
    let cp : Core.State := ⟨.ret (.bool (scr.value==w 0)),[.ifBranches (call 2 1) (call 3 1) (scr.value::env)],scr.final⟩
    check (decide (Core.runStateful 21 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-21) cp=.done value final)) "genuine ifBranches with actual saved scrutinee"
  check (decide (Core.runStateful cost ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedGroupedMatchEffects
open ParsedGroupedMatchEffects
def frontendParsedGroupedMatchEffectTests : IO Unit := do
  positive 0 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [.bool false,w 41,w 99] [.bool false,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23 700
  positive 2 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 37
  positive 2 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 3 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 3 [w 1,w 41,w 99] [w 1,w 41,w 14,w 14] (w 14) 51
  positive 3 [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 44
  let source ← parsed (sourceBody 2); let args := arguments; let p ← prepare source args (core 2); let env := p.1.inputs.environment.values
  let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  let frames := [.binaryApply .wordEq (.bool false),.ifBranches (call 2 1) (call 3 1) (.bool false::env)]
  let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),frames,t⟩
  let before : Core.State := ⟨.eval (.word (word 0)) (.bool false::env),frames,t⟩
  check (decide (Core.runStateful 19 (.initial (core 2) env s)=.outOfFuel before ∧ Core.runStateful 1 before=fault)) "literal before wildcard faults with allocation retained"
  for fuel in List.range 23 do
    let out := Core.runStateful fuel (.initial (core 2) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,out))) "same prepared prefix on corrupt actual store"
    if fuel<20 then match out with
      | .outOfFuel cp => check (decide (Core.runStateful 100 cp=fault)) "all genuine pre-fault resumes"
      | _ => throw (IO.userError "first literal fault threshold")
    else check (decide (out=fault)) "wildcard does not turn invalid literal operands into a miss"
  for text in ["match(f(x)){case ((_)){return r(x);}case ((0)){return Missing;}}","match(f(x)){case ((_)){return r(x);}default{return ();}}","match(f(x)){case ((_)){return r(x);}case ((y)){return w(x);}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=23 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "original raw wildcard skips tail but all static obligations remain"
  for text in ["match(f(x)){case ((0)){return r(x);}}","match(f(x)){case (() ){return r(x);}default{return r(x);}}","match(f(x)){case ((0,0)){return r(x);}default{return r(x);}}","match(f(x)){case ((true)){return r(x);}default{return r(x);}}","match(f(x)){case ((0)){return r(x);}default{return r(x);}} return x;","match(f(x)){case (("++toString Core.wordModulus++")){return r(x);}default{return r(x);}}"] do
    let rejected ← parsed text
    check (decide (compileRecursiveComputationFunction? types owner rejected=none)) "group transparency preserves strict leaves, coverage, Word type and terminal gates"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedGroupedMatchScopes
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedGroupedMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"GroupedMatchScopes",by decide⟩],by decide⟩⟩,117⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 41))) (call 6 3) (.var 3)
private def inner : Core.Expr := .letE (call 4 2) innerTail
private def outerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) inner (call 4 2)
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case ((0,)){match(r(z)){case (41,){return w(z);}case ((_,)){return z;}}}case (_){return r(z);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"grouped-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternClassifies p (some v))) := do
  match shape : p with
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span) "original group range"; let r ← pattern inner; return ⟨r.1,⟨by rw [shape]; exact .group r.2.down⟩⟩
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨.literal ⟨literal,by rw [shape],interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "grouped literal pattern")
termination_by sizeOf p
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span) "original wildcard group range"; let r ← wildcard inner; return ⟨by rw [shape]; exact .group r.down⟩
  | ⟨span,.wildcard marker⟩ => check (decide (marker=span ∧ marker.endByte=marker.startByte+1)) "original one-byte marker"; return ⟨by rw [shape]; exact .wildcard rfl⟩
  | _ => throw (IO.userError "grouped wildcard")
termination_by sizeOf p
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm,wildArm],none⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && armsSpan.contains wildArm.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte ∧ arm.span.endByte≤wildArm.span.startByte)) "nested original scrutinee/cases with no default"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let p ← pattern arm.value.pattern; let a ← body i arm.value.body; let b ← body i wildArm.value.body
      let wild ← wildcard wildArm.value.pattern
      check (wildArm.span.contains wildArm.value.pattern.span && wildArm.span.contains wildArm.value.body.span) "original grouped wildcard and branch ranges"
      if same : sc.1=.word then return ⟨.letE sc.2.core (.ifE (.binary .wordEq (.var 0) (.word p.1)) (a.core.weakenAt 0) (b.core.weakenAt 0)),by
        rw [shape]; exact .wordMatch (defaultEntry := none) (entries := [(arm,some p.1,a.core),(wildArm,none,b.core)]) (same ▸ sc.2.evidence) rfl
          (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact p.2.down; exact wild.down) (.inl rfl)
          (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact a.evidence; exact b.evidence) rfl (by intro entry h; cases h) rfl⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm,wildArm],none⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let p ← pattern arm.value.pattern
      let wild ← wildcard wildArm.value.pattern
      match actual : sc.value with
      | .word v =>
          if same : v=p.1 then let r ← rawBody table env sc.final arm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := none) sc.evidence (by rw [actual]; exact .hit (same.symm ▸ p.2.down)) r.evidence⟩
          else let r ← rawBody table env sc.final wildArm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := none) sc.evidence (by rw [actual]; exact .miss p.2.down same (.wildcard wild.down)) r.evidence⟩
      | _ => throw (IO.userError "raw actual Word before wildcard")
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.word,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.word,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.word,.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[w 0,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (w 0),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 41),.letBody innerTail (w 0::w 41::w 14::env)::pending,allocated⟩),(51,⟨.ret (.bool true),.ifBranches (call 6 3) (.var 3) (w 41::w 0::w 41::w 14::env)::pending,allocated⟩),(67,⟨.ret (w 14),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (68-spent) cp=.done result final)) "saved named/discarded/two hidden slots and literal original environments"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedGroupedMatchScopes
open ParsedGroupedMatchScopes
def frontendParsedGroupedMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 67
  verify source [w 0,w 42,w 99] [w 0,w 42,w 99,w 14] (w 14) 53
  verify source [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 43
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOptionalMatchEffects
/-! Original absent defaults are not replaced by fabricated syntax or Core.
Independent effects and literal paths test wildcard recovery of a missing tail. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedOptionalMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def tailCore (mode : Nat) : Core.Expr := if mode<2 then call 2 1 else
  .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 2 1)
    (if mode=2 then call 3 1 else .ifE (.binary .wordEq (.var 0) (.word (word 1))) (call 2 1) (call 3 1))
private def core (mode : Nat) : Core.Expr := .letE (call 3 0) (tailCore mode)
private def sourceBody (mode : Nat) := match mode with
  | 0 => "match(f(x)){case _{return r(x);}}"
  | 1 => "match(f(x)){case _{return r(x);}case 0{return w(x);}}"
  | 2 => "match(f(x)){case 0{return r(x);}case _{return w(x);}case 0{return r(x);}}"
  | _ => "match(f(x)){case 0{return r(x);}case 1{return r(x);}case _{return w(x);}case _{return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p.value with
  | .wildcard marker => return ⟨none,⟨.wildcard (marker := marker) shape⟩⟩
  | .literal literal => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨.literal ⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal or exact wildcard pattern")
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,none⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && cs.all (fun c => armsSpan.contains c.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match ranges and genuinely absent default"
      let sc ← child i e; let bs ← arms i cs
      match lowered : bs.1.foldr (fun en t => match en.2.1 with | none => some (en.2.2.weakenAt 0) | some v => t.map (fun t => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t)) none with
      | some t => if same : sc.1=.word then return ⟨.letE sc.2.core t,by rw [shape]; exact .wordMatch (defaultEntry := none) (same ▸ sc.2.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) rfl (by simp) lowered⟩ else throw (IO.userError "scrutinee type")
      | none => throw (IO.userError "uncovered original arms")
  | _ => throw (IO.userError "original terminal match without default")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs d selected.1 selected.2)) := do
  match shape : cs with
  | [] => match present : d with | some fallback => return ⟨(fallback,0),⟨by rw [shape,present]; exact .fallback⟩⟩ | none => throw (IO.userError "no raw fallback")
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (location : Nat := 2) : List TypedRuntimeArgument := [allocator,writer location,reader 1,⟨.word,w 14,.word⟩]
private def positive (mode : Nat) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody mode)
  let args ← (arguments location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core mode)
  let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core mode) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace original raw selection"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core mode) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core mode) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core mode) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 (call 3 0) env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore mode) env],scr.final⟩
  check (decide (scr.cost=13 ∧ Core.runStateful 14 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-14) cp=.done value final)) "one allocation and actual hidden-let saved environment"
  if mode=2 then
    let cp : Core.State := ⟨.ret (.bool (scr.value==w 0)),[.ifBranches (call 2 1) (call 3 1) (scr.value::env)],scr.final⟩
    check (decide (Core.runStateful 21 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-21) cp=.done value final)) "genuine ifBranches with actual saved scrutinee"
  check (decide (Core.runStateful cost ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedOptionalMatchEffects
open ParsedOptionalMatchEffects
def frontendParsedOptionalMatchEffectTests : IO Unit := do
  for mode in [0,1] do positive mode [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [.bool false,w 41,w 99] [.bool false,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23 700
  positive 2 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 37
  positive 2 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 3 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 44
  let source ← parsed (sourceBody 2); let args := arguments; let p ← prepare source args (core 2); let env := p.1.inputs.environment.values
  let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  let frames := [.binaryApply .wordEq (.bool false),.ifBranches (call 2 1) (call 3 1) (.bool false::env)]
  let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),frames,t⟩
  let before : Core.State := ⟨.eval (.word (word 0)) (.bool false::env),frames,t⟩
  check (decide (Core.runStateful 19 (.initial (core 2) env s)=.outOfFuel before ∧ Core.runStateful 1 before=fault)) "literal before wildcard faults with allocation retained"
  for fuel in List.range 23 do
    let out := Core.runStateful fuel (.initial (core 2) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,out))) "same prepared prefix on corrupt actual store"
    if fuel<20 then match out with
      | .outOfFuel cp => check (decide (Core.runStateful 100 cp=fault)) "all genuine pre-fault resumes"
      | _ => throw (IO.userError "first literal fault threshold")
    else check (decide (out=fault)) "wildcard does not turn invalid literal operands into a miss"
  for text in ["match(f(x)){case _{return r(x);}case 0{return Missing;}}","match(f(x)){case _{return r(x);}case 0{return ();}}","match(f(x)){case _{return r(x);}case y{return w(x);}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=23 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "original raw wildcard skips tail but all static obligations remain"
  for text in ["match(f(x)){case 0{return r(x);}}"] do
    let rejected ← parsed text
    check (decide (compileRecursiveComputationFunction? types owner rejected=none)) "Word scrutinee and actual wildcard coverage are independent gates"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedOptionalMatchScopes
/-! Original named/discarded slots and nested matches with absent defaults retain
their scopes. Separate literal Core paths expose both hidden scrutinee environments. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedOptionalMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"OptionalMatchScopes",by decide⟩],by decide⟩⟩,114⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 41))) (call 6 3) (.var 3)
private def inner : Core.Expr := .letE (call 4 2) innerTail
private def outerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) inner (call 4 2)
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case 0{match(r(z)){case 41{return w(z);}case _{return z;}}}case _{return r(z);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"optional-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternDenotes p v)) := do
  match shape : p.value with
  | .literal literal => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal pattern")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm,wildArm],none⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && armsSpan.contains wildArm.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte ∧ arm.span.endByte≤wildArm.span.startByte)) "nested original scrutinee/cases with no default"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let p ← pattern arm.value.pattern; let a ← body i arm.value.body; let b ← body i wildArm.value.body
      match wild : wildArm.value.pattern.value with
      | .wildcard marker =>
          check (wildArm.span.contains wildArm.value.pattern.span && wildArm.span.contains wildArm.value.body.span && decide (marker=wildArm.value.pattern.span ∧ marker.endByte=marker.startByte+1)) "original one-byte wildcard marker and branch ranges"
          if same : sc.1=.word then return ⟨.letE sc.2.core (.ifE (.binary .wordEq (.var 0) (.word p.1)) (a.core.weakenAt 0) (b.core.weakenAt 0)),by
            rw [shape]; exact .wordMatch (defaultEntry := none) (entries := [(arm,some p.1,a.core),(wildArm,none,b.core)]) (same ▸ sc.2.evidence) rfl
              (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact .literal p.2.down; exact .wildcard wild) (.inl rfl)
              (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact a.evidence; exact b.evidence) rfl (by intro entry h; cases h) rfl⟩
          else throw (IO.userError "scrutinee type")
      | _ => throw (IO.userError "original wildcard")
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm,wildArm],none⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let p ← pattern arm.value.pattern
      match wild : wildArm.value.pattern.value with
      | .wildcard marker => match actual : sc.value with
        | .word v =>
            if same : v=p.1 then let r ← rawBody table env sc.final arm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := none) sc.evidence (by rw [actual]; exact .hit (.literal (same.symm ▸ p.2.down))) r.evidence⟩
            else let r ← rawBody table env sc.final wildArm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := none) sc.evidence (by rw [actual]; exact .miss (.literal p.2.down) same (.wildcard (.wildcard wild))) r.evidence⟩
        | _ => throw (IO.userError "raw actual Word before wildcard")
      | _ => throw (IO.userError "raw wildcard")
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.word,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.word,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.word,.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[w 0,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (w 0),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 41),.letBody innerTail (w 0::w 41::w 14::env)::pending,allocated⟩),(51,⟨.ret (.bool true),.ifBranches (call 6 3) (.var 3) (w 41::w 0::w 41::w 14::env)::pending,allocated⟩),(67,⟨.ret (w 14),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (68-spent) cp=.done result final)) "saved named/discarded/two hidden slots and literal original environments"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedOptionalMatchScopes
open ParsedOptionalMatchScopes
def frontendParsedOptionalMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 67
  verify source [w 0,w 42,w 99] [w 0,w 42,w 99,w 14] (w 14) 53
  verify source [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 43
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypeGeneralMatchEffects
/-! Original Bool scrutinees keep their effects even for catch-all-only matching.
Independent preparation, source costs and literal Core paths retain exact old fixtures. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedTypeGeneralMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def scrutineeCore : Core.Expr := .binary .wordEq (call 3 0) (.word (word 0))
private def tailCore (mode : Nat) : Core.Expr := if mode=5 then call 3 1 else call 2 1
private def core (mode : Nat) : Core.Expr := .letE scrutineeCore (tailCore mode)
private def sourceBody (mode : Nat) := match mode with
  | 0 => "match(f(x)==0){case _{return r(x);}default{return r(x);}}"
  | 1 => "match(f(x)==0){case _{return r(x);}}"
  | 2 => "match(f(x)==0){case ((_)){return r(x);}}"
  | 3 => "match(f(x)==0){default{return r(x);}}"
  | 4 => "match(f(x)==0){case ((_)){return r(x);}case _{return w(x);}default{return w(x);}}"
  | _ => "match(f(x)==0){case ((_)){return w(x);}default{return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b => do let l ← path n a env s; let r ← path n b (l.value::env) l.final; return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a => do let fn ← path n f env s; let arg ← path n a env fn.final; match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b => do let l ← path n a env s; let r ← path n b env l.final; match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨.word,.word v,by rw [shape]; exact .pure (.wordLiteral (interpretWordLiteral?_sound decoded)) .word .word⟩ | none => throw (IO.userError "strict original literal")
  | ⟨_,.binary l ⟨opSpan,.equal⟩ r⟩ =>
      check (e.span.contains l.span && e.span.contains r.span && e.span.contains opSpan && decide (l.span.endByte≤opSpan.startByte ∧ opSpan.startByte<opSpan.endByte ∧ opSpan.endByte≤r.span.startByte)) "original equality children and operator order"
      let a ← child i l; let b ← child i r
      if same : a.1=.word ∧ b.1=.word then return ⟨.bool,.binary .wordEq a.2.core b.2.core,by rw [shape]; exact .binary .equal (by simpa only [Core.BinaryOp.leftType,same.1] using a.2.evidence) (by simpa only [Core.BinaryOp.rightType,Core.BinaryOp.leftType,same.2] using b.2.evidence)⟩ else throw (IO.userError "equality Word operands")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p with
  | ⟨_,.wildcard _⟩ => return ⟨none,⟨by rw [shape]; exact .wildcard rfl⟩⟩
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨by rw [shape]; exact .literal ⟨literal,rfl,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span && decide (p.span.startByte<inner.span.startByte ∧ inner.span.endByte<p.span.endByte)) "original nested group ranges"; let c ← pattern inner; return ⟨c.1,⟨by rw [shape]; exact .group c.2.down⟩⟩
  | _ => throw (IO.userError "unsupported grouped or bare leaf")
termination_by sizeOf p
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && cs.all (fun c => armsSpan.contains c.span) && d.toList.all (fun b => armsSpan.contains b.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match and optional default ranges"
      let sc ← child i e; let bs ← arms i cs
      let dc : Σ de : Option (Syntax.Block × Core.Expr), PLift (de.map Prod.fst=d ∧ ∀ en ∈ de.toList, RecursiveComputationReturnTreeElaborates types owner i en.1 en.2 .word) ← match present : d with | none => pure ⟨none,⟨by simp [present]⟩⟩ | some b => do let c ← returned i b; pure ⟨some (b,c.core),⟨by refine ⟨present.symm,?_⟩; intro en h; cases List.mem_singleton.mp h; exact c.evidence⟩⟩
      match lowered : bs.1.foldr (fun en t => match en.2.1 with | none => some (en.2.2.weakenAt 0) | some v => t.map (fun t => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t)) (dc.1.map (fun en => en.2.weakenAt 0)) with
      | some t => if caught : bs.1.all (fun en => en.2.1.isNone)=true then return ⟨.letE sc.2.core t,by rw [shape]; exact .wordMatch sc.2.evidence bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inr (by intro en h; simpa using List.all_eq_true.mp caught en h)) (fun e h => (bs.2.down.2 e h).2) dc.2.down.1 dc.2.down.2 lowered⟩ else throw (IO.userError "fixture requires every original case to be catch-all")
      | none => throw (IO.userError "uncovered original arms")
  | _ => throw (IO.userError "original terminal catch-all match")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.literal literal⟩ => match decoded : interpretWordLiteral? literal with | some v => return ⟨.word v,s,1,by rw [shape]; exact .pure (.wordLiteral (interpretWordLiteral?_sound decoded))⟩ | none => throw (IO.userError "raw strict literal")
  | ⟨_,.binary a ⟨_,.equal⟩ b⟩ =>
      let l ← rawChild table env s a; let r ← rawChild table env l.final b
      match applied : Core.BinaryOp.wordEq.apply l.value r.value with | some v => return ⟨v,r.final,l.cost+r.cost+3,by rw [shape]; exact .binary .equal l.evidence r.evidence applied⟩ | none => throw (IO.userError "actual scrutinee comparison fault")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Option Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs d selected.1 selected.2)) := do
  match shape : cs with
  | [] => match present : d with | some fallback => return ⟨(fallback,0),⟨by rw [shape,present]; exact .fallback⟩⟩ | none => throw (IO.userError "no raw fallback")
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some _ => throw (IO.userError "reached literal outside catch-all fixture")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (location : Nat := 2) : List TypedRuntimeArgument := [allocator,writer location,reader 1,⟨.word,w 14,.word⟩]
private def positive (mode : Nat) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody mode)
  let args ← (arguments location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core mode); let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core mode) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace original raw selection"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core mode) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core mode) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core mode) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 scrutineeCore env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore mode) env],scr.final⟩
  check (decide (scr.cost=17 ∧ scr.value=.bool (s[0]? == some (w 0)) ∧ scr.final=s++[w 14] ∧ Core.runStateful 18 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-18) cp=.done value final)) "genuine Bool hidden-let checkpoint after original allocation/equality"
  let left ← path 40 (call 3 0) env s
  let pending : Core.State := ⟨.ret left.value,[.binaryRight .wordEq (.word (word 0)) env,.letBody (tailCore mode) env],left.final⟩
  check (decide (left.cost=13 ∧ some left.value=s[0]? ∧ left.final=s++[w 14] ∧ Core.runStateful 15 (.initial (core mode) env s)=.outOfFuel pending ∧ Core.runStateful (cost-15) pending=.done value final)) "scrutinee binaryRight saves original environment before default or wildcard selection"
  check (decide (Core.runStateful cost ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedTypeGeneralMatchEffects
open ParsedTypeGeneralMatchEffects
def frontendParsedTypeGeneralMatchEffectTests : IO Unit := do
  for mode in [0,1,2,3,4] do positive mode [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 27
  positive 2 [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 27
  positive 4 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 27 700
  positive 3 [w 0,.bool true,w 99] [w 0,.bool true,w 99,w 14] (.bool true) 27
  positive 5 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 34
  let args := arguments; let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  for mode in [0,1,2,3] do
    let source ← parsed (sourceBody mode); let p ← prepare source args (core mode); let env := p.1.inputs.environment.values
    let frames := [.binaryApply .wordEq (.bool false),.letBody (tailCore mode) env]
    let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),frames,t⟩
    let before : Core.State := ⟨.eval (.word (word 0)) env,frames,t⟩
    check (decide (Core.runStateful 16 (.initial (core mode) env s)=.outOfFuel before ∧ Core.runStateful 1 before=fault)) "catch-all does not skip original scrutinee fault or allocation"
    for fuel in List.range 20 do
      let out := Core.runStateful fuel (.initial (core mode) env s)
      check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,out))) "same prepared Bool source on corrupt actual store"
      if fuel<17 then match out with
        | .outOfFuel cp => check (decide (Core.runStateful 100 cp=fault)) "all genuine pre-scrutinee-fault resumes"
        | _ => throw (IO.userError "first scrutinee fault threshold")
      else check (decide (out=fault)) "original equality must complete before any catch-all"
  for text in ["match(f(x)==0){case _{return r(x);}case 0{return w(x);}}","match(f(x)==0){case ((_)){return r(x);}case ((y)){return w(x);}}","match(f(x)==0){case _{return r(x);}case _{return Missing;}}","match(f(x)==0){case _{return r(x);}default{return ();}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=27 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "raw first catch-all does not erase any original type, pattern or body obligation"
  for text in ["match(f(x)==0){case 0{return r(x);}default{return r(x);}}","match(f(x)){case 0{return r(x);}}","match(f(x)==0){case ((true)){return r(x);}default{return r(x);}}","match(f(x)==0){case (0,0){return r(x);}default{return r(x);}}",sourceBody 1++"return x;"] do
    let rejected ← parsed text
    check (decide (compileRecursiveComputationFunction? types owner rejected=none)) "unsupported literal/type, coverage, tuple, constructor and nonterminal cases remain excluded"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedTypeGeneralMatchScopes
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedTypeGeneralMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"TypeGeneralMatchScopes",by decide⟩],by decide⟩⟩,120⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := call 6 4
private def inner : Core.Expr := .letE (.var 6) innerTail
private def outerTail : Core.Expr := .letE (call 5 2) inner
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case ((_)){w(z);match(w){default{return r(z);}}}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"type-general-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .bool),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def wildcard (p : Syntax.Pattern) : IO (PLift (WordMatchPatternClassifies p none)) := do
  match shape : p with
  | ⟨_,.group inner⟩ => check (p.span.contains inner.span) "original wildcard group range"; let r ← wildcard inner; return ⟨by rw [shape]; exact .group r.down⟩
  | ⟨span,.wildcard marker⟩ => check (decide (marker=span ∧ marker.endByte=marker.startByte+1)) "original one-byte marker"; return ⟨by rw [shape]; exact .wildcard rfl⟩
  | _ => throw (IO.userError "grouped wildcard")
termination_by sizeOf p
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm],none⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte)) "original wildcard-only match without default"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let wild ← wildcard arm.value.pattern; let branch ← body i arm.value.body
      return ⟨.letE sc.2.core (branch.core.weakenAt 0),by
        rw [shape]; exact .wordMatch (defaultEntry := none) (entries := [(arm,none,branch.core)]) sc.2.evidence rfl
          (by intro entry h; cases List.mem_singleton.mp h; exact wild.down) (.inr (by simp))
          (by intro entry h; cases List.mem_singleton.mp h; exact branch.evidence) rfl (by simp) rfl⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[],some d⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains d.span && decide (e.span.endByte≤d.span.startByte)) "original default-only match over a function value"
      let sc ← child i e; let branch ← body i d
      return ⟨.letE sc.2.core (branch.core.weakenAt 0),by
        rw [shape]; exact .wordMatch (defaultEntry := some (d,branch.core)) (entries := []) sc.2.evidence rfl
          (by simp) (.inr (by simp)) (by simp) rfl
          (by intro entry h; cases List.mem_singleton.mp h; exact branch.evidence) rfl⟩
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm],none⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let wild ← wildcard arm.value.pattern
      let r ← rawBody table env sc.final arm.value.body
      return ⟨r.value,r.final,sc.cost+r.cost+2,by rw [shape]; exact .wordMatch (cases := [arm]) (defaultBody := none) sc.evidence (.wildcard wild.down) r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[],some d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let r ← rawBody table env sc.final d
      return ⟨r.value,r.final,sc.cost+r.cost+2,by rw [shape]; exact .wordMatch (cases := []) (defaultBody := some d) sc.evidence .fallback r.evidence⟩
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .bool,.closure .word .bool (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .bool 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.bool,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.bool,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.bool,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.bool,.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[.bool true,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (.bool true),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 14),.letBody inner (.bool true::w 41::w 14::env)::pending,final⟩),(47,⟨.ret (writer 2).value,.letBody innerTail (w 14::.bool true::w 41::w 14::env)::pending,final⟩),(56,⟨.ret (w 41),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (57-spent) cp=.done result final)) "saved named/discarded/Bool/function slots and original closure captures"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedTypeGeneralMatchScopes
open ParsedTypeGeneralMatchScopes
def frontendParsedTypeGeneralMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [.bool true,w 41,w 99] [.bool true,w 41,w 14,w 14] (w 41) 56
  verify source [.bool false,w 42,w 99] [.bool false,w 42,w 14,w 14] (w 42) 56
  verify source [.bool false,w 41,w 99] [.bool false,w 41,w 14,w 14] (w 41) 56
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWildcardMatchEffects
/-! Ordered wildcard selection preserves original source and actual effects.
Independent literal Core paths distinguish direct selection from prior guards. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWildcardMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def tailCore (mode : Nat) : Core.Expr := if mode<2 then call 2 1 else
  .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 2 1)
    (if mode=2 then call 3 1 else .ifE (.binary .wordEq (.var 0) (.word (word 1))) (call 2 1) (call 3 1))
private def core (mode : Nat) : Core.Expr := .letE (call 3 0) (tailCore mode)
private def sourceBody (mode : Nat) := match mode with
  | 0 => "match(f(x)){case _{return r(x);}default{return r(x);}}"
  | 1 => "match(f(x)){case _{return r(x);}case 0{return w(x);}case _{return w(x);}default{return r(x);}}"
  | 2 => "match(f(x)){case 0{return r(x);}case _{return w(x);}case 0{return r(x);}default{return r(x);}}"
  | _ => "match(f(x)){case 0{return r(x);}case 1{return r(x);}case _{return w(x);}case _{return r(x);}default{return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩ | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩ | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩ | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ tag : Option Core.Word, PLift (WordMatchPatternClassifies p tag)) := do
  match shape : p.value with
  | .wildcard marker => return ⟨none,⟨.wildcard (marker := marker) shape⟩⟩
  | .literal literal => match decoded : interpretWordLiteral? literal with | some v => return ⟨some v,⟨.literal ⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩ | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal or exact wildcard pattern")
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,some d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains d.span && cs.all (fun c => armsSpan.contains c.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match scrutinee/arms/default spans"
      let sc ← child i e; let bs ← arms i cs; let dc ← returned i d
      if same : sc.1=.word then return ⟨.letE sc.2.core (bs.1.foldr (fun en t => match en.2.1 with | none => en.2.2.weakenAt 0 | some v => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t) (dc.core.weakenAt 0)),by rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (same ▸ sc.2.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) rfl (by intro e h; cases List.mem_singleton.mp h; exact dc.evidence) (by simp only [Option.map_some]; induction bs.1 with | nil => rfl | cons e es ih => cases tag : e.2.1 <;> simp only [List.foldr_cons,tag,ih,Option.map_some])⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "original terminal match")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs (some d) selected.1 selected.2)) := do
  match shape : cs with
  | [] => return ⟨(d,0),⟨by rw [shape]; exact .fallback⟩⟩
  | c::rest =>
      let p ← pattern c.value.pattern
      match tag : p.1 with
      | none => return ⟨(c.value.body,0),⟨by rw [shape]; exact .wildcard (by simpa only [tag] using p.2.down)⟩⟩
      | some literal => match actual : v with
        | .word w =>
            have meaning : WordMatchPatternClassifies c.value.pattern (some literal) := by simpa only [tag] using p.2.down
            if same : w=literal then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (same.symm ▸ meaning)⟩⟩
            else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss meaning same tail.2.down⟩⟩
        | _ => throw (IO.userError "actual non-Word comparison before wildcard")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,some d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (location : Nat := 2) : List TypedRuntimeArgument := [allocator,writer location,reader 1,⟨.word,w 14,.word⟩]
private def positive (mode : Nat) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody mode)
  let args ← (arguments location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core mode)
  let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core mode) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace raw selected/default success"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core mode) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core mode) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core mode) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 (call 3 0) env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore mode) env],scr.final⟩
  check (decide (scr.cost=13 ∧ Core.runStateful 14 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-14) cp=.done value final)) "one allocation and actual hidden-let saved environment"
  if mode=2 then
    let cp : Core.State := ⟨.ret (.bool (scr.value==w 0)),[.ifBranches (call 2 1) (call 3 1) (scr.value::env)],scr.final⟩
    check (decide (Core.runStateful 21 (.initial (core mode) env s)=.outOfFuel cp ∧ Core.runStateful (cost-21) cp=.done value final)) "genuine ifBranches with actual saved scrutinee"
  check (decide (Core.runStateful cost ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core mode) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedWildcardMatchEffects
open ParsedWildcardMatchEffects
def frontendParsedWildcardMatchEffectTests : IO Unit := do
  positive 0 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23
  positive 1 [.bool false,w 41,w 99] [.bool false,w 41,w 99,w 14] (w 41) 23
  positive 1 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 23 700
  positive 2 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 37
  positive 2 [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive 3 [w 7,w 41,w 99] [w 7,w 41,w 14,w 14] (w 14) 44
  let source ← parsed (sourceBody 2); let args := arguments; let p ← prepare source args (core 2); let env := p.1.inputs.environment.values
  let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  let frames := [.binaryApply .wordEq (.bool false),.ifBranches (call 2 1) (call 3 1) (.bool false::env)]
  let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),frames,t⟩
  let before : Core.State := ⟨.eval (.word (word 0)) (.bool false::env),frames,t⟩
  check (decide (Core.runStateful 19 (.initial (core 2) env s)=.outOfFuel before ∧ Core.runStateful 1 before=fault)) "literal before wildcard faults with allocation retained"
  for fuel in List.range 23 do
    let out := Core.runStateful fuel (.initial (core 2) env s)
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,out))) "same prepared prefix on corrupt actual store"
    if fuel<20 then match out with
      | .outOfFuel cp => check (decide (Core.runStateful 100 cp=fault)) "all genuine pre-fault resumes"
      | _ => throw (IO.userError "first literal fault threshold")
    else check (decide (out=fault)) "wildcard does not turn invalid literal operands into a miss"
  for text in ["match(f(x)){case _{return r(x);}case 0{return Missing;}default{return r(x);}}","match(f(x)){case _{return r(x);}default{return ();}}","match(f(x)){case _{return r(x);}case y{return w(x);}default{return r(x);}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=23 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "original raw wildcard skips tail but all static obligations remain"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWildcardMatchScopes
/-! Original named/discarded slots and nested ordered wildcard matches retain their
scopes. Separate literal Core paths expose both hidden scrutinee environments. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWildcardMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WildcardMatchScopes",by decide⟩],by decide⟩⟩,109⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 41))) (call 6 3) (.var 3)
private def inner : Core.Expr := .letE (call 4 2) innerTail
private def outerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) inner (call 4 2)
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case 0{match(r(z)){case 41{return w(z);}case _{return z;}default{return r(z);}}}case _{return r(z);}default{return w(z);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"wildcard-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternDenotes p v)) := do
  match shape : p.value with
  | .literal literal => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal pattern")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm,wildArm],some d⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && armsSpan.contains wildArm.span && armsSpan.contains d.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte ∧ arm.span.endByte≤wildArm.span.startByte ∧ wildArm.span.endByte≤d.span.startByte)) "nested original scrutinee/case/default order"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let p ← pattern arm.value.pattern; let a ← body i arm.value.body; let b ← body i wildArm.value.body; let dc ← body i d
      match wild : wildArm.value.pattern.value with
      | .wildcard marker =>
          check (wildArm.span.contains wildArm.value.pattern.span && wildArm.span.contains wildArm.value.body.span && decide (marker=wildArm.value.pattern.span ∧ marker.endByte=marker.startByte+1)) "original one-byte wildcard marker and branch ranges"
          if same : sc.1=.word then return ⟨.letE sc.2.core (.ifE (.binary .wordEq (.var 0) (.word p.1)) (a.core.weakenAt 0) (b.core.weakenAt 0)),by
            rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (entries := [(arm,some p.1,a.core),(wildArm,none,b.core)]) (same ▸ sc.2.evidence) rfl
              (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact .literal p.2.down; exact .wildcard wild) (.inl rfl)
              (by intro entry h; simp only [List.mem_cons,List.not_mem_nil,or_false] at h; rcases h with rfl|rfl; exact a.evidence; exact b.evidence) rfl (by intro entry h; cases List.mem_singleton.mp h; exact dc.evidence) rfl⟩
          else throw (IO.userError "scrutinee type")
      | _ => throw (IO.userError "original wildcard")
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm,wildArm],some d⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      have wildSmaller : sizeOf wildArm.value.body < sizeOf wildArm := by rcases wildArm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let p ← pattern arm.value.pattern
      match wild : wildArm.value.pattern.value with
      | .wildcard marker => match actual : sc.value with
        | .word v =>
            if same : v=p.1 then let r ← rawBody table env sc.final arm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .hit (.literal (same.symm ▸ p.2.down))) r.evidence⟩
            else let r ← rawBody table env sc.final wildArm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm,wildArm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .miss (.literal p.2.down) same (.wildcard (.wildcard wild))) r.evidence⟩
        | _ => throw (IO.userError "raw actual Word before wildcard")
      | _ => throw (IO.userError "raw wildcard")
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.word,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.word,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.word,.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[w 0,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (w 0),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 41),.letBody innerTail (w 0::w 41::w 14::env)::pending,allocated⟩),(51,⟨.ret (.bool true),.ifBranches (call 6 3) (.var 3) (w 41::w 0::w 41::w 14::env)::pending,allocated⟩),(67,⟨.ret (w 14),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (68-spent) cp=.done result final)) "saved named/discarded/two hidden slots and literal original environments"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedWildcardMatchScopes
open ParsedWildcardMatchScopes
def frontendParsedWildcardMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 67
  verify source [w 0,w 42,w 99] [w 0,w 42,w 99,w 14] (w 14) 53
  verify source [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 43
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordMatchEffects
/-! Original literal cases, preparation and source costs are independent of the
literal Core walker. Allocation exposes repeated scrutinees and selected effects. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWordMatchEffects
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchEffects",by decide⟩],by decide⟩⟩,97⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def rest : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 3 1)
  (.ifE (.binary .wordEq (.var 0) (.word (word 1))) (call 3 1) (call 2 1))
private def tailCore (only : Bool) : Core.Expr := if only then call 2 1 else .ifE (.binary .wordEq (.var 0) (.word (word 0))) (call 2 1) rest
private def core (only : Bool) : Core.Expr := .letE (call 3 0) (tailCore only)
private def sourceBody (only : Bool) := "match(f(x)){"++(if only then "" else "case 0{return r(x);}case 0x00{return w(x);}case 1{return w(x);}")++"default{return r(x);}}"
private def parsed (body : String) : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){"++body++"}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-effects.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "original whole source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def returned (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | _ => throw (IO.userError "return body")
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternDenotes p v)) := do
  match shape : p.value with
  | .literal literal => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal pattern")
private def arms (i : LocalTypeInputs) (cs : List Syntax.MatchCase) : IO (Σ entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)), PLift (entries.map Prod.fst=cs ∧ ∀ entry ∈ entries, WordMatchPatternClassifies entry.1.value.pattern entry.2.1 ∧ RecursiveComputationReturnTreeElaborates types owner i entry.1.value.body entry.2.2 .word)) := do
  match shape : cs with
  | [] => return ⟨[],⟨by rw [shape]; exact ⟨rfl,by simp⟩⟩⟩
  | c::rest =>
      check (c.span.contains c.value.pattern.span && c.span.contains c.value.body.span && decide (c.value.pattern.span.endByte≤c.value.body.span.startByte)) "original pattern/body order"
      let p ← pattern c.value.pattern; let b ← returned i c.value.body; let tail ← arms i rest
      return ⟨(c,some p.1,b.core)::tail.1,⟨by rw [shape]; refine ⟨by simp [tail.2.down.1],?_⟩; intro entry member; rcases List.mem_cons.mp member with rfl|member; exact ⟨.literal p.2.down,b.evidence⟩; exact tail.2.down.2 entry member⟩⟩
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  match shape : b with
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨cs,some d⟩⟩⟩]⟩ =>
      check (b.span.contains matchSpan && matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains d.span && cs.all (fun c => armsSpan.contains c.span) && decide (scrutineeSpan.endByte≤armsSpan.startByte)) "original match scrutinee/arms/default spans"
      let sc ← child i e; let bs ← arms i cs; let dc ← returned i d
      if same : sc.1=.word then return ⟨.letE sc.2.core (bs.1.foldr (fun en t => match en.2.1 with | none => en.2.2.weakenAt 0 | some v => .ifE (.binary .wordEq (.var 0) (.word v)) (en.2.2.weakenAt 0) t) (dc.core.weakenAt 0)),by rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (same ▸ sc.2.evidence) bs.2.down.1 (fun e h => (bs.2.down.2 e h).1) (.inl rfl) (fun e h => (bs.2.down.2 e h).2) rfl (by intro e h; cases List.mem_singleton.mp h; exact dc.evidence) (by simp only [Option.map_some]; induction bs.1 with | nil => rfl | cons e es ih => cases tag : e.2.1 <;> simp only [List.foldr_cons,tag,ih,Option.map_some])⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "original terminal match")
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) (fixed : Core.Expr) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=fixed ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=fixed then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,fixed,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have compiled := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          have prep : RecursiveComputationFunctionPrepares types owner source args ⟨ps.actual,fixed,.word⟩ := ⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩
          have accepted := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr prep
          have matching : args.map (·.type)=ps.statics.context.values.reverse := by
            have layout := congrArg List.reverse (RuntimeParametersBind.argument_types ps.bound).symm
            simpa only [←erased,LocalInputs.toTypeInputs_context,LocalInputs.context,Resolved.LocalScope.values,List.map_map,Function.comp_def,List.map_reverse,List.reverse_reverse] using layout
          have _ : (prepareRecursiveComputationFunction? types owner source args).map PreparedRuntimeFunction.toCompiled=some ⟨ps.statics,fixed,.word⟩ := by
            rw [prepareComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have whole (fuel) (s) : runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial fixed (args.reverse.map (·.value)) s)) := by
            rw [runRecursiveComputationFunction?,runComputationFunction?_factorization,compiled]; simp only [bind,Option.bind_some,matching,↓reduceIte]
          have _ := accepted; have _ := whole
          check (decide (ps.actual.environment.values=args.reverse.map (·.value))) "original actual reverse once"
          return ⟨⟨ps.actual,fixed,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def choose (v : Core.Value) (cs : List Syntax.MatchCase) (d : Syntax.Block) : IO (Σ selected : Syntax.Block × Nat, PLift (WordMatchChooses v cs (some d) selected.1 selected.2)) := do
  match shape : cs with
  | [] => return ⟨(d,0),⟨by rw [shape]; exact .fallback⟩⟩
  | c::rest => match actual : v with
    | .word w =>
        let p ← pattern c.value.pattern
        if same : w=p.1 then return ⟨(c.value.body,1),⟨by rw [shape,actual]; exact .hit (.literal (same.symm ▸ p.2.down))⟩⟩
        else let tail ← choose (.word w) rest d; return ⟨(tail.1.1,tail.1.2+1),⟨by rw [shape,actual]; exact .miss (.literal p.2.down) same tail.2.down⟩⟩
    | _ => throw (IO.userError "actual non-Word comparison")
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨cs,some d⟩⟩⟩]⟩ =>
      let sc ← rawChild table env s e; let c ← choose sc.value cs d
      match selected : c.1.1 with
      | ⟨_,[⟨_,.returnStmt (some child)⟩]⟩ => let r ← rawChild table env sc.final child; return ⟨r.value,r.final,sc.cost+r.cost+2+7*c.1.2,by rw [shape]; exact .wordMatch sc.evidence c.2.down (by rw [selected]; exact .expression r.evidence)⟩
      | _ => throw (IO.userError "selected return")
  | _ => throw (IO.userError "raw body")
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private def arguments (swap : Bool := false) (location : Nat := 2) : List TypedRuntimeArgument := [allocator,if swap then reader 1 else writer location,if swap then writer location else reader 1,⟨.word,w 14,.word⟩]
private def positive (only swap : Bool) (s final : Core.Store) (value : Core.Value) (cost : Nat) (location : Nat := 2) : IO Unit := do
  let source ← parsed (sourceBody only)
  let args ← (arguments swap location).mapM fun original => do
    match built : buildRuntimeArgument? original.value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=original.value ∧ a.type=original.type)) "raw construction preserves complete captures"; return a
    | none => throw (IO.userError "structural actual arguments")
  let p ← prepare source args (core only)
  let i := p.1.inputs; let env := i.environment.values
  let raw ← rawBody i.names i.environment s source.value.body; let manual ← path 80 (core only) env s
  check (decide (raw.value=value ∧ raw.final=final ∧ raw.cost=cost ∧ manual.value=value ∧ manual.final=final ∧ manual.cost=cost)) "independent original source and literal Core expectations"
  have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
  have _ := p.2.down.1.body.core_hasType RecursiveLocalComputationElaborates.core_hasType
  have _ := (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,p.2.down.1.body⟩
  have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
  have allK := fun k => ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) p.2.down.1.body ids k
  have _ := allK
  let world := List.replicate s.length Core.Ty.word
  check (validateRuntimeInputs world args s == (s.all (fun v => v.type==.word) && location != 700)) "same-world validation also inspects unused captured references"
  if validated : validateRuntimeInputs world args s=true then
    have runtime := validateRuntimeInputs_iff.mp validated
    have finitePath : Core.Steps manual.cost
        (.initial p.1.core p.1.inputs.environment.values s) (.final manual.value manual.final) := by
      rw [p.2.down.2.1]
      exact manual.evidence []
    have safe := ComputationFunctionPrepares.runtime_typed_execution (F := RecursiveLocalComputationFragment)
      (ChildElab := RecursiveLocalComputationElaborates) (ChildEval := RecursiveLocalComputationEvaluates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost)
      RecursiveLocalComputationElaborates.core_hasType RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.evaluates_insert_iff
      RecursiveLocalComputationElaborates.evaluates_iff recursiveLocalComputationEvaluates_iff_exists_cost RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation elaborateRecursiveLocalComputation?_iff p.2.down.1 runtime.1 runtime.2 ⟨manual.value, manual.final, Core.steps_from_initial_sound finitePath⟩
    have actualWorld : ∃ future, Core.WorldExtends world future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ RecursiveComputationReturnTreeEvaluatesWithCost owner i.names i.environment s source.value.body manual.value manual.final manual.cost := by
      obtain ⟨future,t,v,n,ext,st,_,r,paths,_,_⟩ := safe.2
      have fixedPath : Core.Steps manual.cost (.initial p.1.core env s) (.final manual.value manual.final) := by rw [p.2.down.2.1]; exact manual.evidence []
      obtain ⟨rfl,rfl,rfl⟩ := (paths []).final_unique fixedPath
      exact ⟨future,ext,st,r⟩
    have _ := actualWorld
  else check (!s.all (fun v => v.type==.word) || location==700) "opt-in rejection does not replace raw selected/default success"
  check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 remains None"
  for fuel in List.range (cost+2) do
    have _ := runComputationFunction?_factorization elaborateRecursiveLocalComputation? types owner source args fuel s
    check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial (core only) env s)) ∧ runRuntimeComputationFunction? types owner source args fuel s=none)) "full entry outcome and original tag"
    match stopped : Core.runStateful fuel (.initial (core only) env s) with
    | .done v t => check (decide (cost≤fuel ∧ v=value ∧ t=final)) "exact threshold"
    | .outOfFuel cp =>
        have _ := (manual.evidence []).residual_of_outOfFuel stopped
        for more in [0,1,7,cost] do
          have _ := Core.runStateful_resume stopped more
          check (decide (Core.runStateful more cp=Core.runStateful (fuel+more) (.initial (core only) env s) ∧ Core.runStateful (cost-fuel) cp=.done value final)) "every genuine checkpoint and full resume"
    | .fault _ _ => throw (IO.userError "successful manual path faulted")
  let scr ← path 40 (call 3 0) env s
  let cp : Core.State := ⟨.ret scr.value,[.letBody (tailCore only) env],scr.final⟩
  check (decide (scr.cost=13 ∧ Core.runStateful 14 (.initial (core only) env s)=.outOfFuel cp ∧ Core.runStateful (cost-14) cp=.done value final)) "one allocation and actual hidden-let saved environment"
  unless only do
    let cp : Core.State := ⟨.ret (.bool (scr.value==w 0)),[.ifBranches (call 2 1) rest (scr.value::env)],scr.final⟩
    check (decide (Core.runStateful 21 (.initial (core only) env s)=.outOfFuel cp ∧ Core.runStateful (cost-21) cp=.done value final)) "genuine ifBranches with actual saved scrutinee"
  check (decide (Core.runStateful cost ⟨.eval (core only) env,[.pairApply (.bool true)],s⟩=.outOfFuel ⟨.ret value,[.pairApply (.bool true)],final⟩ ∧ Core.runStateful (cost+1) ⟨.eval (core only) env,[.pairApply (.bool true)],s⟩=.done (.pair (.bool true) value) final)) "literal retained continuation outside source cost"
end ParsedWordMatchEffects
open ParsedWordMatchEffects
def frontendParsedWordMatchEffectTests : IO Unit := do
  positive false false [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30
  positive false false [w 1,w 41,w 99] [w 1,w 41,w 14,w 14] (w 14) 51
  for n in [7,2^255,Core.wordModulus-1] do positive false false [w n,w 41,w 99] [w n,w 41,w 99,w 14] (w 41) 44
  positive false true [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 37
  positive true false [.bool false,w 41,w 99] [.bool false,w 41,w 99,w 14] (w 41) 23
  positive false false [w 0,w 41,w 99] [w 0,w 41,w 99,w 14] (w 41) 30 700
  positive false false [w 0,.bool true,w 99] [w 0,.bool true,w 99,w 14] (.bool true) 30
  let source ← parsed (sourceBody false); let args := arguments; let p ← prepare source args (core false); let env := p.1.inputs.environment.values
  let s := [.bool false,w 41,w 99]; let t := s++[w 14]
  let fault : Core.StatefulRunResult := .fault (.invalidBinaryOperands .wordEq (.bool false) (w 0)) ⟨.ret (w 0),[.binaryApply .wordEq (.bool false),.ifBranches (call 2 1) rest (.bool false::env)],t⟩
  let missing : Core.StatefulRunResult := .fault (.invalidCellLocation 1) ⟨.ret (.cellRef .word 1),[.loadCellApply],[w 14]⟩
  for (store,threshold,expected) in [(s,20,fault),([],43,missing)] do
    for fuel in List.range (threshold+3) do
      let out := Core.runStateful fuel (.initial (core false) env store)
      check (decide (runRecursiveComputationFunction? types owner source args fuel store=some (.word,out))) "same prepared entry on arbitrary stores"
      if fuel<threshold then match out with
        | .outOfFuel cp => check (decide (Core.runStateful 100 cp=expected)) "pre-fault genuine resumption"
        | _ => throw (IO.userError "first fault threshold")
      else check (decide (out=expected)) "fault20/43 retain allocation, original operands and selected body"
  for text in ["match(f(x)){case 0{return r(x);}case 0{return Missing;}default{return r(x);}}","match(f(x)){case 0{return r(x);}default{return ();}}"] do
    let unselected ← parsed text; let ps ← parameters .empty .empty unselected.value.signature.parameters.elements args
    let raw ← rawBody ps.actual.names ps.actual.environment [w 0,w 41,w 99] unselected.value.body
    check (decide (raw.value=w 41 ∧ raw.final=[w 0,w 41,w 99,w 14] ∧ raw.cost=30 ∧ compileRecursiveComputationFunction? types owner unselected=none)) "negative original parameters and raw first hit versus whole all-arm rejection"
  for text in ["match(f(x)){case 0{return r(x);}}","match(f(x),x){case (0,0){return r(x);}default{return r(x);}}","match(f(x)){case y{return r(x);}default{return r(x);}}","match(f(x)){case "++toString Core.wordModulus++"{return r(x);}default{return r(x);}}","match(f(x)==0){case 0{return r(x);}default{return r(x);}}",sourceBody false++"return x;"] do
    let source ← parsed text
    check (decide (compileRecursiveComputationFunction? types owner source=none)) "whole-arm typing and exact pattern/terminal gates"
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendParsedWordMatchScopes
/-! Original named/discarded slots and nested literal matches retain their source
scopes. Literal Core paths separately expose both hidden scrutinee environments. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend
namespace ParsedWordMatchScopes
private def check (p : Bool) (label : String) : IO Unit := do unless p do throw (IO.userError label)
private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WordMatchScopes",by decide⟩],by decide⟩⟩,103⟩
private def word (n : Nat) := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def call (f x : Nat) : Core.Expr := .apply (.var f) (.var x)
private def innerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 41))) (call 6 3) (.var 3)
private def inner : Core.Expr := .letE (call 4 2) innerTail
private def outerTail : Core.Expr := .ifE (.binary .wordEq (.var 0) (.word (word 0))) inner (call 4 2)
private def outer : Core.Expr := .letE (call 5 1) outerTail
private def tailCore : Core.Expr := .letE (call 2 0) outer
private def core : Core.Expr := .letE (.var 0) tailCore
private def pending : List Core.Frame := [.pairApply (.bool true)]
private def parsed : IO Syntax.FunctionDecl := do
  let text := "function route(f:F,w:W,r:R,x:X) returns(X){let z=x;r(z);match(f(z)){case 0{match(r(z)){case 41{return w(z);}default{return z;}}}default{return r(z);}}}"
  let file : Syntax.SourceFile := ⟨⟨.main,"word-match-scopes.sol"⟩,text⟩
  let .ok lexed := Syntax.Lexer.lex file | throw (IO.userError "lexer")
  let .ok source next := Syntax.Parser.functionDecl .module (Syntax.Parser.State.initial file lexed) | throw (IO.userError "original declaration")
  check (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd && decide (source.span=⟨file.id,0,text.utf8ByteSize⟩) && source.span.contains source.value.signature.span && source.span.contains source.value.body.span) "complete original source ranges"
  return source
private def types : TypeNameTable := [(["F"],.function .word .word),(["W"],.function .word .word),(["R"],.function .word .word),(["X"],.word)]
private def meaning (source : Syntax.TypeExpr) : IO (Σ t, PLift (StructuralTypeDenotes types source t)) := do
  match shape : source with
  | ⟨_,.named name none⟩ => match found : types.lookup? (qualifiedTypeNameKey name) with
    | some t => return ⟨t,⟨by rw [shape]; exact .named (TypeNameTable.lookup?_iff.mp found)⟩⟩
    | none => throw (IO.userError "annotation")
  | _ => throw (IO.userError "annotation shape")
private structure Parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) where
  statics : LocalTypeInputs
  actual : LocalInputs
  declared : RuntimeParametersDeclareFrom types owner s ps statics
  bound : RuntimeParametersBindFrom types owner a ps args actual
private def parameters (s : LocalTypeInputs) (a : LocalInputs) (ps : List Syntax.FunctionParameter) (args : List TypedRuntimeArgument) : IO (Parameters s a ps args) := do
  match shape : ps, supplied : args with
  | [],[] => return ⟨s,a,by rw [shape]; exact .nil,by rw [shape,supplied]; exact .nil⟩
  | ⟨span,.typed none name annotation⟩::rest,arg::tail =>
      check (span.contains name.span && span.contains annotation.span) "original parameter fields"
      let m ← meaning annotation
      if same : m.1=arg.type then
        if unused : name.value ∉ s.names.map Prod.fst ∧ name.value ∉ a.names.map Prod.fst then
          let next ← parameters (s.bindFresh owner name.value arg.type) (a.bindFresh owner name.value arg.type arg.value arg.valueTyped) rest tail
          return ⟨next.statics,next.actual,by rw [shape]; exact .cons (same ▸ m.2.down) unused.1 next.declared,by rw [shape,supplied]; exact .cons (same ▸ m.2.down) unused.2 next.bound⟩
        else throw (IO.userError "duplicate parameter")
      else throw (IO.userError "argument type")
  | _,_ => throw (IO.userError "parameter arity")
private structure Path (e : Core.Expr) (env : Core.Environment) (s : Core.Store) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : ∀ k, Core.Steps cost ⟨.eval e env,k,s⟩ ⟨.ret value,k,final⟩
private def path : (depth : Nat) → (e : Core.Expr) → (env : Core.Environment) → (s : Core.Store) → IO (Path e env s)
  | 0,_,_,_ => throw (IO.userError "manual depth")
  | n+1,e,env,s => do
    match shape : e with
    | .var i => match found : env[i]? with
      | some v => return ⟨v,s,1,fun _ => by rw [shape]; exact .cons (.var found) .refl⟩
      | none => throw (IO.userError "manual variable")
    | .word v => return ⟨.word v,s,1,fun _ => by rw [shape]; exact .cons .word .refl⟩
    | .letE a b =>
        let l ← path n a env s; let r ← path n b (l.value::env) l.final
        return ⟨r.value,r.final,l.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.letE (l.evidence _) (r.evidence _)⟩
    | .apply f a =>
        let fn ← path n f env s; let arg ← path n a env fn.final
        match fv : fn.value with
        | .closure _ _ b captured => let r ← path n b (arg.value::captured) arg.final; return ⟨r.value,r.final,fn.cost+arg.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.apply (fv ▸ fn.evidence _) (arg.evidence _) (r.evidence [])⟩
        | _ => throw (IO.userError "manual closure")
    | .binary op a b =>
        let l ← path n a env s; let r ← path n b env l.final
        match applied : op.apply l.value r.value with
        | some v => return ⟨v,r.final,l.cost+r.cost+3,fun _ => by rw [shape]; exact CostStepComposition.binary (l.evidence _) (r.evidence _) applied⟩
        | none => throw (IO.userError "manual primitive")
    | .ifE c a b =>
        let g ← path n c env s
        match gv : g.value with
        | .bool true => let r ← path n a env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifTrue (gv ▸ g.evidence _) (r.evidence _)⟩
        | .bool false => let r ← path n b env g.final; return ⟨r.value,r.final,g.cost+r.cost+2,fun _ => by rw [shape]; exact CostStepComposition.ifFalse (gv ▸ g.evidence _) (r.evidence _)⟩
        | _ => throw (IO.userError "manual guard")
    | .loadCell (.var i) => match ref : env[i]? with
      | some (.cellRef _ l) => match read : s.read? l with
        | some v => return ⟨v,s,3,fun _ => by rw [shape]; exact .cons .enterLoadCell (.cons (.var ref) (.cons (.applyLoadCell read) .refl))⟩
        | none => throw (IO.userError "manual missing cell")
      | _ => throw (IO.userError "manual reference")
    | .newCell .word (.var i) => match found : env[i]? with
      | some v => return ⟨.cellRef .word s.length,s++[v],3,fun _ => by rw [shape]; exact .cons .enterNewCell (.cons (.var found) (.cons .applyNewCell .refl))⟩
      | none => throw (IO.userError "manual allocation")
    | .storeCell (.var i) (.var j) => match ref : env[i]?, val : env[j]? with
      | some (.cellRef _ l),some v => match read : s.read? l, written : s.write? l v with
        | some _,some t => return ⟨.unit,t,5,fun _ => by rw [shape]; exact .cons .enterStoreCell (.cons (.var ref) (.cons (.beginStoreCellValue read) (.cons (.var val) (.cons (.applyStoreCell written) .refl))))⟩
        | _,_ => throw (IO.userError "manual write")
      | _,_ => throw (IO.userError "manual write operands")
    | _ => throw (IO.userError "manual Core shape")
private structure Static (J : Core.Expr → Prop) where
  core : Core.Expr
  evidence : J core
private def child (i : LocalTypeInputs) (e : Syntax.Expr) : IO (Σ t, Static (fun c => RecursiveLocalComputationElaborates i.names i.context e c t)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match found : i.names.lookup? name.value with
    | some id => match typed : i.context.lookup? id, indexed : Resolved.LocalScope.index? i.context.ids id with
      | some t,some n => return ⟨t,.var n,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp found)) (.var (Resolved.LocalScope.index?_iff.mp indexed)) (.var (Resolved.LocalScope.lookup?_iff.mp typed))⟩
      | _,_ => throw (IO.userError "static row")
    | none => throw (IO.userError "static name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      check (e.span.contains f.span && e.span.contains a.span && decide (f.span.endByte≤a.span.startByte)) "original callee/argument ranges"
      let l ← child i f; let r ← child i a
      match ft : l.1 with
      | .function t u => if same : r.1=t then return ⟨u,.apply l.2.core r.2.core,by rw [shape]; exact .application (by simpa only [ft] using l.2.evidence) (by simpa only [same] using r.2.evidence)⟩ else throw (IO.userError "static argument")
      | _ => throw (IO.userError "static callee")
  | _ => throw (IO.userError "static child shape")
termination_by sizeOf e
private def pattern (p : Syntax.Pattern) : IO (Σ v, PLift (WordMatchPatternDenotes p v)) := do
  match shape : p.value with
  | .literal literal => match decoded : interpretWordLiteral? literal with
    | some v => return ⟨v,⟨⟨literal,shape,interpretWordLiteral?_sound decoded⟩⟩⟩
    | none => throw (IO.userError "strict Word literal")
  | _ => throw (IO.userError "literal pattern")
private def body (i : LocalTypeInputs) (b : Syntax.Block) : IO (Static (fun c => RecursiveComputationReturnTreeElaborates types owner i b c .word)) := do
  check (b.value.all fun statement => b.span.contains statement.span) "original statement ranges"
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← child i e; if same : r.1=.word then return ⟨r.2.core,by rw [shape]; exact .expression (same ▸ r.2.evidence)⟩ else throw (IO.userError "return type")
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← child i e
      if unused : name.value ∉ i.names.map Prod.fst then
        let r ← body (i.bindFresh owner name.value a.1) ⟨span,rest⟩
        return ⟨.letE a.2.core r.core,by rw [shape]; exact .inferred a.2.evidence r.evidence⟩
      else throw (IO.userError "source binding freshness")
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← child i e; let r ← body i ⟨span,rest⟩; return ⟨.letE a.2.core (r.core.weakenAt 0),by rw [shape]; exact .discard a.2.evidence r.evidence⟩
  | ⟨_,[⟨matchSpan,.matchWith ⟨scrutineeSpan,⟨e,[]⟩⟩ ⟨armsSpan,⟨[arm],some d⟩⟩⟩]⟩ =>
      check (matchSpan.contains scrutineeSpan && scrutineeSpan.contains e.span && matchSpan.contains armsSpan && armsSpan.contains arm.span && armsSpan.contains d.span && arm.span.contains arm.value.pattern.span && arm.span.contains arm.value.body.span && decide (e.span.endByte≤arm.span.startByte ∧ arm.span.endByte≤d.span.startByte)) "nested original scrutinee/case/default order"
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← child i e; let p ← pattern arm.value.pattern; let a ← body i arm.value.body; let dc ← body i d
      if same : sc.1=.word then return ⟨.letE sc.2.core (.ifE (.binary .wordEq (.var 0) (.word p.1)) (a.core.weakenAt 0) (dc.core.weakenAt 0)),by
        rw [shape]; exact .wordMatch (defaultEntry := some (d,dc.core)) (entries := [(arm,some p.1,a.core)]) (same ▸ sc.2.evidence) rfl
          (by intro entry h; cases List.mem_singleton.mp h; exact .literal p.2.down) (.inl rfl)
          (by intro entry h; cases List.mem_singleton.mp h; exact a.evidence) rfl (by intro entry h; cases List.mem_singleton.mp h; exact dc.evidence) rfl⟩
      else throw (IO.userError "scrutinee type")
  | _ => throw (IO.userError "fixed original body shape")
termination_by sizeOf b
private def prepare (source : Syntax.FunctionDecl) (args : List TypedRuntimeArgument) : IO (Σ p, PLift (RecursiveComputationFunctionPrepares types owner source args p ∧ p.core=core ∧ p.returnType=.word)) := do
  let ps ← parameters .empty .empty source.value.signature.parameters.elements args; let b ← body ps.actual.toTypeInputs source.value.body
  match clause : source.value.signature.returnsClause with
  | some ⟨_,⟨_,[ann]⟩⟩ =>
      let m ← meaning ann
      if same : m.1=.word ∧ b.core=core then
        if policy : source.value.signature.genericParameters=none ∧ source.value.signature.whereClause=none ∧ source.value.signature.modifiers.publicMarker=none ∧ source.value.signature.modifiers.payableMarker=none then
          have h : RuntimeFunctionHeader types source.value.signature .word := ⟨policy.1,policy.2.1,policy.2.2.1,policy.2.2.2,by rw [clause]; exact .single (same.1 ▸ m.2.down)⟩
          have erased := (RuntimeParametersBind.erase_values ps.bound).result_unique ps.declared
          have compilation : RecursiveComputationFunctionCompiles types owner source ⟨ps.statics,core,.word⟩ := ⟨h,ps.declared,by simpa only [erased,same.2] using b.evidence⟩
          have _ := (compileComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr compilation
          check (decide (ps.actual.environment.values=args.reverse.map (·.value) ∧ ps.actual.names=[("x",⟨owner,3⟩),("r",⟨owner,2⟩),("w",⟨owner,1⟩),("f",⟨owner,0⟩)])) "original bindings and actual reverse once"
          return ⟨⟨ps.actual,core,.word⟩,⟨⟨⟨h,ps.bound,by simpa only [same.2] using b.evidence⟩,rfl,rfl⟩⟩⟩
        else throw (IO.userError "header policy")
      else throw (IO.userError "independent literal Core/return annotation")
  | _ => throw (IO.userError "original return clause")
private structure Raw (J : Core.Value → Core.Store → Nat → Prop) where
  value : Core.Value
  final : Core.Store
  cost : Nat
  evidence : J value final cost
private def rawChild (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (e : Syntax.Expr) : IO (Raw (RecursiveLocalComputationEvaluatesWithCost table env s e)) := do
  match shape : e with
  | ⟨_,.identifier name⟩ => match named : table.lookup? name.value with
    | some id => match found : env.lookup? id with
      | some v => return ⟨v,s,1,by rw [shape]; exact .pure (.identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found))⟩
      | none => throw (IO.userError "raw row")
    | none => throw (IO.userError "raw name")
  | ⟨_,.call f ⟨_,[a]⟩⟩ =>
      let l ← rawChild table env s f; let r ← rawChild table env l.final a
      match fv : l.value with
      | .closure _ _ b captured => let p ← path 50 b (r.value::captured) r.final; return ⟨p.value,p.final,l.cost+r.cost+p.cost+3,by rw [shape]; exact .application (fv ▸ l.evidence) r.evidence (p.evidence [])⟩
      | _ => throw (IO.userError "raw callee")
  | _ => throw (IO.userError "raw child")
termination_by sizeOf e
private def rawBody (table : LocalNameTable) (env : Resolved.Environment) (s : Core.Store) (b : Syntax.Block) : IO (Raw (RecursiveComputationReturnTreeEvaluatesWithCost owner table env s b)) := do
  match shape : b with
  | ⟨_,[⟨_,.returnStmt (some e)⟩]⟩ => let r ← rawChild table env s e; return ⟨r.value,r.final,r.cost,by rw [shape]; exact .expression r.evidence⟩
  | ⟨span,⟨_,.letDecl name none (some e)⟩::rest⟩ =>
      let a ← rawChild table env s e; let id := Resolved.freshLocalId owner (table.map Prod.snd)
      let r ← rawBody ((name.value,id)::table) ((id,a.value)::env) a.final ⟨span,rest⟩
      return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .inferred a.evidence r.evidence⟩
  | ⟨span,⟨_,.expression e true⟩::rest⟩ => let a ← rawChild table env s e; let r ← rawBody table env a.final ⟨span,rest⟩; return ⟨r.value,r.final,a.cost+r.cost+2,by rw [shape]; exact .discard a.evidence r.evidence⟩
  | ⟨_,[⟨_,.matchWith ⟨_,⟨e,[]⟩⟩ ⟨_,⟨[arm],some d⟩⟩⟩]⟩ =>
      have smaller : sizeOf arm.value.body < sizeOf arm := by rcases arm with ⟨_,⟨_,_⟩⟩; simp; omega
      let sc ← rawChild table env s e; let p ← pattern arm.value.pattern
      match actual : sc.value with
      | .word v =>
          if same : v=p.1 then let r ← rawBody table env sc.final arm.value.body; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .hit (.literal (same.symm ▸ p.2.down))) r.evidence⟩
          else let r ← rawBody table env sc.final d; return ⟨r.value,r.final,sc.cost+r.cost+2+7,by rw [shape]; exact .wordMatch (cases := [arm]) (defaultBody := some d) sc.evidence (by rw [actual]; exact .miss (.literal p.2.down) same .fallback) r.evidence⟩
      | _ => throw (IO.userError "raw actual Word")
  | _ => throw (IO.userError "raw fixed body shape")
termination_by sizeOf b
private def allocator : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.newCell .word (.var 0)) (.loadCell (.var 2))) [.cellRef .word 0],.closure (.cons .cellRef .nil) (.letE (.newCell (.var rfl)) (.loadCell (.var rfl)))⟩
private def reader (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.loadCell (.var 1)) [.cellRef .word l],.closure (.cons .cellRef .nil) (.loadCell (.var rfl))⟩
private def writer (l : Nat) : TypedRuntimeArgument := ⟨.function .word .word,.closure .word .word (.letE (.storeCell (.var 1) (.var 0)) (.loadCell (.var 2))) [.cellRef .word l],.closure (.cons .cellRef .nil) (.letE (.storeCell (.var rfl) (.var rfl)) (.loadCell (.var rfl)))⟩
private theorem runtimeArguments {world : Core.StoreTyping} (args : List TypedRuntimeArgument)
    (typed : ∀ arg ∈ args, Core.RuntimeValueHasType world arg.value arg.type) :
    Core.RuntimeEnvironmentHasTypes world (args.map (·.value)) (args.map (·.type)) := by
  induction args with
  | nil => exact .nil
  | cons a rest ih => exact .cons (typed a (by simp)) (ih (fun v member => typed v (by simp [member])))
private def verify (source : Syntax.FunctionDecl) (s final : Core.Store) (value : Core.Value) (cost : Nat) : IO Unit := do
  let rawValues := [allocator.value,(writer 2).value,(reader 1).value,w 14]
  let manual ← path 80 core rawValues.reverse s
  check (decide (manual.cost=cost ∧ manual.value=value ∧ manual.final=final)) "independent literal indices/effects/cost"
  let args ← rawValues.mapM fun value => do
    match built : buildRuntimeArgument? value with
    | some a => have _ := buildRuntimeArgument?_iff.mp built; check (decide (a.value=value ∧ a.type=value.type)) "original actual structural fields"; return a
    | none => throw (IO.userError "structural construction")
  let p ← prepare source args; let i := p.1.inputs; let env := i.environment.values
  if actualEnv : env=rawValues.reverse then
    have literal (k) : Core.Steps manual.cost ⟨.eval core env,k,s⟩ ⟨.ret manual.value,k,manual.final⟩ := by rw [actualEnv]; exact manual.evidence k
    have original : RecursiveComputationReturnTreeElaborates types owner i.toTypeInputs source.value.body core .word := by simpa only [p.2.down.2.1,p.2.down.2.2] using p.2.down.1.body
    let raw ← rawBody i.names i.environment s source.value.body
    have ids : i.environment.ids=i.toTypeInputs.context.ids := by simpa only [LocalInputs.toTypeInputs_context] using i.sameIds
    have allK (k) : Core.Steps raw.cost ⟨.eval core env,k,s⟩ ⟨.ret raw.value,k,raw.final⟩ :=
      ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := RecursiveLocalComputationFragment) (ChildElab := RecursiveLocalComputationElaborates) (ChildCost := RecursiveLocalComputationEvaluatesWithCost) RecursiveLocalComputationElaborates.core_fragment RecursiveLocalComputationFragment.weakenAt RecursiveLocalComputationFragment.insertion_paths RecursiveLocalComputationEvaluatesWithCost.toStepsWithContinuation
        (by simpa only [LocalInputs.toTypeInputs_names] using raw.evidence) original ids k
    have correspondence := (allK []).final_unique (literal [])
    check (decide (raw.cost=cost ∧ raw.value=value ∧ raw.final=final)) "independent original cost agrees with literal path"
    have _ := correspondence; have _ := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr original
    have _ := (prepareComputationFunction?_iff elaborateRecursiveLocalComputation?_iff).mpr p.2.down.1
    if validated : validateRuntimeInputs [.word,.word,.word] args s=true then
      have runtime := validateRuntimeInputs_iff.mp validated
      have reversed := runtimeArguments args.reverse (fun a member => runtime.1 a (List.mem_reverse.mp member))
      have actual : Core.RuntimeEnvironmentHasTypes [.word,.word,.word] env i.toTypeInputs.context.values := by
        dsimp only [env,i]
        simpa only [LocalInputs.environment,LocalInputs.context,LocalInputs.toTypeInputs_context,Resolved.LocalScope.values,List.map_map,Function.comp_def,p.2.down.1.parameters.argument_values,p.2.down.1.parameters.argument_types] using reversed
      have typedK : Core.ContinuationHasType [.word,.word,.word] pending .word (.product .bool .word) := .cons (.pairApply .bool) .nil
      have safe := original.runtime_checkpoint_safety RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK
      let start : Core.State := ⟨.eval core env,pending,s⟩
      let result := Core.Value.pair (.bool true) value
      have whole : Core.Steps (manual.cost+1) start ⟨.ret (.pair (.bool true) manual.value),[],manual.final⟩ := (literal pending).trans (.cons .applyPair .refl)
      for fuel in List.range (cost+2) do
        check (decide (runRecursiveComputationFunction? types owner source args fuel s=some (.word,Core.runStateful fuel (.initial core env s)))) "same prepared full entry outcome"
        match stopped : Core.runStateful fuel start with
        | .done v t => check (decide (cost+1≤fuel ∧ v=result ∧ t=final)) "body cost excludes retained typed frame"
        | .fault _ _ => throw (IO.userError "typed source continuation fault")
        | .outOfFuel cp =>
            have _ := safe.2.2 stopped
            have saved := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK stopped
            have retained : ∃ savedWorld future, Core.WorldExtends [.word,.word,.word] savedWorld ∧ Core.RuntimeStoreHasTypes savedWorld cp.store ∧ Core.WorldExtends savedWorld future ∧ Core.RuntimeStoreHasTypes future manual.final ∧ future[2]?=some .word := by
              obtain ⟨savedWorld,extension,stored,resumed⟩ := saved
              obtain ⟨future,growth,finalTyped⟩ := resumed (whole.residual_of_outOfFuel stopped).2
              exact ⟨savedWorld,future,extension,stored,growth,finalTyped,(extension.trans growth).lookup rfl⟩
            have _ := retained
            for extra in [0,1,7,cost+1] do
              have _ := Core.runStateful_resume stopped extra; have _ := whole.resumed_done_iff (additional := extra) stopped
              check (decide (Core.runStateful extra cp=Core.runStateful (fuel+extra) start ∧ Core.runStateful (cost+1-fuel) cp=.done result final)) "all genuine checkpoints and exact full resume"
      if s=[w 0,w 41,w 99] then
        let allocated := s++[w 14]
        let checkpoints : List (Nat × Core.State) := [(2,⟨.ret (w 14),.letBody tailCore env::pending,s⟩),(12,⟨.ret (w 41),.letBody outer (w 14::env)::pending,s⟩),(27,⟨.ret (w 0),.letBody outerTail (w 41::w 14::env)::pending,allocated⟩),(44,⟨.ret (w 41),.letBody innerTail (w 0::w 41::w 14::env)::pending,allocated⟩),(51,⟨.ret (.bool true),.ifBranches (call 6 3) (.var 3) (w 41::w 0::w 41::w 14::env)::pending,allocated⟩),(67,⟨.ret (w 14),pending,final⟩)]
        for (spent,cp) in checkpoints do
          if genuine : Core.runStateful spent start=.outOfFuel cp then
            have _ := original.runtime_checkpoint_world_extension RecursiveLocalComputationElaborates.core_hasType actual runtime.2 typedK genuine
            have _ := safe.2.2 genuine
            check (decide (Core.runStateful (68-spent) cp=.done result final)) "saved named/discarded/two hidden slots and literal original environments"
          else throw (IO.userError "literal checkpoint fields")
      check (decide (compileRuntimeComputationFunction? types owner source=none ∧ prepareRuntimeComputationFunction? types owner source args=none)) "old252 unchanged"
    else throw (IO.userError "same-world actual input validation")
  else throw (IO.userError "actual reverse-once environment")
end ParsedWordMatchScopes
open ParsedWordMatchScopes
def frontendParsedWordMatchScopeTests : IO Unit := do
  let source ← parsed
  verify source [w 0,w 41,w 99] [w 0,w 41,w 14,w 14] (w 14) 67
  verify source [w 0,w 42,w 99] [w 0,w 42,w 99,w 14] (w 14) 53
  verify source [w 7,w 41,w 99] [w 7,w 41,w 99,w 14] (w 41) 43
end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendRawLookupProperties
/-! Composed lookup, not hidden identities or positional machine layouts, is
the raw observation. All concrete results begin with independent source paths. -/
set_option autoImplicit false
namespace Tests.FrontendRawLookup
open Solcore Solcore.Frontend

private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"Lookup", by decide⟩], by decide⟩⟩, index⟩
private def id (declaration index : Nat) : Resolved.LocalId := ⟨owner declaration, index⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "lookup.sol"⟩, 227, 9⟩
private def ref (name : String) : Syntax.Expr := ⟨span, .identifier ⟨span, name⟩⟩
private def annotation : Syntax.TypeExpr := ⟨span, .named ⟨span, ⟨⟨⟨span, "Word"⟩, []⟩⟩⟩ none⟩
private def returned (name : String) : Syntax.Block := ⟨span, [⟨span, .returnStmt (some (ref name))⟩]⟩
private def binding (name : String) (value : Syntax.Expr) (tail : Syntax.Block) : Syntax.Block :=
  ⟨span, ⟨span, .letDecl ⟨span, name⟩ (some annotation) (some value)⟩ :: tail.value⟩
private def zero : Syntax.Expr := ⟨span, .literal ⟨span, .decimal "0"⟩⟩
private def guard : Syntax.Expr := ⟨span, .binary zero ⟨span, .equal⟩ zero⟩
private theorem zeroMeaning : WordLiteralDenotes ⟨span, .decimal "0"⟩ Core.Word.zero :=
  .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) (by decide)) .nil)
private def tree : List String → String → Syntax.Block
  | [], previous => returned previous
  | name :: rest, previous => binding name (ref previous)
      ⟨span, [⟨span, .ifThen guard (tree rest name) (some (returned name))⟩]⟩
private def leftTable : LocalNameTable := [("seed", id 0 7), ("seed", id 1 199), ("alias", id 0 7)]
private def rightTable : LocalNameTable :=
  [("ghost", id 2 80), ("seed", id 3 3), ("alias", id 3 3), ("seed", id 4 9), ("ghost", id 4 10)]
private def leftEnv (value hidden : Core.Value) : Resolved.Environment :=
  [(id 0 8, hidden), (id 1 199, .bool false), (id 0 7, value), (id 0 7, .bool true)]
private def rightEnv (value hidden : Core.Value) : Resolved.Environment :=
  [(id 2 81, hidden), (id 3 3, value), (id 4 9, .bool false), (id 3 3, .bool true), (id 0 900, .unit)]
private theorem sameLookup (value hidden : Core.Value) (name : String) :
    (leftTable.lookup? name).bind (leftEnv value hidden).lookup? =
      (rightTable.lookup? name).bind (rightEnv value hidden).lookup? := by
  by_cases seed : name = "seed"
  · subst name; rfl
  by_cases alias : name = "alias"
  · subst name; rfl
  by_cases ghost : name = "ghost"
  · subst name; rfl
  simp [leftTable, rightTable, LocalNameTable.lookup?, Ne.symm seed, Ne.symm alias, Ne.symm ghost]
private theorem counted (locals : List String) (who : Resolved.DeclarationId) (previous : String)
    (table : LocalNameTable) (env : Resolved.Environment) (value : Core.Value) (store : Core.Store)
    (head : LocalExpressionEvaluatesWithCost table env store (ref previous) value store 1) :
    TypedLetReturnTreeEvaluatesWithCost who table env store (tree locals previous) value store (10 * locals.length + 1) := by
  induction locals generalizing previous table env with
  | nil => exact .single (.expression head)
  | cons name rest ih =>
    have count : 1 + (5 + (10 * rest.length + 1) + 2) + 2 = 10 * (name :: rest).length + 1 := by simp; omega
    simpa only [count, tree, binding, guard, zero] using TypedLetReturnTreeEvaluatesWithCost.binding
      (name := ⟨span, name⟩) (annotation := annotation) head
      (.ifTrue (.equal (.wordLiteral zeroMeaning) (.wordLiteral zeroMeaning)) (ih name _ _ (.identifier .head .head)))
private theorem raw (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv value hidden) store (tree locals "seed") value store (10 * locals.length + 1) :=
  counted locals (owner 0) "seed" leftTable (leftEnv value hidden) value store
    (.identifier .head (.tail (by decide) (.tail (by decide) .head)))

theorem arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores
    (locals : List String) (value hidden : Core.Value) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (tree locals "seed") = some (value, 10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") value store (10 * locals.length + 1) ∧
    TypedLetReturnTreeEvaluates (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") value store := by
  have original := evaluateTypedLetReturnTreeWithCost?_complete (raw locals value hidden store)
  exact ⟨original,
    (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) leftTable rightTable _ _ (sameLookup value hidden) _).symm.trans original,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store),
    (typedLetReturnTreeEvaluates_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store).erase⟩

theorem reflection_does_not_drop_the_final_store_constraint
    (locals : List String) (value hidden result : Core.Value) (store final : Core.Store) (cost : Nat) :
    (TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") result final cost ↔
      result = value ∧ final = store ∧ cost = 10 * locals.length + 1) ∧
    (TypedLetReturnTreeEvaluates (owner 2) rightTable (rightEnv value hidden) store (tree locals "seed") result final ↔
      result = value ∧ final = store) := by
  constructor
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := owner 0)
        (sameLookup value hidden)).mpr path).deterministic (raw locals value hidden store)
    · rintro ⟨sameValue, sameStore, sameCost⟩; subst result; subst final; subst cost
      exact (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store)
  · constructor
    · intro path
      exact ((typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := owner 0)
        (sameLookup value hidden)).mpr path).deterministic (raw locals value hidden store).erase
    · rintro ⟨sameValue, sameStore⟩; subst result; subst final
      exact (typedLetReturnTreeEvaluates_congr_lookup_iff (sameLookup value hidden)).mp (raw locals value hidden store).erase

theorem absent_and_unbound_names_can_change_allocation_without_changing_results (value hidden : Core.Value) :
    leftTable.lookup? "ghost" = none ∧ rightTable.lookup? "ghost" = some (id 2 80) ∧
    (rightEnv value hidden).lookup? (id 2 80) = none ∧
    Resolved.freshLocalId (owner 0) (leftTable.map Prod.snd) = id 0 8 ∧
    Resolved.freshLocalId (owner 2) (rightTable.map Prod.snd) = id 2 81 ∧
    (leftEnv value hidden).lookup? (id 0 8) = some hidden ∧ (rightEnv value hidden).lookup? (id 2 81) = some hidden ∧
    leftTable.length ≠ rightTable.length ∧ (leftEnv value hidden).length ≠ (rightEnv value hidden).length ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (tree ["ghost", "seed", "seed"] "seed") = some (value, 31) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by change 4 ≠ 5; decide,
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores _ value hidden []).2.1⟩

private def shortCircuit : Syntax.Expr := ⟨span, .binary (ref "seed") ⟨span, .logicalAnd⟩ (ref "ghost")⟩
theorem composed_lookup_preserves_short_circuit_success_and_selected_absence (hidden : Core.Value) :
    evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool false) hidden) shortCircuit = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? rightTable (rightEnv (.bool false) hidden) shortCircuit = some (.bool false, 4) ∧
    evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool true) hidden) shortCircuit = none ∧
    evaluateLocalExpressionWithCost? rightTable (rightEnv (.bool true) hidden) shortCircuit = none := by
  have falsePath : LocalExpressionEvaluatesWithCost leftTable (leftEnv (.bool false) hidden) [] shortCircuit (.bool false) [] 4 :=
    .andFalse (.identifier .head (.tail (by decide) (.tail (by decide) .head)))
  have succeeded := evaluateLocalExpressionWithCost?_complete falsePath
  have absent : evaluateLocalExpressionWithCost? leftTable (leftEnv (.bool true) hidden) shortCircuit = none := by
    simp [evaluateLocalExpressionWithCost?, shortCircuit, ref, leftTable, leftEnv,
      LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  exact ⟨succeeded,
    (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ (sameLookup (.bool false) hidden) _).symm.trans succeeded,
    absent, (evaluateLocalExpressionWithCost?_congr_lookup _ _ _ _ (sameLookup (.bool true) hidden) _).symm.trans absent⟩

theorem opaque_values_keep_their_exact_representation (locals : List String) (location : Core.Location) :
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.cellRef .word location) .unit) (tree locals "seed") =
      some (.cellRef .word location, 10 * locals.length + 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.closure .word .bool (.var 90) [.unit]) .unit) (tree locals "seed") =
      some (.closure .word .bool (.var 90) [.unit], 10 * locals.length + 1) :=
  ⟨(arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores locals _ .unit []).2.1,
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores locals _ .unit []).2.1⟩

private def indexShift (binder : Resolved.LocalId) : Resolved.LocalId := { binder with binderIndex := binder.binderIndex + 10 }
private theorem indexInjective : Function.Injective indexShift := by
  intro left right same
  have owners := congrArg Resolved.LocalId.owner same
  have indices := Nat.add_right_cancel (congrArg Resolved.LocalId.binderIndex same)
  cases left; cases right; cases owners; cases indices; rfl
theorem injective_index_changes_can_preserve_raw_results_without_allocator_commutation (value : Core.Value) :
    Function.Injective indexShift ∧
    Resolved.freshLocalId (owner 0) ([id 1 0].map indexShift) ≠ indexShift (Resolved.freshLocalId (owner 0) [id 1 0]) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) [("seed", id 1 0)] [(id 1 0, value)] (binding "z" (ref "seed") (returned "z")) = some (value, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) (LocalNameTable.mapIds indexShift [("seed", id 1 0)])
      (Resolved.LocalScope.mapIds indexShift [(id 1 0, value)]) (binding "z" (ref "seed") (returned "z")) = some (value, 4) := by
  have lookup (name : String) :
      (LocalNameTable.lookup? [("seed", id 1 0)] name).bind (Resolved.LocalScope.lookup? [(id 1 0, value)]) =
        (LocalNameTable.lookup? (LocalNameTable.mapIds indexShift [("seed", id 1 0)]) name).bind
          (Resolved.LocalScope.lookup? (Resolved.LocalScope.mapIds indexShift [(id 1 0, value)])) := by
    by_cases hit : name = "seed"
    · subst name; rfl
    · simp [LocalNameTable.mapIds, LocalNameTable.lookup?, Ne.symm hit]
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) [("seed", id 1 0)] [(id 1 0, value)] []
      (binding "z" (ref "seed") (returned "z")) value [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨indexInjective, by decide, output,
    (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 0) _ _ _ _ lookup _).symm.trans output⟩

theorem changing_a_visible_first_match_really_can_change_the_result :
    ¬ (∀ name, (leftTable.lookup? name).bind (leftEnv (.bool false) .unit).lookup? =
      (rightTable.lookup? name).bind (rightEnv (.bool true) .unit).lookup?) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv (.bool false) .unit) (returned "seed") = some (.bool false, 1) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.bool true) .unit) (returned "seed") = some (.bool true, 1) := by
  refine ⟨?_, evaluateTypedLetReturnTreeWithCost?_complete (raw [] (.bool false) .unit []),
    (arbitrary_names_and_depth_preserve_exact_values_costs_and_both_stores [] (.bool true) .unit []).2.1⟩
  intro same
  have impossible := same "seed"
  change some (Core.Value.bool false) = some (Core.Value.bool true) at impossible
  cases impossible

theorem a_strict_missing_initializer_is_absent_even_when_its_name_exists_on_one_side (value hidden : Core.Value) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv value hidden) (binding "unused" (ref "ghost") (returned "seed")) = none ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv value hidden) (binding "unused" (ref "ghost") (returned "seed")) = none := by
  have absent : ¬ ∃ result cost, TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv value hidden)
      store (binding "unused" (ref "ghost") (returned "seed")) result store cost := by
    rintro ⟨result, cost, path⟩
    cases path with
    | single child => cases child
    | binding initializer _ =>
      cases initializer with
      | identifier found _ =>
        have impossible := LocalNameTable.lookup?_iff.mpr found
        change none = some _ at impossible
        cases impossible
  have rejected := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mpr absent
  exact ⟨rejected, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) _ _ _ _ (sameLookup value hidden) _).symm.trans rejected⟩

theorem strict_unused_arithmetic_keeps_its_cost_and_the_old_visible_value (word : Core.Word) (hidden : Core.Value) (store : Core.Store) :
    let body := binding "unused" ⟨span, .binary zero ⟨span, .subtract⟩ (ref "seed")⟩ (returned "seed")
    evaluateTypedLetReturnTreeWithCost? (owner 0) leftTable (leftEnv (.word word) hidden) body = some (.word word, 8) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 2) rightTable (rightEnv (.word word) hidden) body = some (.word word, 8) ∧
    TypedLetReturnTreeEvaluatesWithCost (owner 2) rightTable (rightEnv (.word word) hidden) store body (.word word) store 8 := by
  intro body
  have seed : LocalExpressionEvaluatesWithCost leftTable (leftEnv (.word word) hidden) store (ref "seed") (.word word) store 1 :=
    .identifier .head (.tail (by decide) (.tail (by decide) .head))
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) leftTable (leftEnv (.word word) hidden) store body (.word word) store 8 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 5) (tailCost := 1)
    · exact .subtract (.wordLiteral zeroMeaning) seed
    · exact .single (.expression (.identifier (.tail (by decide) .head)
        (.tail (by decide) (.tail (by decide) (.tail (by decide) .head)))))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨output, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 2) _ _ _ _ (sameLookup (.word word) hidden) body).symm.trans output,
    (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (sameLookup (.word word) hidden)).mp original⟩

private def leftInputs (word : Core.Word) : LocalInputs := ⟨[⟨"seed", id 0 7, .word, .word word, .word⟩], by change [id 0 7].Nodup; decide⟩
private def rightInputs (word : Core.Word) : LocalInputs :=
  ⟨[⟨"seed", id 1 3, .word, .word word, .word⟩, ⟨"seed", id 1 5, .bool, .bool true, .bool⟩], by change [id 1 3, id 1 5].Nodup; decide⟩
private def checkedBody := binding "x" (ref "seed") (returned "x")
private def checkedCore : Core.Expr := .letE (.var 0) (.var 0)
private theorem checkedLookup (word : Core.Word) (name : String) :
    ((leftInputs word).names.lookup? name).bind (leftInputs word).environment.lookup? =
      ((rightInputs word).names.lookup? name).bind (rightInputs word).environment.lookup? := by
  by_cases hit : name = "seed"
  · subst name; rfl
  · simp [leftInputs, rightInputs, LocalInputs.names, LocalNameTable.lookup?, Ne.symm hit]
private theorem leftElab (word : Core.Word) : TypedLetReturnTreeElaborates [(["Word"], .word)] (owner 0)
    (leftInputs word).toTypeInputs checkedBody checkedCore .word :=
  .binding (.named .head) (by change "x" ∉ ["seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))
private theorem rightElab (word : Core.Word) : TypedLetReturnTreeElaborates [(["Word"], .word)] (owner 1)
    (rightInputs word).toTypeInputs checkedBody checkedCore .word :=
  .binding (.named .head) (by change "x" ∉ ["seed", "seed"]; decide) (.identifier .head) (.var .head) (.var .head)
    (.single (.expression (.identifier .head) (.var .head) (.var .head)))

theorem even_independently_checked_and_aligned_inputs_can_have_different_checkpoints (word : Core.Word) (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? (owner 0) (leftInputs word).names (leftInputs word).environment checkedBody = some (.word word, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 1) (rightInputs word).names (rightInputs word).environment checkedBody = some (.word word, 4) ∧
    (leftInputs word).runTypedLetReturnTree? [(["Word"], .word)] (owner 0) 2 checkedBody store =
      some (.word, .outOfFuel ⟨.ret (.word word), [.letBody (.var 0) [.word word]], store⟩) ∧
    (rightInputs word).runTypedLetReturnTree? [(["Word"], .word)] (owner 1) 2 checkedBody store =
      some (.word, .outOfFuel ⟨.ret (.word word), [.letBody (.var 0) [.word word, .bool true]], store⟩) ∧
    (⟨.ret (.word word), [.letBody (.var 0) [.word word]], store⟩ : Core.State) ≠
      ⟨.ret (.word word), [.letBody (.var 0) [.word word, .bool true]], store⟩ := by
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 0) (leftInputs word).names (leftInputs word).environment store checkedBody (.word word) store 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  exact ⟨output, (evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 1) _ _ _ _ (checkedLookup word) _).symm.trans output,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨checkedCore, (leftElab word).complete, rfl⟩,
    LocalInputs.runTypedLetReturnTree?_eq_some_iff.mpr ⟨checkedCore, (rightElab word).complete, rfl⟩,
    by intro impossible; cases impossible⟩

theorem the_same_raw_observation_does_not_preserve_whole_annotation_acceptance (word : Core.Word) :
    let bad : LocalTypeInputs := ⟨[⟨"seed", id 1 3, .bool⟩], by decide⟩
    evaluateTypedLetReturnTreeWithCost? (owner 0) (leftInputs word).names (leftInputs word).environment checkedBody = some (.word word, 4) ∧
    evaluateTypedLetReturnTreeWithCost? (owner 1) bad.names [(id 1 3, .word word)] checkedBody = some (.word word, 4) ∧
    elaborateTypedLetReturnTree? [(["Word"], .word)] (owner 0) (leftInputs word).toTypeInputs checkedBody = some (checkedCore, .word) ∧
    elaborateTypedLetReturnTree? [(["Word"], .word)] (owner 1) bad checkedBody = none := by
  intro bad
  have original : TypedLetReturnTreeEvaluatesWithCost (owner 1) bad.names [(id 1 3, .word word)] [] checkedBody (.word word) [] 4 := by
    apply TypedLetReturnTreeEvaluatesWithCost.binding (initializerCost := 1) (tailCost := 1)
    · exact .identifier .head .head
    · exact .single (.expression (.identifier .head .head))
  have lookup (name : String) : ((leftInputs word).names.lookup? name).bind (leftInputs word).environment.lookup? =
      (bad.names.lookup? name).bind (Resolved.LocalScope.lookup? [(id 1 3, Core.Value.word word)]) := by
    by_cases hit : name = "seed"
    · subst name; rfl
    · simp [leftInputs, LocalInputs.names, bad, LocalTypeInputs.names, LocalNameTable.lookup?, Ne.symm hit]
  have output := evaluateTypedLetReturnTreeWithCost?_complete original
  refine ⟨(evaluateTypedLetReturnTreeWithCost?_congr_lookup (owner 0) (owner 1) _ _ _ _ lookup _).trans output,
    output, (leftElab word).complete, ?_⟩
  have initializer : elaborateLocalExpression? bad.names bad.context (ref "seed") = some (.var 0, .bool) :=
    elaborateLocalExpression?_complete (.identifier .head) (.var .head) (.var .head)
  have meaning : interpretStructuralType? [(["Word"], .word)] annotation = some .word :=
    (show StructuralTypeDenotes [(["Word"], .word)] annotation .word from .named .head).complete
  have fresh : "x" ∉ bad.names.map Prod.fst := by change "x" ∉ ["seed"]; decide
  simp only [checkedBody, binding, elaborateTypedLetReturnTree?, if_pos fresh, meaning, initializer]
  rfl

end Tests.FrontendRawLookup
end

section
-- leanmerge: from Solcore.Test.FrontendTypeGeneralMatchBoundaryProperties
/-! Symbolic original syntax. Static types do not assert a shared runtime world
or inhabitants; actual paths independently quantify over values and stores. -/
set_option autoImplicit false
namespace Tests.FrontendTypeGeneralMatchBoundary
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment
open RecursiveLocalComputationEvaluatesWithCost

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"TypeGeneralMatchBoundary",by decide⟩],by decide⟩⟩,118⟩
private def id (n : Nat) : Resolved.LocalId := ⟨owner,n⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-type-general-match-boundary.sol"⟩,0,128⟩
private def wrap : List Syntax.SourceSpan → Syntax.Pattern → Syntax.Pattern
  | [], pattern => pattern
  | outer::rest, pattern => ⟨outer,.group (wrap rest pattern)⟩
private theorem wrapMeaning {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (groups : List Syntax.SourceSpan) (meaning : WordMatchPatternClassifies pattern tag) :
    WordMatchPatternClassifies (wrap groups pattern) tag := by
  induction groups with
  | nil => exact meaning
  | cons outer rest ih => exact .group ih
private def ref (name : String) : Syntax.Expr := ⟨span,.identifier ⟨span,name⟩⟩
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some (ref "y"))⟩]⟩
private def wild (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.wildcard marker⟩,returned⟩⟩
private def literal (groups : List Syntax.SourceSpan) : Syntax.MatchCase :=
  ⟨span,⟨wrap groups ⟨span,.literal ⟨span,.decimal "0"⟩⟩,returned⟩⟩
private def source (cases : List Syntax.MatchCase) (defaultBody : Option Syntax.Block) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨ref "x",[]⟩⟩ ⟨span,⟨cases,defaultBody⟩⟩⟩]⟩
private def inputs (scrutineeType resultType : Core.Ty) : LocalTypeInputs :=
  ⟨[⟨"x",id 0,scrutineeType⟩,⟨"y",id 1,resultType⟩],by change [id 0,id 1].Nodup; decide⟩
private def environment (scrutinee result : Core.Value) : Resolved.Environment :=
  [(id 0,scrutinee),(id 1,result)]
private def core : Core.Expr := .letE (.var 0) (.var 2)
private theorem xElaborates (s t : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs s t).names (inputs s t).context (ref "x") (.var 0) s :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem yElaborates (s t : Core.Ty) : RecursiveLocalComputationElaborates
    (inputs s t).names (inputs s t).context (ref "y") (.var 1) t :=
  .pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl))
    (.var (Resolved.LocalScope.index?_iff.mp rfl)) (.var (Resolved.LocalScope.lookup?_iff.mp rfl))
private theorem literalMeaning (groups : List Syntax.SourceSpan) :
    WordMatchPatternClassifies (literal groups).value.pattern (some .zero) :=
  wrapMeaning groups (.literal ⟨⟨span,.decimal "0"⟩,rfl,
    .decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩)
private theorem defaultElaborates (s t : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs s t)
      (source [] (some returned)) core t := by
  refine ComputationReturnTreeElaborates.wordMatch (entries := [])
    (defaultEntry := some (returned,.var 1)) (xElaborates s t) rfl (by simp)
    (.inr (by simp)) (by simp) rfl ?_ ?_
  · intro entry member; cases List.mem_singleton.mp member; exact .expression (yElaborates s t)
  · simp [Core.Expr.weakenAt]
private theorem wildElaborates (s t : Core.Ty) (groups : List Syntax.SourceSpan)
    (marker : Syntax.SourceSpan) (present : Bool) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs s t)
      (source [wild groups marker] (if present then some returned else none)) core t := by
  refine ComputationReturnTreeElaborates.wordMatch (entries := [(wild groups marker,none,.var 1)])
    (defaultEntry := if present then some (returned,.var 1) else none)
    (xElaborates s t) rfl ?_ (.inr (by simp)) ?_ ?_ ?_ ?_
  · intro entry member; cases List.mem_singleton.mp member; exact wrapMeaning groups (.wildcard rfl)
  · intro entry member; cases List.mem_singleton.mp member; exact .expression (yElaborates s t)
  · cases present <;> rfl
  · cases present with
    | false => simp
    | true => intro entry member; cases List.mem_singleton.mp member; exact .expression (yElaborates s t)
  · simp [Core.Expr.weakenAt]
private theorem counted (s t : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan)
    (rest : List Syntax.MatchCase) (defaultBody : Option Syntax.Block)
    (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs s t).names (environment scrutinee result)
      store (source (wild groups marker::rest) defaultBody) result store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := (inputs s t).names) (environment := environment scrutinee result)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := ref "x") (cases := wild groups marker::rest) (defaultBody := defaultBody)
    (selected := returned) (scrutineeValue := scrutinee)
    (.pure (.identifier .head .head)) (.wildcard (wrapMeaning groups (.wildcard rfl)))
    (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
      (Resolved.LocalScope.lookup?_iff.mp rfl))))
private theorem literalPath (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))
private theorem rejection {s t : Core.Ty} {body : Syntax.Block}
    (noType : ∀ resultType, ¬ RecursiveComputationReturnTreeHasType [] owner (inputs s t) body resultType) :
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t) body = none := by
  cases accepted : elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t) body with
  | none => rfl
  | some result =>
      have elaboration := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mp accepted
      exact False.elim (noType result.2
        ((computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩))

theorem default_only_scrutinee_and_result_types_are_independent (s t : Core.Ty) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs s t) (source [] (some returned)) core t ∧
    RecursiveComputationReturnTreeHasType [] owner (inputs s t) (source [] (some returned)) t ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t)
      (source [] (some returned)) = some (core,t) ∧
    Core.HasType ((inputs s t).context.map Prod.snd) core t := by
  have elaboration := defaultElaborates s t
  exact ⟨elaboration,
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr elaboration,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType elaboration⟩

theorem original_grouped_wildcards_accept_any_scrutinee_and_result_type
    (s t : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) (present : Bool) :
    RecursiveComputationReturnTreeElaborates [] owner (inputs s t)
      (source [wild groups marker] (if present then some returned else none)) core t ∧
    RecursiveComputationReturnTreeHasType [] owner (inputs s t)
      (source [wild groups marker] (if present then some returned else none)) t ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t)
      (source [wild groups marker] (if present then some returned else none)) = some (core,t) ∧
    Core.HasType ((inputs s t).context.map Prod.snd) core t := by
  have elaboration := wildElaborates s t groups marker present
  exact ⟨elaboration,
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr ⟨_,elaboration⟩,
    (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr elaboration,
    ComputationReturnTreeElaborates.core_hasType RecursiveLocalComputationElaborates.core_hasType elaboration⟩

theorem every_actual_scrutinee_is_evaluated_and_saved_even_when_ignored
    (s t : Core.Ty) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan) (present : Bool)
    (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs s t).names (environment scrutinee result)
      store (source [wild groups marker] (if present then some returned else none)) result store 4 ∧
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ ∧
    Core.Steps 4 ⟨.eval core (environment scrutinee result).values,pending,store⟩ ⟨.ret result,pending,store⟩ := by
  refine ⟨counted s t groups marker [] _ scrutinee result store,literalPath scrutinee result store pending,?_⟩
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths
    toStepsWithContinuation (counted s t groups marker [] _ scrutinee result store)
    (wildElaborates s t groups marker present) rfl pending

theorem default_only_has_the_same_independent_four_transition_path
    (s t : Core.Ty) (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs s t).names (environment scrutinee result)
      store (source [] (some returned)) result store 4 ∧
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ := by
  refine ⟨?_,literalPath scrutinee result store pending⟩
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := (inputs s t).names) (environment := environment scrutinee result)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := ref "x") (cases := []) (defaultBody := some returned) (selected := returned)
    (scrutineeValue := scrutinee) (.pure (.identifier .head .head)) .fallback
    (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
      (Resolved.LocalScope.lookup?_iff.mp rfl))))

theorem all_fuel_and_saved_actual_values_keep_the_exact_residual_path
    (scrutinee result : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (.initial core [scrutinee,result] store)=.done result store ↔ 4≤fuel) ∧
    Core.runStateful 2 (.initial core [scrutinee,result] store)=
      .outOfFuel ⟨.ret scrutinee,[.letBody (.var 2) [scrutinee,result]],store⟩ ∧
    (∀ spent saved, Core.runStateful spent (.initial core [scrutinee,result] store)=.outOfFuel saved →
      spent<4 ∧ Core.Steps (4-spent) saved (.final result store) ∧
      ∀ additional, Core.runStateful additional saved =
        Core.runStateful (spent+additional) (.initial core [scrutinee,result] store)) := by
  have path := literalPath scrutinee result store []
  refine ⟨path.runStateful_done_iff,rfl,?_⟩
  intro spent saved stopped
  have residual := path.residual_of_outOfFuel stopped
  exact ⟨residual.1,residual.2,Core.runStateful_resume stopped⟩

theorem vacuous_compatibility_does_not_accept_empty_no_default (s t : Core.Ty) :
    (∀ resultType, ¬ RecursiveComputationReturnTreeHasType [] owner (inputs s t) (source [] none) resultType) ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t) (source [] none)=none := by
  have noType (resultType : Core.Ty) :
      ¬ RecursiveComputationReturnTreeHasType [] owner (inputs s t) (source [] none) resultType := by
    intro typing
    cases typing with
    | wordMatch _ _ _ covered _ _ =>
        rcases covered with present | ⟨arm,member,_⟩
        · cases present
        · cases member
  exact ⟨noType,rejection noType⟩

theorem a_nonword_unreachable_literal_is_rejected_despite_raw_success
    (s t : Core.Ty) (notWord : s ≠ .word) (groups : List Syntax.SourceSpan) (marker : Syntax.SourceSpan)
    (defaultBody : Option Syntax.Block) (scrutinee result : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner (inputs s t).names (environment scrutinee result)
      store (source [wild groups marker,literal groups] defaultBody) result store 4 ∧
    (∀ resultType, ¬ RecursiveComputationReturnTreeHasType [] owner (inputs s t)
      (source [wild groups marker,literal groups] defaultBody) resultType) ∧
    elaborateComputationReturnTree? elaborateRecursiveLocalComputation? [] owner (inputs s t)
      (source [wild groups marker,literal groups] defaultBody)=none := by
  have noType (resultType : Core.Ty) : ¬ RecursiveComputationReturnTreeHasType [] owner (inputs s t)
      (source [wild groups marker,literal groups] defaultBody) resultType := by
    intro typing
    cases typing with
    | wordMatch scrutineeTyping _ compatible _ _ _ =>
        rcases compatible with same | allWild
        · obtain ⟨xCore,xProof⟩ := recursiveLocalComputationHasType_iff_elaborates.mp scrutineeTyping
          have checked := elaborateRecursiveLocalComputation?_iff.mpr xProof
          rw [elaborateRecursiveLocalComputation?_iff.mpr (xElaborates s t)] at checked
          exact notWord ((congrArg Prod.snd (Option.some.inj checked)).trans same)
        · have caught := allWild (literal groups) (by simp)
          cases (literalMeaning groups).tag_unique caught
  exact ⟨counted s t groups marker [literal groups] defaultBody scrutinee result store,noType,rejection noType⟩

end Tests.FrontendTypeGeneralMatchBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendTypeGeneralMatchCountProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendWildcardMatchBoundaryProperties
/-! Symbolic original ASTs distinguish unconditional selection from literal
comparison. Marker spans are retained, not equated with enclosing spans. -/
set_option autoImplicit false
namespace Tests.FrontendWildcardMatchBoundary
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment
open RecursiveLocalComputationEvaluatesWithCost

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"WildcardBoundary",by decide⟩],by decide⟩⟩,106⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-wildcard-boundary.sol"⟩,0,90⟩
private def x : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some x)⟩]⟩
private def wildcard (marker : Syntax.SourceSpan) : Syntax.MatchCase := ⟨span,⟨⟨span,.wildcard marker⟩,returned⟩⟩
private def zero := Core.Word.ofNatModulo 0
private def literal : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,returned⟩⟩
private def source (cases : List Syntax.MatchCase) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨x,[]⟩⟩ ⟨span,⟨cases,some returned⟩⟩⟩]⟩
private def inputs := LocalTypeInputs.empty.bindFresh owner "x" .word
private def environment (value : Core.Value) : Resolved.Environment := [(⟨owner,0⟩,value)]
private def direct : Core.Expr := .letE (.var 0) (.var 1)
private def guarded : Core.Expr :=
  .letE (.var 0) (.ifE (.binary .wordEq (.var 0) (.word zero)) (.var 1) (.var 1))
private theorem xElaborates : RecursiveLocalComputationElaborates
    inputs.names inputs.context x (.var 0) .word :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem literalMeaning : WordMatchPatternDenotes literal.value.pattern zero :=
  ⟨⟨span,.decimal "0"⟩,rfl,.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩
private theorem originalElaborates (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner inputs
      (source [wildcard marker,literal,wildcard marker]) direct .word := by
  simpa [source,direct,Core.Expr.weakenAt] using
    (ComputationReturnTreeElaborates.wordMatch (types := []) (owner := owner)
      (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (defaultBody := some returned) (defaultEntry := some (returned,.var 0))
      (entries := [(wildcard marker,none,Core.Expr.var 0),(literal,some zero,.var 0),(wildcard marker,none,.var 0)])
      xElaborates rfl
      (by intro entry member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl
          exact .wildcard rfl
          exact .literal literalMeaning
          exact .wildcard rfl) (.inl rfl)
      (by intro entry member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl <;> exact .expression xElaborates)
      rfl (by intro entry member; simp only [Option.toList_some,List.mem_singleton] at member
              subst entry; exact .expression xElaborates) rfl)
private theorem counted (marker : Syntax.SourceSpan) (rest : List Syntax.MatchCase)
    (value : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source (wildcard marker::rest)) value store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := inputs.names) (environment := environment value)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := x) (cases := wildcard marker::rest) (defaultBody := some returned) (selected := returned) (scrutineeValue := value)
    (.pure (.identifier .head .head)) (.wildcard (.wildcard rfl)) (.expression (.pure (.identifier .head .head)))
private theorem guardedElaborates (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner inputs
      (source [literal,wildcard marker]) guarded .word := by
  simpa [source,guarded,Core.Expr.weakenAt] using
    (ComputationReturnTreeElaborates.wordMatch (types := []) (owner := owner)
      (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (defaultBody := some returned) (defaultEntry := some (returned,.var 0))
      (entries := [(literal,some zero,Core.Expr.var 0),(wildcard marker,none,.var 0)])
      xElaborates rfl
      (by intro entry member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl; exact .literal literalMeaning; exact .wildcard rfl) (.inl rfl)
      (by intro entry member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> exact .expression xElaborates)
      rfl (by intro entry member; simp only [Option.toList_some,List.mem_singleton] at member
              subst entry; exact .expression xElaborates) rfl)
private theorem literalPath (value : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval direct [value],pending,store⟩ ⟨.ret value,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))

theorem original_markers_and_unreachable_rows_remain_statically_present (marker : Syntax.SourceSpan) :
    RecursiveComputationReturnTreeElaborates [] owner inputs
      (source [wildcard marker,literal,wildcard marker]) direct .word ∧
    RecursiveComputationReturnTreeHasType [] owner inputs
      (source [wildcard marker,literal,wildcard marker]) .word :=
  ⟨originalElaborates marker,
    (computationReturnTreeHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr
      ⟨direct,originalElaborates marker⟩⟩

theorem leading_wildcard_keeps_arbitrary_actual_values_and_continuations
    (marker : Syntax.SourceSpan) (value : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source [wildcard marker,literal,wildcard marker]) value store 4 ∧
    Core.Steps 4 ⟨.eval direct [value],pending,store⟩ ⟨.ret value,pending,store⟩ ∧
    Core.Steps 4 ⟨.eval direct (environment value).values,pending,store⟩ ⟨.ret value,pending,store⟩ := by
  refine ⟨counted marker _ value store,literalPath value store pending,?_⟩
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths
    toStepsWithContinuation (counted marker _ value store) (originalElaborates marker) rfl pending

theorem every_genuine_checkpoint_and_full_resumption (value : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (.initial direct [value] store)=.done value store ↔ 4≤fuel) ∧
    (∀ spent saved, Core.runStateful spent (.initial direct [value] store)=.outOfFuel saved →
      spent<4 ∧ Core.Steps (4-spent) saved (.final value store) ∧
      ∀ additional, Core.runStateful additional saved =
        Core.runStateful (spent+additional) (.initial direct [value] store)) := by
  have path := literalPath value store []
  refine ⟨path.runStateful_done_iff,?_⟩
  intro spent saved stopped
  have residual := path.residual_of_outOfFuel stopped
  exact ⟨residual.1,residual.2,Core.runStateful_resume stopped⟩

theorem no_later_original_pattern_or_body_is_dynamically_inspected
    (marker : Syntax.SourceSpan) (value : Core.Value) (store : Core.Store)
    (rest : List Syntax.MatchCase) (defaultBody : Syntax.Block) :
    WordMatchChooses value (wildcard marker::rest) (some defaultBody) returned 0 ∧
    (∀ selected tests, WordMatchChooses value (wildcard marker::rest) (some defaultBody) selected tests →
      selected=returned ∧ tests=0) ∧
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source (wildcard marker::rest)) value store 4 := by
  have choice : WordMatchChooses value (wildcard marker::rest) (some defaultBody) returned 0 := .wildcard (.wildcard rfl)
  exact ⟨choice,fun _ _ other => other.deterministic choice,counted marker rest value store⟩

theorem an_unselected_malformed_pattern_still_blocks_all_body_typing
    (marker : Syntax.SourceSpan) (value : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source [wildcard marker,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) value store 4 ∧
    ¬ RecursiveComputationReturnTreeHasType [] owner inputs
      (source [wildcard marker,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) .word := by
  refine ⟨counted marker _ value store,?_⟩
  intro typed
  cases typed with
  | wordMatch _ patterns _ _ _ _ =>
      obtain ⟨tag,meaning⟩ := patterns ⟨span,⟨⟨span,.error⟩,returned⟩⟩ (by simp)
      have checked := interpretWordMatchPattern?_iff.mpr meaning
      simp [interpretWordMatchPattern?] at checked

theorem a_literal_before_the_wildcard_still_requires_an_actual_Word
    (marker : Syntax.SourceSpan) (value : Core.Value) (rest : List Syntax.MatchCase)
    (defaultBody selected : Syntax.Block) (tests : Nat)
    (choice : WordMatchChooses value (literal::wildcard marker::rest) (some defaultBody) selected tests) :
    ∃ word, value=.word word := by
  cases choice with
  | wildcard meaning => cases (WordMatchPatternClassifies.literal literalMeaning).tag_unique meaning
  | hit _ => exact ⟨_,rfl⟩
  | miss _ _ _ => exact ⟨_,rfl⟩

theorem a_pending_frame_is_not_charged_to_the_original_body (value : Core.Value) (store : Core.Store) :
    Core.runStateful 4 ⟨.eval direct [value],[.pairApply (.bool true)],store⟩ =
      .outOfFuel ⟨.ret value,[.pairApply (.bool true)],store⟩ ∧
    Core.runStateful 5 ⟨.eval direct [value],[.pairApply (.bool true)],store⟩ =
      .done (.pair (.bool true) value) store := ⟨rfl,rfl⟩

theorem a_later_wildcard_does_not_rescue_an_earlier_comparison_fault
    (marker : Syntax.SourceSpan) (flag : Bool) (store : Core.Store) :
    RecursiveComputationReturnTreeElaborates [] owner inputs
      (source [literal,wildcard marker]) guarded .word ∧
    Core.runStateful 4 (.initial direct [.bool flag] store)=.done (.bool flag) store ∧
    Core.runStateful 8 (.initial guarded [.bool flag] store)=
      .fault (.invalidBinaryOperands .wordEq (.bool flag) (.word zero))
        ⟨.ret (.word zero),[.binaryApply .wordEq (.bool flag),
          .ifBranches (.var 1) (.var 1) [.bool flag,.bool flag]],store⟩ :=
  ⟨guardedElaborates marker,rfl,rfl⟩

end Tests.FrontendWildcardMatchBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendWildcardMatchCountProperties
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
end

section
-- leanmerge: from Solcore.Test.FrontendParsedRawLookup
/-! Composed lookup agrees on every spelling, independently of IDs and layouts.
Original parsed blocks have separate value/cost certificates on both sides. -/
set_option autoImplicit false
namespace Tests
open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do throw (IO.userError label)
private def owner (index : Nat) : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"RawLookup", by decide⟩], by decide⟩⟩, index⟩
private def id (o i : Nat) : Resolved.LocalId := ⟨owner o, i⟩
private def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def w (n : Nat) : Core.Value := .word (word n)
private def stores : List Core.Store := [[], [.cellRef .word 40, .bool true, w 91]]
private def types : TypeNameTable := [(["Word"], .word), (["Bool"], .bool)]
private def leftTable : LocalNameTable := [("c", id 17 2), ("d", id 71 999), ("r", id 17 5), ("l", id 17 7)]
private def rightTable : LocalNameTable := [("ghost", id 3 77), ("l", id 3 2), ("c", id 3 1),
  ("l", id 71 80), ("r", id 3 4), ("d", id 71 0)]
private def leftEnv (l r : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 17 8, w 99), (id 17 5, r), (id 71 999, .bool d), (id 17 2, .bool c), (id 17 7, l), (id 17 7, .bool true)]
private def rightEnv (l r : Core.Value) (c d : Bool) : Resolved.Environment :=
  [(id 71 0, .bool d), (id 3 4, r), (id 3 1, .bool c), (id 3 2, l), (id 3 78, w 88), (id 3 2, .bool false), (id 71 117, .unit)]
private theorem sameLookup (l r : Core.Value) (c d : Bool) : ∀ name,
    (leftTable.lookup? name).bind (leftEnv l r c d).lookup? = (rightTable.lookup? name).bind (rightEnv l r c d).lookup? := by
  intro name
  by_cases hc : "c" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hd : "d" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hr : "r" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hl : "l" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  by_cases hg : "ghost" = name
  · subst name; simp [leftTable, rightTable, leftEnv, rightEnv, LocalNameTable.lookup?, Resolved.LocalScope.lookup?, id, owner]
  simp [leftTable, rightTable, LocalNameTable.lookup?, hc, hd, hr, hl, hg]
private def parsed (content : String) : IO Syntax.Block := do
  let file : Syntax.SourceFile := { id := ⟨.main, "raw-lookup.sol"⟩, content }
  let .ok lexed ← pure (Syntax.Lexer.lex file) | throw (IO.userError "lexer invariant")
  let .ok body next := Syntax.Parser.block .allow (Syntax.Parser.State.initial file lexed)
    | throw (IO.userError s!"block did not parse: {content}")
  assertTrue (lexed.diagnostics.isEmpty && next.diagnostics.isEmpty && next.atEnd) "incomplete original block"
  assertTrue (decide (body.span.source = file.id ∧ body.span.startByte = 0 ∧ body.span.endByte = content.utf8ByteSize))
    "original block span changed"
  return body
private structure Expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (source : Syntax.Expr) where
  value : Core.Value
  cost : Nat
  costed : LocalExpressionEvaluatesWithCost table env store source value store cost
private def reference (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier name⟩ =>
      match named : table.lookup? name.value with
      | none => throw (IO.userError "certificate name missing")
      | some id =>
          match found : env.lookup? id with
          | none => throw (IO.userError "certificate actual value missing")
          | some value => return ⟨value, 1, by
              rw [sourceAt]
              exact .identifier (LocalNameTable.lookup?_iff.mp named) (Resolved.LocalScope.lookup?_iff.mp found)⟩
  | _ => throw (IO.userError "certificate expected original reference")
private def expression (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (source : Syntax.Expr) : IO (Expression table env store source) := do
  match sourceAt : source with
  | ⟨_, .identifier _⟩ => reference table env store source
  | ⟨_, .unary ⟨_, .bitNot⟩ operand⟩ =>
      let child ← reference table env store operand
      match atValue : child.value with
      | .word value => return ⟨.word value.bitNot, child.cost + 2, by rw [sourceAt]; exact .bitNot (atValue ▸ child.costed)⟩
      | _ => throw (IO.userError "certificate expected Word")
  | ⟨_, .binary left ⟨_, .subtract⟩ right⟩ =>
      let first ← reference table env store left
      let second ← reference table env store right
      match atLeft : first.value, atRight : second.value with
      | .word l, .word r => return ⟨.word (l.sub r), first.cost + second.cost + 3, by
          rw [sourceAt]; exact .subtract (atLeft ▸ first.costed) (atRight ▸ second.costed)⟩
      | _, _ => throw (IO.userError "certificate subtraction expected Words")
  | _ => throw (IO.userError "expression outside independent certificate script")
private structure Certificate (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store) (body : Syntax.Block) where
  value : Core.Value
  cost : Nat
  costed : TypedLetReturnTreeEvaluatesWithCost currentOwner table env store body value store cost
private def certify (currentOwner : Resolved.DeclarationId) (table : LocalNameTable) (env : Resolved.Environment) (store : Core.Store)
    (body : Syntax.Block) (choices : List Bool) : IO (Certificate currentOwner table env store body) := do
  match atBody : body with
  | ⟨span, ⟨_, .letDecl name annotation (some initializer)⟩ :: rest⟩ =>
      let child ← expression table env store initializer
      let id := Resolved.freshLocalId currentOwner (table.map Prod.snd)
      let tail ← certify currentOwner ((name.value, id) :: table) ((id, child.value) :: env) store ⟨span, rest⟩ choices
      return ⟨tail.value, child.cost + tail.cost + 2, by
        rw [atBody]
        cases annotation with
        | none => exact .inferred child.costed tail.costed
        | some _ => exact .binding child.costed tail.costed⟩
  | ⟨_, [⟨_, .ifThen condition left (some right)⟩]⟩ =>
      let choice :: rest := choices | throw (IO.userError "independent branch script missing")
      let guard ← reference table env store condition
      if agrees : guard.value = .bool choice then
        match atChoice : choice with
        | true =>
            let child ← certify currentOwner table env store left rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifTrue (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
        | false =>
            let child ← certify currentOwner table env store right rest
            return ⟨child.value, guard.cost + child.cost + 2, by
              rw [atBody]
              exact .ifFalse (by simpa only [agrees, atChoice] using guard.costed) child.costed⟩
      else throw (IO.userError "independent branch script disagrees with actual guard")
  | ⟨_, [⟨_, .returnStmt none⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past bare return"
      return ⟨.unit, 1, by rw [atBody]; exact .single .bare⟩
  | ⟨_, [⟨_, .returnStmt (some operand)⟩]⟩ =>
      assertTrue choices.isEmpty "script continued past return"
      let child ← expression table env store operand
      return ⟨child.value, child.cost, by rw [atBody]; exact .single (.expression child.costed)⟩
  | _ => throw (IO.userError "body outside independent certificate script")
termination_by sizeOf body
private def raw (lo ro : Resolved.DeclarationId) (lt rt : LocalNameTable) (le re : Resolved.Environment)
    (agrees : ∀ name, (lt.lookup? name).bind le.lookup? = (rt.lookup? name).bind re.lookup?)
    (body : Syntax.Block) (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  have same := evaluateTypedLetReturnTreeWithCost?_congr_lookup lo ro lt rt le re agrees body
  have _ := same.symm
  assertTrue (decide (evaluateTypedLetReturnTreeWithCost? lo lt le body = expected ∧
    evaluateTypedLetReturnTreeWithCost? ro rt re body = expected)) "independent result/cost differed"
  match body.value with
  | [⟨_, .returnStmt (some expression)⟩] =>
      have sameExpression := evaluateLocalExpressionWithCost?_congr_lookup lt rt le re agrees expression
      have _ := sameExpression.symm
      assertTrue (decide (evaluateLocalExpressionWithCost? lt le expression = expected ∧
        evaluateLocalExpressionWithCost? rt re expression = expected)) "expression lookup law changed cost"
  | _ => pure ()
  for store in stores do
    match expected with
    | none =>
        match left : evaluateTypedLetReturnTreeWithCost? lo lt le body,
            right : evaluateTypedLetReturnTreeWithCost? ro rt re body with
        | none, none =>
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp left
            have _ := (evaluateTypedLetReturnTreeWithCost?_eq_none_iff store).mp right
            pure ()
        | _, _ => throw (IO.userError "genuine raw absence disappeared")
    | some (value, cost) =>
        let left ← certify lo lt le store body choices
        let right ← certify ro rt re store body choices
        assertTrue (decide (left.value = value ∧ right.value = value ∧ left.cost = cost ∧ right.cost = cost))
          "independent raw certificates disagreed"
        have _ := (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mp left.costed
        have _ := (typedLetReturnTreeEvaluatesWithCost_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mpr right.costed
        have _ := (typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mp left.costed.erase
        have _ := (typedLetReturnTreeEvaluates_congr_lookup_iff (leftOwner := lo) (rightOwner := ro) agrees).mpr right.costed.erase
        have _ : ¬ TypedLetReturnTreeEvaluatesWithCost ro rt re store body value (.unit :: store) cost := by
          intro impossible
          have lengths := congrArg List.length impossible.store_eq
          simp only [List.length_cons] at lengths
          omega
        pure ()
private def sample (content : String) (l r : Core.Value) (c d : Bool)
    (expected : Option (Core.Value × Nat)) (choices : List Bool := []) : IO Unit := do
  raw (owner 17) (owner 3) leftTable rightTable (leftEnv l r c d) (rightEnv l r c d)
    (sameLookup l r c d) (← parsed content) expected choices
private def spine (remaining level : Nat) : String :=
  match remaining with
  | 0 => "return " ++ (if level = 0 then "l" else s!"z{level - 1}") ++ ";"
  | count + 1 => "if(c){" ++ s!"let z{level}: Word=" ++
      (if level = 0 then "l" else s!"z{level - 1}") ++ ";" ++ spine count (level + 1) ++
      "}else{" ++ s!"let z{level}: Word=r;return z{level};" ++ "}"
private def checkedLeft : LocalInputs := ⟨[⟨"x", id 17 0, .word, w 9, .word⟩,
  ⟨"y", id 17 1, .word, w 2, .word⟩], by change [id 17 0, id 17 1].Nodup; decide⟩
private def checkedRight : LocalInputs := ⟨[⟨"y", id 3 0, .word, w 2, .word⟩,
  ⟨"x", id 3 10, .word, w 9, .word⟩, ⟨"x", id 3 20, .word, w 99, .word⟩], by
    change [id 3 0, id 3 10, id 3 20].Nodup; decide⟩
private def checked : IO Unit := do
  let body ← parsed "{let z: Word=x;return z;}"
  have same : ∀ name, (checkedLeft.names.lookup? name).bind checkedLeft.environment.lookup? =
      (checkedRight.names.lookup? name).bind checkedRight.environment.lookup? := by
    intro name
    by_cases hx : "x" = name
    · subst name; rfl
    by_cases hy : "y" = name
    · subst name; rfl
    simp [checkedLeft, checkedRight, LocalInputs.names, LocalInputs.environment, LocalNameTable.lookup?, hx, hy]
  raw (owner 17) (owner 3) checkedLeft.names checkedRight.names checkedLeft.environment checkedRight.environment same body (some (w 9, 4))
  for (actual, currentOwner, core) in [(checkedLeft, owner 17, Core.Expr.letE (.var 0) (.var 0)),
      (checkedRight, owner 3, Core.Expr.letE (.var 1) (.var 0))] do
    assertTrue (decide (actual.checkTypedLetReturnTree? types currentOwner body = some (core, .word))) "independent exact Core disappeared"
    match accepted : actual.checkTypedLetReturnTree? types currentOwner body,
        evaluated : evaluateTypedLetReturnTreeWithCost? currentOwner actual.toTypeInputs.names actual.environment body with
    | some _, some _ =>
        have aligned : actual.environment.ids = actual.toTypeInputs.context.ids := by
          simpa only [LocalInputs.toTypeInputs_context] using actual.sameIds
        for store in stores do
          have _ := evaluateTypedLetReturnTreeWithCost?_checked_toStepsWithContinuation (store := store) evaluated accepted aligned []
          for fuel in List.range 7 do
            assertTrue (decide (actual.runTypedLetReturnTree? types currentOwner fuel body store =
              some (.word, Core.runStateful fuel (.initial core actual.environment.values store)))) "own actual Core result changed"
          assertTrue (decide (actual.runTypedLetReturnTree? types currentOwner 2 body store =
            some (.word, .outOfFuel ⟨.ret (w 9), [.letBody (.var 0) actual.environment.values], store⟩))) "independent captured environment changed"
    | _, _ => throw (IO.userError "separate checked premises missing")
  for store in stores do
    assertTrue (decide (checkedLeft.runTypedLetReturnTree? types (owner 17) 2 body store ≠
      checkedRight.runTypedLetReturnTree? types (owner 3) 2 body store)) "equal raw results were mistaken for equal checkpoints"

def frontendParsedRawLookupTests : IO Unit := do
  sample "{let z=l;return z;}" (w 9) (w 2) true false (some (w 9, 4))
  for depth in [0, 1, 2, 5, 12] do
    for c in [false, true] do
      sample ("{" ++ spine depth 0 ++ "}") (w 9) (w 2) c false
        (some (w (if depth = 0 || c then 9 else 2), if depth = 0 then 1 else if c then 6 * depth + 1 else 7))
        (if depth = 0 then [] else if c then List.replicate depth true else [false])
  for (l, r) in [(9, 2), (2, 9), (0, Core.wordModulus - 1), (2 ^ 255, 7)] do
    for c in [false, true] do
      for d in [false, true] do
        sample "{if(c){let z: Word=l - r;if(d){let q: Word=z;return ~q;}else{let q: Word=r - z;return q;}}else{let z: Word=r - l;return r;}}"
          (w l) (w r) c d (some (if c then if d then w (Core.wordModulus - 1 - (l + Core.wordModulus - r) % Core.wordModulus)
            else w (r + Core.wordModulus - (l + Core.wordModulus - r) % Core.wordModulus) else w r,
            if c then if d then 19 else 21 else 11)) (if c then [true, d] else [false])
  for (content, value, cost, choices) in [("{return;}", Core.Value.unit, 1, []), ("{return l - r;}", w 7, 5, []),
      ("{return ~l;}", w (Core.wordModulus - 10), 3, []), ("{let unused: Word=l - r;return r;}", w 2, 8, []),
      ("{let z: Unknown=l;return z;}", w 9, 4, []), ("{let z: Bool=l;return z;}", w 9, 4, []), ("{let l: Word=l - r;return l;}", w 7, 8, []),
      ("{if(c){return l;}else{let z: Unknown=ghost;return z;}}", w 9, 4, [true])] do
    sample content (w 9) (w 2) true false (some (value, cost)) choices
  for content in ["{}", "{return ghost;}", "{return missing;}", "{let z: Word;return l;}",
      "{let z: Word=l;}", "{return l;return r;}", "{if(c){return l;}}", "{if(c){return l;}else{return r;}return l;}",
      "{let unused: Word=ghost;return r;}", "{let unused: Word=~c;return r;}", "{return f(l);}",
      "{if(l){return l;}else{return r;}}"] do sample content (w 9) (w 2) true false none
  for value in [Core.Value.unit, .cellRef .word 999, .closure .word .word (.var 1) [w 7],
      .closure .word .bool (.var 80) [], .constructed ⟨⟨91⟩, 4⟩ (.pair .unit (w 7))] do
    sample "{let z: Word=l;if(c){return z;}else{return r;}}" value (w 2) true false (some (value, 7)) [true]
  let static : LocalTypeInputs := ⟨[⟨"c", id 17 2, .bool⟩, ⟨"d", id 71 999, .bool⟩,
    ⟨"r", id 17 5, .word⟩, ⟨"l", id 17 7, .word⟩], by
      change [id 17 2, id 71 999, id 17 5, id 17 7].Nodup; decide⟩
  assertTrue (decide (static.names = leftTable)) "whole-check contrast replaced raw names"
  for content in ["{let z: Unknown=l;return z;}", "{let z: Bool=l;return z;}", "{let l: Word=l - r;return l;}",
      "{if(c){return l;}else{let z: Unknown=ghost;return z;}}"] do
    assertTrue ((elaborateTypedLetReturnTree? types (owner 17) static (← parsed content)).isNone)
      "raw selected success was mistaken for whole annotation/freshness/branch acceptance"
  assertTrue (decide (leftTable.lookup? "ghost" = none ∧ rightTable.lookup? "ghost" = some (id 3 77) ∧
    Resolved.freshLocalId (owner 17) (leftTable.map Prod.snd) = id 17 8 ∧
    Resolved.freshLocalId (owner 3) (rightTable.map Prod.snd) = id 3 78 ∧
    (leftEnv (w 9) (w 2) true false).lookup? (id 17 8) = some (w 99) ∧
    (rightEnv (w 9) (w 2) true false).lookup? (id 3 78) = some (w 88))) "absence, unbound names and independent fresh collisions changed"
  checked
  let source ← parsed "{let z: Unknown=x;return z;}"
  let indexShift := fun binder : Resolved.LocalId => { binder with binderIndex := binder.binderIndex + 10 }
  let table : LocalNameTable := [("x", id 71 0)]
  let env : Resolved.Environment := [(id 71 0, w 9)]
  let mappedTable := LocalNameTable.mapIds indexShift table
  let mappedEnv := Resolved.LocalScope.mapIds indexShift env
  have same : ∀ name, (table.lookup? name).bind env.lookup? = (mappedTable.lookup? name).bind mappedEnv.lookup? := by
    intro name
    by_cases hx : "x" = name
    · subst name; rfl
    simp [table, mappedTable, LocalNameTable.mapIds, LocalNameTable.lookup?, hx]
  raw (owner 17) (owner 17) table mappedTable env mappedEnv same source (some (w 9, 4))
  assertTrue (decide (Resolved.freshLocalId (owner 17) (mappedTable.map Prod.snd) ≠
    indexShift (Resolved.freshLocalId (owner 17) (table.map Prod.snd)))) "index-changing map unexpectedly commuted with allocation"
  let changed : Resolved.Environment := (id 71 0, w 2) :: env
  assertTrue (decide ((table.lookup? "x").bind env.lookup? ≠ (table.lookup? "x").bind changed.lookup? ∧
    evaluateTypedLetReturnTreeWithCost? (owner 17) table changed source = some (w 2, 4))) "changed visible first match had no witness"

end Tests
end

section
-- leanmerge: from Solcore.Test.FrontendWordMatchBoundaryProperties
/-! Symbolic original ASTs isolate the no-comparison boundary. The spans below
are retained literally, not asserted to describe a parsed source file. -/
set_option autoImplicit false
namespace Tests.FrontendWordMatchBoundary
open Solcore Solcore.Frontend
open RecursiveLocalComputationElaborates RecursiveLocalComputationFragment
open RecursiveLocalComputationEvaluatesWithCost

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"MatchBoundary",by decide⟩],by decide⟩⟩,94⟩
private def span : Syntax.SourceSpan := ⟨⟨.main,"symbolic-match-boundary.sol"⟩,0,9⟩
private def x : Syntax.Expr := ⟨span,.identifier ⟨span,"x"⟩⟩
private def returned : Syntax.Block := ⟨span,[⟨span,.returnStmt (some x)⟩]⟩
private def zero := Core.Word.ofNatModulo 0
private def arm : Syntax.MatchCase := ⟨span,⟨⟨span,.literal ⟨span,.decimal "0"⟩⟩,returned⟩⟩
private def source (cases : List Syntax.MatchCase) : Syntax.Block :=
  ⟨span,[⟨span,.matchWith ⟨span,⟨x,[]⟩⟩ ⟨span,⟨cases,some returned⟩⟩⟩]⟩
private def inputs := LocalTypeInputs.empty.bindFresh owner "x" .word
private def environment (value : Core.Value) : Resolved.Environment := [(⟨owner,0⟩,value)]
private def emptyCore : Core.Expr := .letE (.var 0) (.var 1)
private def guardedCore : Core.Expr :=
  .letE (.var 0) (.ifE (.binary .wordEq (.var 0) (.word zero)) (.var 1) (.var 1))
private theorem xElaborates : RecursiveLocalComputationElaborates
    inputs.names inputs.context x (.var 0) .word :=
  .pure (.identifier .head) (.var .head) (.var .head)
private theorem zeroMeaning : WordMatchPatternDenotes arm.value.pattern zero :=
  ⟨⟨span,.decimal "0"⟩,rfl,.decimal (by decide) (.cons (.decimal (digit := 0) (by decide) rfl) .nil)⟩
private theorem emptyElaborates :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source []) emptyCore .word := by
  simpa [source,emptyCore,Core.Expr.weakenAt] using
    (ComputationReturnTreeElaborates.wordMatch (types := []) (owner := owner)
      (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (defaultBody := some returned) (defaultEntry := some (returned,.var 0))
      (entries := []) xElaborates rfl (by simp) (.inl rfl) (by simp) rfl
      (by intro entry member; simp only [Option.toList_some,List.mem_singleton] at member
          subst entry; exact .expression xElaborates) rfl)
private theorem guardedElaborates :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source [arm]) guardedCore .word := by
  simpa [source,guardedCore,Core.Expr.weakenAt] using
    (ComputationReturnTreeElaborates.wordMatch (types := []) (owner := owner)
      (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (defaultBody := some returned) (defaultEntry := some (returned,.var 0))
      (entries := [(arm,some zero,Core.Expr.var 0)]) xElaborates rfl
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .literal zeroMeaning) (.inl rfl)
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression xElaborates)
      rfl (by intro entry member; simp only [Option.toList_some,List.mem_singleton] at member
              subst entry; exact .expression xElaborates) rfl)
private theorem counted (value : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source []) value store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := inputs.names) (environment := environment value)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := x) (defaultBody := some returned) (selected := returned) (scrutineeValue := value)
    (.pure (.identifier .head .head)) .fallback (.expression (.pure (.identifier .head .head)))
private theorem literalPath (value : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval emptyCore [value],pending,store⟩ ⟨.ret value,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))

theorem both_original_sources_are_statically_Word :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source []) emptyCore .word ∧
    RecursiveComputationReturnTreeElaborates [] owner inputs (source [arm]) guardedCore .word :=
  ⟨emptyElaborates,guardedElaborates⟩

theorem default_only_keeps_every_actual_value_store_and_pending_continuation
    (value : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source []) value store 4 ∧
    Core.Steps 4 ⟨.eval emptyCore [value],pending,store⟩ ⟨.ret value,pending,store⟩ ∧
    Core.Steps 4 ⟨.eval emptyCore (environment value).values,pending,store⟩ ⟨.ret value,pending,store⟩ := by
  refine ⟨counted value store,literalPath value store pending,?_⟩
  exact ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation
    (F := RecursiveLocalComputationFragment) core_fragment weakenAt insertion_paths
    toStepsWithContinuation (counted value store) emptyElaborates rfl pending

theorem every_default_only_checkpoint_retains_the_exact_remaining_path
    (value : Core.Value) (store : Core.Store) (fuel : Nat) :
    (Core.runStateful fuel (.initial emptyCore [value] store) = .done value store ↔ 4 ≤ fuel) ∧
    (∀ spent saved, Core.runStateful spent (.initial emptyCore [value] store) = .outOfFuel saved →
      spent < 4 ∧ Core.Steps (4-spent) saved (.final value store) ∧
      ∀ additional, Core.runStateful additional saved =
        Core.runStateful (spent+additional) (.initial emptyCore [value] store)) := by
  have path := literalPath value store []
  refine ⟨path.runStateful_done_iff,?_⟩
  intro spent saved exhausted
  have residual := path.residual_of_outOfFuel exhausted
  exact ⟨residual.1,residual.2,Core.runStateful_resume exhausted⟩

private def beforeFault (flag : Bool) (store : Core.Store) : Core.State :=
  ⟨.eval (.word zero) [.bool flag,.bool flag],
    [.binaryApply .wordEq (.bool flag),.ifBranches (.var 1) (.var 1) [.bool flag,.bool flag]],store⟩
private def faultState (flag : Bool) (store : Core.Store) : Core.State :=
  ⟨.ret (.word zero),
    [.binaryApply .wordEq (.bool flag),.ifBranches (.var 1) (.var 1) [.bool flag,.bool flag]],store⟩

theorem a_nonempty_case_list_faults_instead_of_treating_Bool_as_a_miss
    (flag : Bool) (store : Core.Store) :
    Core.runStateful 4 (.initial emptyCore [.bool flag] store) = .done (.bool flag) store ∧
    Core.runStateful 7 (.initial guardedCore [.bool flag] store) = .outOfFuel (beforeFault flag store) ∧
    Core.runStateful 8 (.initial guardedCore [.bool flag] store) =
      .fault (.invalidBinaryOperands .wordEq (.bool flag) (.word zero)) (faultState flag store) ∧
    Core.runStateful 1 (beforeFault flag store) =
      .fault (.invalidBinaryOperands .wordEq (.bool flag) (.word zero)) (faultState flag store) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem a_Bool_cannot_choose_even_the_default_of_nonempty_literal_cases
    (flag : Bool) (rest : List Syntax.MatchCase) (fallback selected : Syntax.Block) (tests : Nat) :
    ¬ WordMatchChooses (.bool flag) (arm::rest) (some fallback) selected tests := by
  intro choice
  cases choice with
  | wildcard meaning => cases (WordMatchPatternClassifies.literal zeroMeaning).tag_unique meaning

theorem malformed_unvisited_pattern_and_body_do_not_change_raw_first_hit
    (badPattern : Syntax.Pattern) (badBody fallback : Syntax.Block) :
    WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] (some fallback) returned 1 ∧
    (∀ selected tests,
      WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] (some fallback) selected tests →
      selected = returned ∧ tests = 1) := by
  have chosen : WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] (some fallback) returned 1 :=
    .hit (.literal zeroMeaning)
  exact ⟨chosen,fun _ _ other => other.deterministic chosen⟩

theorem a_malformed_unselected_case_still_blocks_static_typing (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment (.word zero))
      store (source [arm,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) (.word zero) store 11 ∧
    ¬ RecursiveComputationReturnTreeHasType [] owner inputs
      (source [arm,⟨span,⟨⟨span,.error⟩,returned⟩⟩]) .word := by
  constructor
  · exact ComputationReturnTreeEvaluatesWithCost.wordMatch
      (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
      (owner := owner) (table := inputs.names) (environment := environment (.word zero))
      (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (scrutinee := x) (defaultBody := some returned) (selected := returned) (scrutineeValue := .word zero)
      (.pure (.identifier .head .head)) (.hit (.literal zeroMeaning)) (.expression (.pure (.identifier .head .head)))
  · intro typing
    cases typing with
    | wordMatch _ patterns _ _ _ _ =>
        obtain ⟨tag,meaning⟩ := patterns ⟨span,⟨⟨span,.error⟩,returned⟩⟩ (by simp)
        have checked := interpretWordMatchPattern?_iff.mpr meaning
        simp [interpretWordMatchPattern?] at checked

end Tests.FrontendWordMatchBoundary
end

section
-- leanmerge: from Solcore.Test.FrontendWordMatchCountProperties
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
end
