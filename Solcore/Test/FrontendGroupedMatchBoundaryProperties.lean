import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

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
