import Solcore.Frontend.ComputationReturnTreeProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationTypingProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

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
    (xElaborates type) rfl ?_ ?_ rfl (by simp) ?_
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact ⟨marker,rfl⟩
    · exact literalMeaning
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
    (.pure (.identifier .head .head)) (.wildcard rfl)
    (.expression (.pure (.identifier (id := id 1) (LocalNameTable.lookup?_iff.mp rfl)
      (Resolved.LocalScope.lookup?_iff.mp rfl))))
private theorem literalPath (scrutinee result : Core.Value) (store : Core.Store) (pending : List Core.Frame) :
    Core.Steps 4 ⟨.eval core [scrutinee,result],pending,store⟩ ⟨.ret result,pending,store⟩ :=
  .cons .enterLet (.cons (.var rfl) (.cons .bindLet (.cons (.var rfl) .refl)))
private theorem noLiteralCoverage (type resultType : Core.Ty) :
    ¬ RecursiveComputationReturnTreeHasType [] owner (inputs type) (source [literal]) resultType := by
  intro typed
  cases typed with
  | wordMatch _ _ covered _ _ =>
      rcases covered with present | ⟨arm,member,marker,shape⟩
      · cases present
      · simp only [List.mem_singleton] at member
        subst arm
        cases shape

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
    | wordMatch _ _ covered _ _ =>
        rcases covered with present | ⟨arm,member,_,_⟩
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
      (.pure (.identifier .head .head)) (.hit literalMeaning)
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
  | wordMatch _ patterns _ _ _ =>
      obtain ⟨tag,meaning⟩ := patterns ⟨span,⟨⟨span,.error⟩,returned⟩⟩ (by simp)
      cases tag with
      | none => obtain ⟨_,shape⟩ := meaning; cases shape
      | some word => obtain ⟨_,shape,_⟩ := meaning; cases shape

theorem a_pending_frame_is_outside_the_original_four_transition_body
    (scrutinee result : Core.Value) (store : Core.Store) :
    Core.runStateful 4 ⟨.eval core [scrutinee,result],[.pairApply (.bool true)],store⟩ =
      .outOfFuel ⟨.ret result,[.pairApply (.bool true)],store⟩ ∧
    Core.runStateful 5 ⟨.eval core [scrutinee,result],[.pairApply (.bool true)],store⟩ =
      .done (.pair (.bool true) result) store := ⟨rfl,rfl⟩

end Tests.FrontendOptionalMatchBoundary
