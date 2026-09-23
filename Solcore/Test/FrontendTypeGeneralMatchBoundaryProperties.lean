import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Core.FuelResumptionProperties

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
