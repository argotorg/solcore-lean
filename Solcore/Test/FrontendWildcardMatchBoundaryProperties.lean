import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

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
          exact .wildcard rfl)
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
          rcases member with rfl | rfl; exact .literal literalMeaning; exact .wildcard rfl)
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
  | wordMatch _ patterns _ _ _ =>
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
