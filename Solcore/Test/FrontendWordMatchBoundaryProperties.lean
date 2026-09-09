import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputationProperties
import Solcore.Frontend.RecursiveLocalComputationExecutionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionProperties
import Solcore.Frontend.RecursiveLocalComputationFragmentInsertionPaths
import Solcore.Core.FuelResumptionProperties

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
      (defaultBody := returned) (entries := []) xElaborates rfl (by simp) (by simp)
      (.expression xElaborates))
private theorem guardedElaborates :
    RecursiveComputationReturnTreeElaborates [] owner inputs (source [arm]) guardedCore .word := by
  simpa [source,guardedCore,Core.Expr.weakenAt] using
    (ComputationReturnTreeElaborates.wordMatch (types := []) (owner := owner)
      (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
      (defaultBody := returned) (entries := [(arm,zero,Core.Expr.var 0)]) xElaborates rfl
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact zeroMeaning)
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact .expression xElaborates)
      (.expression xElaborates))
private theorem counted (value : Core.Value) (store : Core.Store) :
    RecursiveComputationReturnTreeEvaluatesWithCost owner inputs.names (environment value)
      store (source []) value store 4 := by
  exact ComputationReturnTreeEvaluatesWithCost.wordMatch
    (ChildCost := RecursiveLocalComputationEvaluatesWithCost) (scrutineeCost := 1) (branchCost := 1)
    (owner := owner) (table := inputs.names) (environment := environment value)
    (initialStore := store) (blockSpan := span) (matchSpan := span) (scrutineeSpan := span) (armsSpan := span)
    (scrutinee := x) (defaultBody := returned) (selected := returned) (scrutineeValue := value)
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
    ¬ WordMatchChooses (.bool flag) (arm::rest) fallback selected tests := by
  intro choice
  cases choice

theorem malformed_unvisited_pattern_and_body_do_not_change_raw_first_hit
    (badPattern : Syntax.Pattern) (badBody fallback : Syntax.Block) :
    WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] fallback returned 1 ∧
    (∀ selected tests,
      WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] fallback selected tests →
      selected = returned ∧ tests = 1) := by
  have chosen : WordMatchChooses (.word zero) [arm,⟨span,⟨badPattern,badBody⟩⟩] fallback returned 1 :=
    .hit zeroMeaning
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
      (scrutinee := x) (defaultBody := returned) (selected := returned) (scrutineeValue := .word zero)
      (.pure (.identifier .head .head)) (.hit zeroMeaning) (.expression (.pure (.identifier .head .head)))
  · intro typing
    cases typing with
    | wordMatch _ patterns _ _ =>
        obtain ⟨word,literal,shape,_⟩ := patterns ⟨span,⟨⟨span,.error⟩,returned⟩⟩ (by simp)
        cases shape

end Tests.FrontendWordMatchBoundary
