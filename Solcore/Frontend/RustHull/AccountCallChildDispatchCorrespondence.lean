import Solcore.Frontend.RustHull.AccountCallChildRunCorrespondence

/-! Dispatch commits successful child effects and restores every captured shared
cell after revert or fault. The same frame rule retains the caller's local cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem run_children_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state store) (ready : valid store)
    (computed : AccountCallSemantics.Run children .ordinary source request state result finalState) :
    ∃ target final, Core.Evaluates environment store (dispatchRun shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final := by
  cases computed with
  | precompile executed =>
    obtain ⟨target, final, evaluated, responded, retained⟩ := precompiledPreserved executed [] store
    refine ⟨target, final, ?_, responded, related.retained retained, .ofRetains retained⟩
    exact accountRun_precompile_evaluates ((argument.part (index := 0) rfl).part (index := 0) rfl)
      executed.precompiled (by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using evaluated)
  | empty ordinary absent complete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .returned _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, complete, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | unavailable ordinary absent incomplete =>
    obtain ⟨final, evaluated, retained⟩ := accountRun_absent references
      ((argument.part (index := 0) rfl).part (index := 0) rfl) related.shared ordinary absent
      (precompiled := precompiled) (child := fun record => runFrame record (childRequest extended))
    refine ⟨_, final, ?_, .language _, related.retained retained, .ofRetains retained⟩
    simpa only [emptyRunResult, incomplete, Bool.false_eq_true, ↓reduceIte, dispatchRun, requestValues, List.length_cons, List.length_nil] using evaluated
  | child computed =>
    simpa only [List.nil_append, List.length_nil, Nat.add_zero] using
      childrenPreserved computed [] references argument related ready (precompiled := precompiled)

def dispatchAfter (before : AccountCallSemantics.Shared)
    (result : Semantics.Result AccountCallSemantics.Response) (after : AccountCallSemantics.Shared) :
    AccountCallSemantics.Shared :=
  match result with
  | .value response => if response.success then after else before
  | .fault _ => before

def dispatchWith (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended precompiled : Code) : Code :=
  let request := part 0 3 extended
  let mode := part 1 3 extended
  let source := part 2 3 extended
  AccountRuntime.checkpoint shared fun restore =>
  bindResult Calls.responseType (lookup (load (AccountRuntime.reference shared "balances")) source) fun sourceBalance =>
  choose (choose (binary .wordEq mode (number 2)) (CodeBuilder.boolean false)
    (binary .wordGt (part 2 8 request) sourceBalance))
    (AccountRuntime.callResult (CodeBuilder.boolean false) empty (number 0)) <|
  bindResult Calls.responseType
    (choose (binary .wordEq mode (number 0))
      (AccountRuntime.transfer shared source (part 0 8 request) (part 2 8 request)) (success unit)) fun _ =>
  fun depth => .caseE (dispatchRun shared runFrame extended precompiled depth)
    ((bind restore fun _ => failure Calls.responseType (fun here => .var (here - depth - 1))) (depth + 1))
    ((let response : Code := fun here => .var (here - depth - 1)
      choose (part 0 3 response) (success response)
        (bind restore fun _ => success response)) (depth + 1))

theorem dispatch_transferred_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state attempted : AccountCallSemantics.Shared} {balances : StorageSemantics.Words}
    {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (funds : ¬ request.value > StorageSemantics.readWord source state.balances)
    (moved : AccountCallSemantics.transfer source request.target request.value state.balances = .ok balances)
    (computed : AccountCallSemantics.Run children .ordinary source request {state with balances := balances} result attempted) :
    ∃ target final, Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations (dispatchAfter state result attempted) final ∧
      SharedFrame locations initial final := by
  obtain ⟨accounts, worldSame, links, worldRead⟩ := related.linked
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  obtain ⟨first, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.shared.balances)
    ((innerArgument.part (index := 2) rfl).evaluates initial)
  let sourceBalance := StorageSemantics.readWord source state.balances
  let extra := .word sourceBalance :: saved
  have afterArgument := argument.prepend extra
  have requestCode := afterArgument.part (index := 0) rfl
  obtain ⟨transferred, transferEvaluated, balanceFinal, transferFrame⟩ := transfer_preserves (references.balances.prepend extra)
    (afterArgument.part (index := 2) rfl) (requestCode.part (index := 0) rfl) (requestCode.part (index := 2) rfl)
    (retained_read retained related.shared.balances)
  rw [moved] at transferEvaluated balanceFinal
  have combined := (BalanceFrame.ofRetains retained).trans transferFrame
  have transferredRelated := related.balances_updated combined balanceFinal
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  obtain ⟨output, afterRun, runEvaluated, resultRelated, afterRelated, runFrameProof⟩ :=
    run_children_preserves (childrenPreserved.prepend runExtra) (precompiledPreserved.prepend runExtra)
      (references.prepend runExtra) (argument.prepend runExtra) transferredRelated
      (stable (.ofBalance combined) ready) computed
  have throughRun : SharedFrame locations initial afterRun := (SharedFrame.ofBalance combined).trans runFrameProof
  have enter {target : Core.Value} {final : Core.Store}
      (continued : Core.Evaluates runEnv transferred
        (.caseE (dispatchRun shared runFrame extended precompiled (depth + 6))
          ((bind (checkpointRestore shared depth) fun _ => failure Calls.responseType (fun here => .var (here - (depth + 6) - 1))) (depth + 7))
          ((let response : Code := fun here => .var (here - (depth + 6) - 1)
            choose (part 0 3 response) (success response)
              (bind (checkpointRestore shared depth) fun _ => success response)) (depth + 7))) target final) :
      Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final := by
    apply checkpoint_evaluates references worldRead related.shared.logs related.shared.logSize related.shared.balances
    apply LanguageResult.bind_success Calls.responseType looked
    apply Core.Evaluates.ifFalse
    · apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
      exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
        ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
        (by simp [BinaryOp.apply, sourceBalance, funds])
    apply LanguageResult.bind_success Calls.responseType
      (.ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) transferEvaluated)
    exact continued
  have restoreBound : ∀ location ∈ locations.mutable, location < afterRun.length :=
    fun location member => Nat.lt_of_lt_of_le (related.shared.mutable_bounded location member) throughRun.length_le
  let restored := checkpointStore locations (StorageCorrespondence.world accounts) (WordMapping.encode state.logs)
    (.word state.logSize) (WordMapping.encode state.balances) afterRun
  have restoredRelated : LinkedSharedStateRel anchors locations state restored :=
    checkpointStore_restores related.shared worldSame links throughRun
  have restoredFrame : SharedFrame locations initial restored := throughRun.trans (checkpointStore_frame ..)
  cases resultRelated with
  | returned response =>
    have responseCode := CodeValue.bound (depth + 6) runEnv (responseValue response)
    cases success : response.success with
    | true =>
      refine ⟨_, afterRun, enter (.caseRight runEvaluated ?_), .returned _, ?_, throughRun⟩
      · exact .ifTrue (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
          (.inRight (responseCode.evaluates afterRun))
      · simpa only [dispatchAfter, success, ↓reduceIte] using afterRelated
    | false =>
      refine ⟨_, restored, enter (.caseRight runEvaluated ?_), .returned _, ?_, restoredFrame⟩
      · apply Core.Evaluates.ifFalse (by simpa only [success, responseValues, List.length_cons, List.length_nil, Nat.add_assoc] using (responseCode.part (index := 0) rfl).evaluates afterRun)
        apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
          [responseValue response, .unit, .word sourceBalance] restoreBound)
        exact .inRight ((responseCode.prepend [.unit]).evaluates restored)
      · simpa only [dispatchAfter, success, Bool.false_eq_true, ↓reduceIte] using restoredRelated
  | language reason =>
    refine ⟨_, restored, enter (.caseLeft runEvaluated ?_), .language _, restoredRelated, restoredFrame⟩
    apply Core.Evaluates.letE (checkpointRestore_all_evaluates _ _ _ _ references
      [.word reason, .unit, .word sourceBalance] restoreBound)
    exact .inLeft (((CodeValue.bound (depth + 6) runEnv (.word reason)).prepend [.unit]).evaluates restored)

/-- The actual dispatcher is the composition above with the actual precompile
call, restated by `PrecompileCorrespondence.precompileCode`. -/
theorem dispatch_precompile_eq (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (extended : Code) :
    AccountRuntime.dispatch shared runFrame extended =
      dispatchWith shared runFrame extended (PrecompileCorrespondence.precompileCode (part 0 3 extended)) := rfl

/-- Source dispatch selects the real funds, transfer and child branches. This
internal composition theorem is instantiated with compiled child execution. -/
theorem dispatch_children_preserves {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation anchors locations shared runFrame children valid depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (computed : AccountCallSemantics.Dispatch children .ordinary source request state result finalState) :
    ∃ target final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  have requestCode : CodeValue depth environment (part 0 3 extended) (requestValue request) :=
    argument.part (index := 0) rfl
  cases computed with
  | insufficient checked shortfall =>
    obtain ⟨final, evaluated, retained⟩ := dispatch_insufficient references argument related.shared shortfall
    exact ⟨_, final, evaluated, .returned _, related.retained retained, .ofRetains retained⟩
  | transferFault funds failed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨final, evaluated, finalRelated, frame⟩ :=
      dispatch_transferFault references argument related.shared funds' (transferFor_error failed)
    exact ⟨_, final, evaluated, .language _, related.balances_updated frame finalRelated.balances, .ofBalance frame⟩
  | succeeded funds moved executed success =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, success, ↓reduceIte] using
      dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
        stable references argument related ready funds' transferOk executed
  | refused funds moved executed failure =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    simpa only [dispatchAfter, failure, Bool.false_eq_true, ↓reduceIte] using
      dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
        stable references argument related ready funds' transferOk executed
  | fault funds moved executed =>
    have funds' : ¬ request.value > StorageSemantics.readWord source state.balances := by simpa using funds
    obtain ⟨balances, transferOk, rfl⟩ := transferFor_ok moved
    rw [dispatch_precompile_eq]
    exact dispatch_transferred_preserves childrenPreserved (precompileCode_preservation requestCode)
      stable references argument related ready funds' transferOk executed

end Solcore.Frontend.RustHull.AccountCallCorrespondence
