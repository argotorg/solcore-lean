import Solcore.Frontend.RustHull.AccountCallModeRunCorrespondence

/-! CALLCODE and DELEGATECALL use the actual checkpoint and funds branch but
perform no transfer. All modes commit or roll back the same four shared cells. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation run_children_preserves dispatch_insufficient

theorem dispatch_insufficient {mode : AccountCallSemantics.Mode} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {extended : Code}
    {locations : SharedLocations} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state : AccountCallSemantics.Shared}
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : SharedStateRel locations state initial)
    (checked : mode ≠ .delegateCall)
    (shortfall : request.value > StorageSemantics.readWord source state.balances) :
    ∃ final, Core.Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth)
      (.inRight .word (responseValue (AccountCallSemantics.emptyResponse false))) final ∧
      StoreRetains initial final := by
  obtain ⟨accounts, worldSame, worldRead⟩ := related.world
  let saved : Core.Environment := [WordMapping.encode state.balances, .word state.logSize,
    WordMapping.encode state.logs, StorageCorrespondence.world accounts]
  have innerReferences := references.prepend saved
  have innerArgument := argument.prepend saved
  have sourceCode : CodeValue (depth + 4) (saved ++ environment) (part 2 3 extended) (.word source) :=
    innerArgument.part (index := 2) rfl
  obtain ⟨final, looked, retained⟩ := lookup_preserves
    (.loadCell (innerReferences.balances.evaluates initial) related.balances) (sourceCode.evaluates initial)
  refine ⟨final, ?_, retained⟩
  apply checkpoint_evaluates references worldRead related.logs related.logSize related.balances
  apply LanguageResult.bind_success Calls.responseType looked
  have afterArgument := innerArgument.prepend [.word (StorageSemantics.readWord source state.balances)]
  have modeCode := afterArgument.part (index := 1) rfl
  have requestCode := afterArgument.part (index := 0) rfl
  have valueCode := requestCode.part (index := 2) rfl
  apply Core.Evaluates.ifTrue
  · apply Core.Evaluates.ifFalse (.binary (modeCode.evaluates final) .word (by
      cases mode with
      | ordinary => rfl
      | callCode => rfl
      | delegateCall => exact False.elim (checked rfl)))
    exact .binary (valueCode.evaluates final)
      ((CodeValue.bound (depth + 4) (saved ++ environment)
        (.word (StorageSemantics.readWord source state.balances))).evaluates final)
      (by simp [BinaryOp.apply, shortfall])
  · exact .inRight (.pair .bool (.pair (.construct .unit) .word))

theorem dispatch_untransferred_preserves {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {initial : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state attempted : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (other : mode ≠ .ordinary)
    (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
    (computed : AccountCallSemantics.Run children mode source request state result attempted) :
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
  let runExtra := .unit :: extra
  let runEnv := runExtra ++ environment
  obtain ⟨output, afterRun, runEvaluated, resultRelated, afterRelated, runFrameProof⟩ :=
    run_children_preserves (childrenPreserved.prepend runExtra) (references.prepend runExtra)
      (argument.prepend runExtra) (related.retained retained) (stable (.ofRetains retained) ready) computed
      (precompiled := precompiled)
  have throughRun : SharedFrame locations initial afterRun := (SharedFrame.ofRetains retained).trans runFrameProof
  have enter {target : Core.Value} {final : Core.Store}
      (continued : Core.Evaluates runEnv first
        (.caseE (dispatchRun shared runFrame extended precompiled (depth + 6))
          ((bind (checkpointRestore shared depth) fun _ => failure Calls.responseType (fun here => .var (here - (depth + 6) - 1))) (depth + 7))
          ((let response : Code := fun here => .var (here - (depth + 6) - 1)
            choose (part 0 3 response) (success response)
              (bind (checkpointRestore shared depth) fun _ => success response)) (depth + 7))) target final) :
      Core.Evaluates environment initial (dispatchWith shared runFrame extended precompiled depth) target final := by
    apply checkpoint_evaluates references worldRead related.shared.logs related.shared.logSize related.shared.balances
    apply LanguageResult.bind_success Calls.responseType looked
    apply Core.Evaluates.ifFalse
    · cases mode with
      | ordinary => exact False.elim (other rfl)
      | callCode =>
        apply Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl)
        exact .binary ((requestCode.part (index := 2) rfl).evaluates first)
          ((CodeValue.bound (depth + 4) (saved ++ environment) (.word sourceBalance)).evaluates first)
          (by
            have enough : ¬ request.value > StorageSemantics.readWord source state.balances :=
              funds.resolve_left (by decide)
            simp [BinaryOp.apply, sourceBalance, enough])
      | delegateCall =>
        exact .ifTrue (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word rfl) .bool
    apply LanguageResult.bind_success Calls.responseType
      (Core.Evaluates.ifFalse (.binary ((afterArgument.part (index := 1) rfl).evaluates first) .word (by
        cases mode with
        | ordinary => exact False.elim (other rfl)
        | callCode => rfl
        | delegateCall => rfl)) (.inRight .unit))
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


private theorem transferFor_noTransfer {mode : AccountCallSemantics.Mode} {source : Word}
    {request : AccountCallSemantics.Request} {state final : AccountCallSemantics.Shared}
    (other : mode ≠ .ordinary) (moved : AccountCallSemantics.transferFor mode source request state = .ok final) :
    final = state := by
  have different : (mode == .ordinary) = false := by
      cases mode <;> first | rfl | contradiction
  simp only [AccountCallSemantics.transferFor, different, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at moved
  exact moved.symm

/-- Every source mode reaches the real dispatcher, including its checkpoint,
mode-specific funds check and child request transformation. -/
theorem dispatch_children_preserves {mode : AccountCallSemantics.Mode}
    {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Store → Prop} {depth : Nat} {environment : Environment} {initial : Store}
    {extended : Code} {source : Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState) :
    ∃ target final, Evaluates environment initial (AccountRuntime.dispatch shared runFrame extended depth) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  by_cases ordinary : mode = .ordinary
  · subst mode
    exact AccountCallCorrespondence.dispatch_children_preserves childrenPreserved stable references argument related ready computed
  cases computed with
  | insufficient checked shortfall =>
    obtain ⟨final, evaluated, retained⟩ := dispatch_insufficient references argument related.shared checked shortfall
    exact ⟨_, final, evaluated, .returned _, related.retained retained, .ofRetains retained⟩
  | transferFault funds failed =>
    have different : (mode == .ordinary) = false := by
      cases mode <;> first | rfl | contradiction
    simp only [AccountCallSemantics.transferFor, different, Bool.false_eq_true, ↓reduceIte] at failed
    contradiction
  | succeeded funds moved executed success =>
    cases transferFor_noTransfer ordinary moved
    simpa only [dispatchAfter, success, ↓reduceIte, dispatchWith, AccountRuntime.dispatch,
      dispatchRun, accountRun, childRequest] using
      dispatch_untransferred_preserves childrenPreserved stable references argument related ready ordinary funds executed
  | refused funds moved executed failure =>
    cases transferFor_noTransfer ordinary moved
    simpa only [dispatchAfter, failure, Bool.false_eq_true, ↓reduceIte, dispatchWith, AccountRuntime.dispatch,
      dispatchRun, accountRun, childRequest] using
      dispatch_untransferred_preserves childrenPreserved stable references argument related ready ordinary funds executed
  | fault funds moved executed =>
    cases transferFor_noTransfer ordinary moved
    exact dispatch_untransferred_preserves childrenPreserved stable references argument related ready ordinary funds executed

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
