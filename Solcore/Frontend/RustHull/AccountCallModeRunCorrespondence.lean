import Solcore.Frontend.RustHull.AccountCallChildDispatchCorrespondence
import Solcore.Frontend.RustHull.ChildFrameModeSemantics

/-! Calls select code by the original target and execute it at the address
chosen by their dispatch mode. Captured requests keep caller and value separate. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation childRequest_evaluates childRequest_value

def extendedValue (mode : AccountCallSemantics.Mode) (source : Word)
    (request : AccountCallSemantics.Request) : Value :=
  bundleValues [requestValue request, .word (Word.ofNatModulo mode.number), .word source]

theorem childRequest_evaluates {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended : Code} {mode : AccountCallSemantics.Mode} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue mode source request)) :
    Core.Evaluates environment store (childRequest extended depth) (requestValue (ChildFrameModeSemantics.executionRequest mode source request)) store := by
  have requestCode := argument.part (index := 0) rfl
  apply Core.Evaluates.pair
  · cases mode with
    | ordinary =>
      exact .ifTrue (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((requestCode.part (index := 0) rfl).evaluates store)
    | callCode =>
      exact .ifFalse (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((argument.part (index := 2) rfl).evaluates store)
    | delegateCall =>
      exact .ifFalse (.binary ((argument.part (index := 1) rfl).evaluates store) .word rfl)
        ((argument.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 1) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 2) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 3) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 4) rfl).evaluates store)
  apply Core.Evaluates.pair ((requestCode.part (index := 5) rfl).evaluates store)
  exact .pair ((requestCode.part (index := 6) rfl).evaluates store)
    ((requestCode.part (index := 7) rfl).evaluates store)

theorem childRequest_value {depth : Nat} {environment : Core.Environment} {extended : Code}
    {mode : AccountCallSemantics.Mode} {source : Core.Word} {request : AccountCallSemantics.Request}
    (argument : CodeValue depth environment extended (extendedValue mode source request)) :
    CodeValue depth environment (childRequest extended) (requestValue (ChildFrameModeSemantics.executionRequest mode source request)) := by
  intro extra store
  simpa only [List.length_append, Nat.add_assoc] using childRequest_evaluates (argument.prepend extra) (store := store)

def ChildRunPreservation (mode : AccountCallSemantics.Mode) (anchors : List CatalogWorldCorrespondence.Anchor) (locations : SharedLocations)
    (shared : AccountRuntime.References) (runFrame : Code → Code → Code)
    (children : AccountCallSemantics.Children) (valid : Core.Store → Prop)
    (baseDepth : Nat) (captured : Core.Environment) : Prop :=
  ∀ {source request state result finalState}, children mode source request state result finalState →
  ∀ (extra : Core.Environment) {store : Core.Store} {extended precompiled : Code},
    SharedReferences (baseDepth + extra.length) (extra ++ captured) shared locations →
    CodeValue (baseDepth + extra.length) (extra ++ captured) extended (extendedValue mode source request) →
    LinkedSharedStateRel anchors locations state store → valid store →
    ∃ target final, Core.Evaluates (extra ++ captured) store
      (dispatchRun shared runFrame extended precompiled (baseDepth + extra.length)) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations store final

theorem ChildRunPreservation.prepend {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {baseDepth : Nat} {captured : Core.Environment}
    (preserved : ChildRunPreservation mode anchors locations shared runFrame children valid baseDepth captured)
    (front : Core.Environment) :
    ChildRunPreservation mode anchors locations shared runFrame children valid (baseDepth + front.length) (front ++ captured) := by
  intro source request state result finalState computed extra store extended precompiled references argument related ready
  have references' : SharedReferences (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) shared locations := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using references
  have argument' : CodeValue (baseDepth + (extra ++ front).length) ((extra ++ front) ++ captured) extended (extendedValue mode source request) := by
    simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using argument
  simpa only [List.length_append, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    preserved computed (extra ++ front) references' argument' related ready (precompiled := precompiled)

theorem run_children_preserves {mode : AccountCallSemantics.Mode} {anchors : List CatalogWorldCorrespondence.Anchor} {locations : SharedLocations}
    {shared : AccountRuntime.References} {runFrame : Code → Code → Code} {children : AccountCallSemantics.Children}
    {valid : Core.Store → Prop} {depth : Nat} {environment : Core.Environment} {store : Core.Store}
    {extended precompiled : Code} {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (childrenPreserved : ChildRunPreservation mode anchors locations shared runFrame children valid depth environment)
    (precompiledPreserved : PrecompiledPreservation precompiled request depth environment)
    (references : SharedReferences depth environment shared locations)
    (argument : CodeValue depth environment extended (extendedValue mode source request))
    (related : LinkedSharedStateRel anchors locations state store) (ready : valid store)
    (computed : AccountCallSemantics.Run children mode source request state result finalState) :
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

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
