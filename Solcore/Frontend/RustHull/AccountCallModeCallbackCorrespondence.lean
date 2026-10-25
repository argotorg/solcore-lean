import Solcore.Frontend.RustHull.AccountCallModeDispatchCorrespondence
import Solcore.Frontend.RustHull.AccountCallModeHandlersCorrespondence

/-! Captured runtime handlers execute child-capable dispatch. The internal
child interface is discharged by compiled frame execution before the public
contract theorem is exposed. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence
open AccountCallCorrespondence hiding extendedValue ChildRunPreservation CallHandlerClosure InstalledHandlers dispatch_children_preserves

theorem dispatcher_apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {value : Core.Value}
    (closure : DispatcherClosure locations value)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations closure.shared closure.runFrame children valid closure.depth closure.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment before function value middle)
    (supplied : Core.Evaluates environment middle argument (extendedValue mode source request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases closure with ⟨depth, captured, shared, runFrame, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, frame⟩ :=
    dispatch_children_preserves (childrenPreserved.prepend [extendedValue mode source request]) stable
      (references.prepend [extendedValue mode source request])
      (CodeValue.bound depth captured (extendedValue mode source request)) related ready computed
  exact ⟨target, final, .apply resolved supplied evaluated, resultRelated, finalRelated, frame⟩

theorem CallHandlerClosure.apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {source : Core.Word}
    {dispatcherLocation : Nat} {handlerValue dispatchValue : Core.Value}
    (handler : CallHandlerClosure mode source dispatcherLocation handlerValue)
    (dispatcher : DispatcherClosure locations dispatchValue)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations dispatcher.shared dispatcher.runFrame children valid dispatcher.depth dispatcher.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (dispatchRead : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (resolved : Core.Evaluates environment before function handlerValue middle)
    (supplied : Core.Evaluates environment middle argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final := by
  rcases handler with ⟨depth, captured, frame, dispatchRef, capturedClosure, address, dispatcherReference⟩
  cases capturedClosure
  have read := OptionalCell.read_success (Word.ofNatModulo 7)
    ((dispatcherReference.prepend [requestValue request]).evaluates initial) dispatchRead
  have requestBound := CodeValue.bound depth captured (requestValue request)
  have dispatchBound := CodeValue.bound (depth + 1) (requestValue request :: captured) dispatchValue
  have suppliedExtended := Core.Evaluates.pair ((requestBound.prepend [dispatchValue]).evaluates initial)
    (.pair (.word (value := Word.ofNatModulo mode.number)) ((address.prepend [dispatchValue, requestValue request]).evaluates initial))
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, kept⟩ :=
    dispatcher_apply_children_preserves dispatcher childrenPreserved stable computed related ready (dispatchBound.evaluates initial) suppliedExtended
  refine ⟨target, final, .apply resolved supplied ?_, resultRelated, finalRelated, kept⟩
  exact LanguageResult.bind_success Calls.responseType read evaluated

/-- Handler-cell reads are the reads installed by the actual initializer;
callback correctness follows from the captured body, not a premise. -/
theorem InstalledHandlers.apply_children_preserves {mode : AccountCallSemantics.Mode} {locations : SharedLocations} {source : Core.Word}
    {handlerLocation dispatcherLocation : Nat} {initial : Core.Store}
    (installed : InstalledHandlers mode locations source handlerLocation dispatcherLocation initial)
    {anchors : List CatalogWorldCorrespondence.Anchor} {children : AccountCallSemantics.Children} {valid : Core.Store → Prop}
    (childrenPreserved : ChildRunPreservation mode anchors locations installed.dispatch.shared installed.dispatch.runFrame children valid
      installed.dispatch.depth installed.dispatch.captured)
    (stable : ∀ {first last}, SharedFrame locations first last → valid first → valid last)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch children mode source request state result finalState)
    {environment : Core.Environment} {function argument : Core.Expr}
    (related : LinkedSharedStateRel anchors locations state initial) (ready : valid initial)
    (resolved : Core.Evaluates environment initial function installed.handlerValue initial)
    (supplied : Core.Evaluates environment initial argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment initial (.apply function argument) target final ∧
      ResponseRel result target ∧ LinkedSharedStateRel anchors locations finalState final ∧
      SharedFrame locations initial final :=
  installed.handler.apply_children_preserves installed.dispatch childrenPreserved stable computed related ready installed.dispatchRead resolved supplied

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
