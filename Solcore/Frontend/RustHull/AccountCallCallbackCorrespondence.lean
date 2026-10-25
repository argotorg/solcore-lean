import Solcore.Frontend.RustHull.AccountCallDispatchCorrespondence

/-! The concrete callback closures installed by object initialization execute
independent account dispatch in their captured environments. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Core Correspondence ScalarExecution CodeBuilder CallTransportCorrespondence

theorem DispatcherClosure.apply_preserves {locations : SharedLocations} {value : Core.Value}
    (closure : DispatcherClosure locations value)
    {source : Core.Word} {request : AccountCallSemantics.Request}
    {state finalState : AccountCallSemantics.Shared} {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (resolved : Core.Evaluates environment before function value middle)
    (supplied : Core.Evaluates environment middle argument (extendedValue source request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final := by
  rcases closure with ⟨depth, captured, shared, runFrame, capturedClosure, references⟩
  cases capturedClosure
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, frame⟩ :=
    dispatch_preserves (references.prepend [extendedValue source request])
      (CodeValue.bound depth captured (extendedValue source request)) related computed
  exact ⟨target, final, .apply resolved supplied evaluated, resultRelated, finalRelated, frame⟩

theorem CallHandlerClosure.apply_preserves {locations : SharedLocations} {source : Core.Word}
    {dispatcherLocation : Nat} {handlerValue dispatchValue : Core.Value}
    (handler : CallHandlerClosure source dispatcherLocation handlerValue)
    (dispatcher : DispatcherClosure locations dispatchValue)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {before middle initial : Core.Store} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (dispatchRead : initial.read? dispatcherLocation = some (.inRight .unit dispatchValue))
    (resolved : Core.Evaluates environment before function handlerValue middle)
    (supplied : Core.Evaluates environment middle argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment before (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final := by
  rcases handler with ⟨depth, captured, frame, dispatchRef, capturedClosure, address, dispatcherReference⟩
  cases capturedClosure
  have read := OptionalCell.read_success (Word.ofNatModulo 7)
    ((dispatcherReference.prepend [requestValue request]).evaluates initial) dispatchRead
  have requestBound := CodeValue.bound depth captured (requestValue request)
  have dispatchBound := CodeValue.bound (depth + 1) (requestValue request :: captured) dispatchValue
  have suppliedExtended := Core.Evaluates.pair ((requestBound.prepend [dispatchValue]).evaluates initial)
    (.pair (.word (value := Word.zero)) ((address.prepend [dispatchValue, requestValue request]).evaluates initial))
  obtain ⟨target, final, evaluated, resultRelated, finalRelated, kept⟩ :=
    dispatcher.apply_preserves computed related (dispatchBound.evaluates initial) suppliedExtended
  refine ⟨target, final, .apply resolved supplied ?_, resultRelated, finalRelated, kept⟩
  exact LanguageResult.bind_success Calls.responseType read evaluated

/-- Handler-cell reads are the reads installed by the actual initializer;
callback correctness follows from the captured body, not a premise. -/
theorem InstalledHandlers.apply_preserves {locations : SharedLocations} {source : Core.Word}
    {handlerLocation dispatcherLocation : Nat} {initial : Core.Store}
    (installed : InstalledHandlers locations source handlerLocation dispatcherLocation initial)
    {request : AccountCallSemantics.Request} {state finalState : AccountCallSemantics.Shared}
    {result : Semantics.Result AccountCallSemantics.Response}
    (computed : AccountCallSemantics.Dispatch AccountCallSemantics.noChildren .ordinary source request state result finalState)
    {environment : Core.Environment} {function argument : Core.Expr}
    (related : SharedStateRel locations state initial)
    (resolved : Core.Evaluates environment initial function installed.handlerValue initial)
    (supplied : Core.Evaluates environment initial argument (requestValue request) initial) :
    ∃ target final, Core.Evaluates environment initial (.apply function argument) target final ∧
      ResponseRel result target ∧ SharedStateRel locations finalState final ∧
      BalanceFrame locations.balances initial final :=
  installed.handler.apply_preserves installed.dispatch computed related installed.dispatchRead resolved supplied

end Solcore.Frontend.RustHull.AccountCallCorrespondence
