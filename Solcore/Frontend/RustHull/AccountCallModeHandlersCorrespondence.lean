import Solcore.Frontend.RustHull.AccountCallModeRunCorrespondence

/-! The actual frame handler captures its execution address separately from
request caller and value. The selected mode is part of the captured Core body. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallModeCorrespondence
open Core Correspondence ScalarExecution CodeBuilder
open AccountCallCorrespondence (SharedLocations DispatcherClosure)

structure CallHandlerClosure (mode : AccountCallSemantics.Mode) (source : Word)
    (dispatcherLocation : Nat) (value : Value) where
  depth : Nat
  captured : Environment
  frame : Code
  dispatcher : Code
  closure : CapturedClosure (AccountRuntime.frameCallHandler mode.number frame dispatcher depth) captured value
  address : CodeValue depth captured (part 0 8 frame) (.word source)
  dispatcherReference : CodeValue depth captured dispatcher
    (.cellRef (OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)

structure InstalledHandlers (mode : AccountCallSemantics.Mode) (locations : SharedLocations) (source : Word)
    (handlerLocation dispatcherLocation : Nat) (store : Store) where
  dispatchValue : Value
  handlerValue : Value
  dispatch : DispatcherClosure locations dispatchValue
  handler : CallHandlerClosure mode source dispatcherLocation handlerValue
  dispatchRead : store.read? dispatcherLocation = some (.inRight .unit dispatchValue)
  handlerRead : store.read? handlerLocation = some (.inRight .unit handlerValue)

/-- Existing ordinary closures carry the same concrete body and references. -/
def CallHandlerClosure.of_ordinary {source : Word} {dispatcher : Nat} {value : Value}
    (handler : AccountCallCorrespondence.CallHandlerClosure source dispatcher value) :
    CallHandlerClosure .ordinary source dispatcher value where
  depth := handler.depth
  captured := handler.captured
  frame := handler.frame
  dispatcher := handler.dispatcher
  closure := handler.closure
  address := handler.address
  dispatcherReference := handler.dispatcherReference

end Solcore.Frontend.RustHull.AccountCallModeCorrespondence
