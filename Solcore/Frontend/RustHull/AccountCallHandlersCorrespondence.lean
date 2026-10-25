import Solcore.Frontend.RustHull.AccountCallSemantics
import Solcore.Frontend.RustHull.RuntimeClosureCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeCorrespondence
import Solcore.Frontend.RustHull.StorageCorrespondence

/-! Installed call handlers record the actual closures, their captured cell
references, and the optional cells from which the runtime reads them. No field
assumes that a callback preserves source execution. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallCorrespondence
open Correspondence ScalarExecution CodeBuilder

structure SharedLocations where
  world : Nat
  logs : Nat
  logSize : Nat
  balances : Nat
  complete : Nat

def SharedLocations.all (locations : SharedLocations) : List Nat :=
  [locations.world, locations.logs, locations.logSize, locations.balances, locations.complete]

structure SharedReferences (depth : Nat) (environment : Core.Environment)
    (shared : AccountRuntime.References) (locations : SharedLocations) : Prop where
  world : CodeValue depth environment (AccountRuntime.reference shared "world") (.cellRef AccountState.type locations.world)
  logs : CodeValue depth environment (AccountRuntime.reference shared "logs") (.cellRef Core.WordMapping.type locations.logs)
  logSize : CodeValue depth environment (AccountRuntime.reference shared "logSize") (.cellRef .word locations.logSize)
  balances : CodeValue depth environment (AccountRuntime.reference shared "balances") (.cellRef Core.WordMapping.type locations.balances)
  complete : CodeValue depth environment (AccountRuntime.reference shared "worldComplete") (.cellRef .bool locations.complete)

theorem SharedReferences.prepend {depth : Nat} {environment : Core.Environment}
    {shared : AccountRuntime.References} {locations : SharedLocations}
    (references : SharedReferences depth environment shared locations) (extra : Core.Environment) :
    SharedReferences (depth + extra.length) (extra ++ environment) shared locations :=
  ⟨references.world.prepend extra, references.logs.prepend extra, references.logSize.prepend extra,
    references.balances.prepend extra, references.complete.prepend extra⟩

structure SharedStateRel (locations : SharedLocations) (state : AccountCallSemantics.Shared)
    (store : Core.Store) : Prop where
  world : ∃ accounts : StorageCorrespondence.Accounts,
    accounts.map Prod.fst = state.world ∧ store.read? locations.world = some (StorageCorrespondence.world accounts)
  logs : store.read? locations.logs = some (Core.WordMapping.encode state.logs)
  logSize : store.read? locations.logSize = some (.word state.logSize)
  balances : store.read? locations.balances = some (Core.WordMapping.encode state.balances)
  complete : store.read? locations.complete = some (.bool state.complete)
  distinct : locations.all.Nodup

structure DispatcherClosure (locations : SharedLocations) (value : Core.Value) where
  depth : Nat
  captured : Core.Environment
  shared : AccountRuntime.References
  runFrame : Code → Code → Code
  closure : CapturedClosure
    (lambda AccountRuntime.dispatchType (Core.LanguageResult.resultType Calls.responseType)
      (AccountRuntime.dispatch shared runFrame) depth) captured value
  references : SharedReferences depth captured shared locations

structure CallHandlerClosure (source : Core.Word) (dispatcherLocation : Nat) (value : Core.Value) where
  depth : Nat
  captured : Core.Environment
  frame : Code
  dispatcher : Code
  closure : CapturedClosure (AccountRuntime.frameCallHandler 0 frame dispatcher depth) captured value
  address : CodeValue depth captured (part 0 8 frame) (.word source)
  dispatcherReference : CodeValue depth captured dispatcher
    (.cellRef (Core.OptionalCell.cellType AccountRuntime.dispatchCallbackType) dispatcherLocation)

structure InstalledHandlers (locations : SharedLocations) (source : Core.Word)
    (handlerLocation dispatcherLocation : Nat) (store : Core.Store) where
  dispatchValue : Core.Value
  handlerValue : Core.Value
  dispatch : DispatcherClosure locations dispatchValue
  handler : CallHandlerClosure source dispatcherLocation handlerValue
  dispatchRead : store.read? dispatcherLocation = some (.inRight .unit dispatchValue)
  handlerRead : store.read? handlerLocation = some (.inRight .unit handlerValue)

end Solcore.Frontend.RustHull.AccountCallCorrespondence
