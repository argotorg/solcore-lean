import Solcore.Frontend.RustHull.StorageSemantics
import Solcore.Frontend.RustHull.MemorySemantics

/-! Account dispatch and its checkpoint are independent of Core closures.
Requests carry the copied calldata of a child frame. The child relation is
instantiated by finite source call trees, while an absent account in a complete
world can return without executing a child frame. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.AccountCallSemantics
open Core

structure Request where
  target : Word
  caller : Word
  value : Word
  isStatic : Bool
  depth : Word
  gas : Word
  calldata : MemorySemantics.Entries
  calldataSize : Word
  deriving Repr

structure Response where
  success : Bool
  data : MemorySemantics.Entries
  size : Word
  deriving Repr

structure Shared where
  world : StorageSemantics.World := []
  balances : StorageSemantics.Words := []
  logs : MemorySemantics.Entries := []
  logSize : Word := Word.zero
  complete : Bool := false
  deriving Repr

inductive Mode where
  | ordinary | callCode | delegateCall
  deriving DecidableEq, BEq, Repr

def Mode.number : Mode → Nat
  | .ordinary => 0 | .callCode => 1 | .delegateCall => 2

def emptyResponse (success : Bool) : Response := ⟨success, [], Word.zero⟩

def isPrecompile (target : Word) : Bool :=
  target == Word.ofNatModulo 256 || (target > Word.zero && Word.ofNatModulo 5 > target)

/-- The caller's funds are checked before this transfer. The self-transfer and
zero-value cases leave the mathematical balance mapping unchanged. -/
def transfer (source target value : Word) (balances : StorageSemantics.Words) : Except Word StorageSemantics.Words :=
  if value == Word.zero then .ok balances
  else if source == target then .ok balances
  else
    let sourceBalance := StorageSemantics.readWord source balances
    let targetBalance := StorageSemantics.readWord target balances
    if targetBalance > Word.maximum.sub value then .error (Word.ofNatModulo 12)
    else .ok (StorageSemantics.writeWord target (targetBalance.add value)
      (StorageSemantics.writeWord source (sourceBalance.sub value) balances))

def transferFor (mode : Mode) (source : Word) (request : Request) (state : Shared) : Except Word Shared :=
  if mode == .ordinary then
    (transfer source request.target request.value state.balances).map fun balances => {state with balances := balances}
  else .ok state

abbrev Children := Mode → Word → Request → Shared → Semantics.Result Response → Shared → Prop

/-- A child-free dispatch is justified by absence in the source world. This
also establishes that its real default record has executable identity zero;
no identity is inferred merely from empty bytecode. -/
inductive Run (children : Children) (mode : Mode) (source : Word) (request : Request) :
    Shared → Semantics.Result Response → Shared → Prop where
  | empty {state : Shared}
      (ordinaryAccount : isPrecompile request.target = false)
      (absent : StorageSemantics.lookup request.target state.world = none)
      (complete : state.complete = true) :
      Run children mode source request state (.value (emptyResponse true)) state
  | unavailable {state : Shared}
      (ordinaryAccount : isPrecompile request.target = false)
      (absent : StorageSemantics.lookup request.target state.world = none)
      (incomplete : state.complete = false) :
      Run children mode source request state (.fault (.language (Word.ofNatModulo 7))) state
  | child {state result final}
      (executed : children mode source request state result final) :
      Run children mode source request state result final

/-- Shared state is restored after a false child response or a language fault.
The unsuccessful response still carries its revert bytes to the caller. -/
inductive Dispatch (children : Children) (mode : Mode) (source : Word) (request : Request) :
    Shared → Semantics.Result Response → Shared → Prop where
  | insufficient {state : Shared}
      (checked : mode ≠ .delegateCall)
      (shortfall : request.value > StorageSemantics.readWord source state.balances) :
      Dispatch children mode source request state (.value (emptyResponse false)) state
  | transferFault {state : Shared} {reason : Word}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (failed : transferFor mode source request state = .error reason) :
      Dispatch children mode source request state (.fault (.language reason)) state
  | succeeded {state transferred final : Shared} {response : Response}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.value response) final)
      (success : response.success = true) :
      Dispatch children mode source request state (.value response) final
  | refused {state transferred attempted : Shared} {response : Response}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.value response) attempted)
      (failure : response.success = false) :
      Dispatch children mode source request state (.value response) state
  | fault {state transferred attempted : Shared} {fault : Semantics.Fault}
      (funds : mode = .delegateCall ∨ ¬ request.value > StorageSemantics.readWord source state.balances)
      (moved : transferFor mode source request state = .ok transferred)
      (executed : Run children mode source request transferred (.fault fault) attempted) :
      Dispatch children mode source request state (.fault fault) state

def noChildren : Children := fun _ _ _ _ _ _ => False

end Solcore.Frontend.RustHull.AccountCallSemantics
