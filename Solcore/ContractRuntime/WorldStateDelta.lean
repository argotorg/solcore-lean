import Solcore.ContractRuntime.WorldStateStorageRead
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.WorldStateNonceProperties
import Solcore.ContractRuntime.WorldStateCode

/-! Exact, queryable endpoint observations for arbitrary WorldState transitions. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/--
An exact observation of one transition between two WorldState endpoints.

WorldState is function-valued, so this carrier deliberately exposes pointwise
queries instead of claiming that changed accounts or slots can be enumerated.
-/
inductive WorldStateDelta (initialWorld finalWorld : WorldState) : Type where
  /-- The canonical exact observation for the indexed endpoint worlds. -/
  | exact : WorldStateDelta initialWorld finalWorld

namespace WorldStateDelta

/-- The unchanged transition, represented by the same canonical observation. -/
def identity (world : WorldState) : WorldStateDelta world world :=
  .exact

/-- Observe exact account presence and contents at one address. -/
def accountEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Account × Option Account :=
  (initialWorld.account? address, finalWorld.account? address)

/--
Observe exact storage reads at one address and slot.

Each endpoint remains optional: `none` means that the account is absent, while
`some Core.Word.zero` means that the account is present and the slot reads zero.
-/
def storageEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) : Option Core.Word × Option Core.Word :=
  (initialWorld.readStorage? address slot,
    finalWorld.readStorage? address slot)

/--
Observe exact balance endpoints at one address.

`none` denotes an absent account and `some Core.Word.zero` denotes a present
zero-balance account, so creation-era presence remains observable.
-/
def balanceEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Core.Word × Option Core.Word :=
  (initialWorld.balance? address, finalWorld.balance? address)

/-- Observe exact creation-nonce endpoints at one address. -/
def nonceEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option Core.Word × Option Core.Word :=
  (initialWorld.nonce? address, finalWorld.nonce? address)

/-- Observe exact checked-code endpoints at one address. -/
def codeEndpoints
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) :
    Option CheckedHostCoreProgram × Option CheckedHostCoreProgram :=
  (initialWorld.code? address, finalWorld.code? address)

/-- Report exactly an absent-to-present Account transition. -/
def createdAccount?
    {initialWorld finalWorld : WorldState}
    (_delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Bool :=
  match initialWorld.account? address, finalWorld.account? address with
  | none, some _ => true
  | _, _ => false

/-- Return exact old/new storage endpoints only when the observation changed. -/
def slotChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.storageEndpoints address slot
  if endpoints.1 = endpoints.2 then none else some endpoints

/-- Return exact old/new balance endpoints only when the observation changed. -/
def balanceChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.balanceEndpoints address
  if endpoints.1 = endpoints.2 then none else some endpoints

/-- Return exact old/new nonce endpoints only when the observation changed. -/
def nonceChange?
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address) : Option (Option Core.Word × Option Core.Word) :=
  let endpoints := delta.nonceEndpoints address
  if endpoints.1 = endpoints.2 then none else some endpoints

end WorldStateDelta

end Solcore.ContractRuntime
