import Solcore.Oracle.V5.Input
import Solcore.Oracle.V5.Wire.Scalar

/-! Oracle-only scenario decoding with embedded Core Programs kept opaque. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.Semantics

structure RawStaticMethod where
  name : String
  implementation : Lean.Json
  implementationPath : Path

inductive RawContractSpec where
  | checkedCore (program : Lean.Json) (programPath : Path)
  | staticWordAbi (methods : List RawStaticMethod)

structure RawContract where
  id : String
  spec : RawContractSpec

structure RawScenario where
  contracts : List RawContract
  world : WorldInput
  environment : EnvironmentInput
  invocation : InvocationInput

inductive RawQuery where
  | capabilities
  | coreCheck (program : Lean.Json) (path : Path)
  | execute (scenario : RawScenario)

def decodeStorageAt
    (path : Path)
    (json : Lean.Json) : DecodeResult StorageInput := do
  ensureExactObject path json ["slot", "value"] ["slot", "value"]
  let slot ← decodeWordAt (path.field "slot")
    (← requireField path json "slot")
  let value ← decodeWordAt (path.field "value")
    (← requireField path json "value")
  pure { slot, value }

def decodeAccountAt
    (path : Path)
    (json : Lean.Json) : DecodeResult AccountInput := do
  ensureExactObject path json
    ["address", "balance", "code", "nonce", "storage"]
    ["address", "balance", "code", "nonce", "storage"]
  let address ← decodeAddressAt (path.field "address")
    (← requireField path json "address")
  let balance ← decodeWordAt (path.field "balance")
    (← requireField path json "balance")
  let code ← decodeNullableStringAt (path.field "code")
    (← requireField path json "code")
  let nonce ← decodeWordAt (path.field "nonce")
    (← requireField path json "nonce")
  let storage ← decodeArrayAt decodeStorageAt (path.field "storage")
    (← requireField path json "storage")
  pure { address, balance, nonce, storage, code }

def decodeWorldAt
    (path : Path)
    (json : Lean.Json) : DecodeResult WorldInput := do
  ensureExactObject path json ["accounts"] ["accounts"]
  let accounts ← decodeArrayAt decodeAccountAt (path.field "accounts")
    (← requireField path json "accounts")
  pure { accounts }

def decodeCallBindingAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CallRegistryInput := do
  ensureExactObject path json
    ["address", "contract"] ["address", "contract"]
  let address ← decodeAddressAt (path.field "address")
    (← requireField path json "address")
  let contract ← decodeStringAt (path.field "contract")
    (← requireField path json "contract")
  pure { address, contract }

def decodeCreationTemplateAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CreationTemplateInput := do
  ensureExactObject path json
    ["initializer", "runtime", "templateId"]
    ["initializer", "runtime", "templateId"]
  let initializer ← decodeStringAt (path.field "initializer")
    (← requireField path json "initializer")
  let runtime ← decodeStringAt (path.field "runtime")
    (← requireField path json "runtime")
  let templateId ← decodeWordAt (path.field "templateId")
    (← requireField path json "templateId")
  pure { templateId, initializer, runtime }

def decodeCreationRouteAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CreationRouteInput := do
  ensureExactObject path json
    ["address", "creator", "nonce"] ["address", "creator", "nonce"]
  let address ← decodeAddressAt (path.field "address")
    (← requireField path json "address")
  let creator ← decodeAddressAt (path.field "creator")
    (← requireField path json "creator")
  let nonce ← decodeWordAt (path.field "nonce")
    (← requireField path json "nonce")
  pure { creator, nonce, address }

def decodeCreationAddressPolicyAt
    (path : Path)
    (json : Lean.Json) : DecodeResult CreationAddressPolicyInput := do
  ensureExactObject path json
    ["defaultAddress", "routes"] ["defaultAddress", "routes"]
  let defaultAddress ← decodeAddressAt (path.field "defaultAddress")
    (← requireField path json "defaultAddress")
  let routes ← decodeArrayAt decodeCreationRouteAt (path.field "routes")
    (← requireField path json "routes")
  pure { routes, defaultAddress }

def decodeEnvironmentAt
    (path : Path)
    (json : Lean.Json) : DecodeResult EnvironmentInput := do
  ensureExactObject path json
    ["callRegistry", "creationAddressPolicy", "creationTemplates"]
    ["callRegistry", "creationAddressPolicy", "creationTemplates"]
  let callRegistry ← decodeArrayAt decodeCallBindingAt
    (path.field "callRegistry")
    (← requireField path json "callRegistry")
  let creationAddressPolicy ← decodeCreationAddressPolicyAt
    (path.field "creationAddressPolicy")
    (← requireField path json "creationAddressPolicy")
  let creationTemplates ← decodeArrayAt decodeCreationTemplateAt
    (path.field "creationTemplates")
    (← requireField path json "creationTemplates")
  pure { callRegistry, creationTemplates, creationAddressPolicy }

def decodeProbeAt
    (path : Path)
    (json : Lean.Json) : DecodeResult Probe := do
  let kindPath := path.field "kind"
  let kind ← decodeStringAt kindPath (← requireField path json "kind")
  let probe ← match kind with
  | "accountPresence" => do
      ensureExactObject path json ["address", "kind"] ["address", "kind"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      pure (.accountPresence address)
  | "storage" => do
      ensureExactObject path json
        ["address", "kind", "slot"] ["address", "kind", "slot"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      let slot ← decodeWordAt (path.field "slot")
        (← requireField path json "slot")
      pure (.storage address slot)
  | "balance" | "nonce" | "code" => do
      ensureExactObject path json ["address", "kind"] ["address", "kind"]
      let address ← decodeAddressAt (path.field "address")
        (← requireField path json "address")
      match kind with
      | "balance" => pure (.balance address)
      | "nonce" => pure (.nonce address)
      | _ => pure (.code address)
  | _ => invalidTagAt kindPath (.str kind) <|
      Lean.Json.arr #["accountPresence", "storage", "balance", "nonce", "code"]
  pure probe

def decodeInvocationAt
    (path : Path)
    (json : Lean.Json) : DecodeResult InvocationInput := do
  ensureExactObject path json
    ["callValue", "calldata", "caller", "probes", "target"]
    ["callValue", "calldata", "caller", "probes", "target"]
  let callValue ← decodeWordAt (path.field "callValue")
    (← requireField path json "callValue")
  let calldata ← decodeBytesAt (path.field "calldata")
    (← requireField path json "calldata")
  let caller ← decodeAddressAt (path.field "caller")
    (← requireField path json "caller")
  let probes ← decodeArrayAt decodeProbeAt (path.field "probes")
    (← requireField path json "probes")
  let target ← decodeAddressAt (path.field "target")
    (← requireField path json "target")
  pure { target, caller, callValue, calldata, probes }

end Solcore.Oracle.V5.Wire
