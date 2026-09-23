import Solcore.Core.Wire.V3.Codec
import Solcore.Oracle.V5.Input
import Solcore.Oracle.V5.Wire.Scalar

/-! Canonical JSON encoding for Oracle v5 requests and scenarios. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.Core.Wire
open Solcore.ContractRuntime

private def jsonArray (values : List Lean.Json) : Lean.Json :=
  .arr values.toArray

private def contractLE (left right : ContractInput) : Bool :=
  (compare left.id right.id).isLE

private def canonicalContracts
    (contracts : List ContractInput) : List ContractInput :=
  contracts.mergeSort contractLE

private def methodSignature (method : StaticMethodInput) : String :=
  method.name ++ "(uint256)"

private def methodLE (left right : StaticMethodInput) : Bool :=
  (compare (methodSignature left) (methodSignature right)).isLE

private def canonicalMethods
    (methods : List StaticMethodInput) : List StaticMethodInput :=
  methods.mergeSort methodLE

private def accountLE (left right : AccountInput) : Bool :=
  (compare left.address.val right.address.val).isLE

private def canonicalAccounts
    (accounts : List AccountInput) : List AccountInput :=
  accounts.mergeSort accountLE

private def storageLE (left right : StorageInput) : Bool :=
  (compare left.slot.val right.slot.val).isLE

private def canonicalStorage
    (storage : List StorageInput) : List StorageInput :=
  storage.mergeSort storageLE

private def callLE (left right : CallRegistryInput) : Bool :=
  (compare left.address.val right.address.val).isLE

private def canonicalCalls
    (calls : List CallRegistryInput) : List CallRegistryInput :=
  calls.mergeSort callLE

private def templateLE
    (left right : CreationTemplateInput) : Bool :=
  (compare left.templateId.val right.templateId.val).isLE

private def canonicalTemplates
    (templates : List CreationTemplateInput) : List CreationTemplateInput :=
  templates.mergeSort templateLE

private def routeLE
    (left right : CreationRouteInput) : Bool :=
  match compare left.creator.val right.creator.val with
  | .lt => true
  | .gt => false
  | .eq => (compare left.nonce.val right.nonce.val).isLE

private def canonicalRoutes
    (routes : List CreationRouteInput) : List CreationRouteInput :=
  routes.mergeSort routeLE

def encodeLimits (limits : Limits) : Lean.Json :=
  .mkObj [
    ("jsonDepth", limits.jsonDepth),
    ("jsonNodes", limits.jsonNodes),
    ("coreDepth", limits.coreDepth),
    ("coreNodes", limits.coreNodes),
    ("scenarioEntries", limits.scenarioEntries),
    ("identifierBytes", limits.identifierBytes),
    ("calldataBytes", limits.calldataBytes),
    ("evaluationSteps", limits.evaluationSteps)
  ]

def encodeProfile (profile : ProfileRef) : Lean.Json :=
  .mkObj [
    ("id", profile.id),
    ("digest", profile.digest)
  ]

def encodeStaticMethod (method : StaticMethodInput) : Lean.Json :=
  .mkObj [
    ("name", method.name),
    ("implementation", V3.encodeProgram method.implementation)
  ]

def encodeContract (contract : ContractInput) : Lean.Json :=
  match contract.spec with
  | .checkedCore program => .mkObj [
      ("id", contract.id),
      ("kind", "checkedCore"),
      ("program", V3.encodeProgram program)
    ]
  | .staticWordAbi methods => .mkObj [
      ("id", contract.id),
      ("kind", "staticWordAbi"),
      ("methods", jsonArray <|
        (canonicalMethods methods).map encodeStaticMethod)
    ]

def encodeStorage (storage : StorageInput) : Lean.Json :=
  .mkObj [
    ("slot", encodeWord storage.slot),
    ("value", encodeWord storage.value)
  ]

def encodeAccount (account : AccountInput) : Lean.Json :=
  .mkObj [
    ("address", encodeAddress account.address),
    ("balance", encodeWord account.balance),
    ("nonce", encodeWord account.nonce),
    ("storage", jsonArray <|
      (canonicalStorage account.storage).map encodeStorage),
    ("code", encodeNullableString account.code)
  ]

def encodeWorld (world : WorldInput) : Lean.Json :=
  .mkObj [
    ("accounts", jsonArray <|
      (canonicalAccounts world.accounts).map encodeAccount)
  ]

def encodeCallBinding (binding : CallRegistryInput) : Lean.Json :=
  .mkObj [
    ("address", encodeAddress binding.address),
    ("contract", binding.contract)
  ]

def encodeCreationTemplate
    (template : CreationTemplateInput) : Lean.Json :=
  .mkObj [
    ("templateId", encodeWord template.templateId),
    ("initializer", template.initializer),
    ("runtime", template.runtime)
  ]

def encodeCreationRoute (route : CreationRouteInput) : Lean.Json :=
  .mkObj [
    ("creator", encodeAddress route.creator),
    ("nonce", encodeWord route.nonce),
    ("address", encodeAddress route.address)
  ]

def encodeCreationAddressPolicy
    (policy : CreationAddressPolicyInput) : Lean.Json :=
  .mkObj [
    ("routes", jsonArray <|
      (canonicalRoutes policy.routes).map encodeCreationRoute),
    ("defaultAddress", encodeAddress policy.defaultAddress)
  ]

def encodeEnvironment (environment : EnvironmentInput) : Lean.Json :=
  .mkObj [
    ("callRegistry", jsonArray <|
      (canonicalCalls environment.callRegistry).map encodeCallBinding),
    ("creationTemplates", jsonArray <|
      (canonicalTemplates environment.creationTemplates).map
        encodeCreationTemplate),
    ("creationAddressPolicy",
      encodeCreationAddressPolicy environment.creationAddressPolicy)
  ]

def encodeProbe : Probe → Lean.Json
  | .accountPresence address => .mkObj [
      ("kind", "accountPresence"),
      ("address", encodeAddress address)
    ]
  | .storage address slot => .mkObj [
      ("kind", "storage"),
      ("address", encodeAddress address),
      ("slot", encodeWord slot)
    ]
  | .balance address => .mkObj [
      ("kind", "balance"),
      ("address", encodeAddress address)
    ]
  | .nonce address => .mkObj [
      ("kind", "nonce"),
      ("address", encodeAddress address)
    ]
  | .code address => .mkObj [
      ("kind", "code"),
      ("address", encodeAddress address)
    ]

def encodeInvocation (invocation : InvocationInput) : Lean.Json :=
  .mkObj [
    ("target", encodeAddress invocation.target),
    ("caller", encodeAddress invocation.caller),
    ("callValue", encodeWord invocation.callValue),
    ("calldata", encodeBytes invocation.calldata),
    ("probes", jsonArray (invocation.probes.map encodeProbe))
  ]

def encodeQuery : Query → Lean.Json
  | .capabilities => .mkObj [("kind", "capabilities")]
  | .coreCheck program => .mkObj [
      ("kind", "coreCheck"),
      ("program", V3.encodeProgram program)
    ]
  | .execute scenario => .mkObj [
      ("kind", "execute"),
      ("contracts", jsonArray <|
        (canonicalContracts scenario.contracts).map encodeContract),
      ("world", encodeWorld scenario.world),
      ("environment", encodeEnvironment scenario.environment),
      ("invocation", encodeInvocation scenario.invocation)
    ]

/-- Canonical Oracle v5 request JSON, including fixed identity fields. -/
def encodeRequest (request : Request) : Lean.Json :=
  .mkObj [
    ("schema", schemaVersion),
    ("id", encodeRequestId request.id),
    ("spec", request.spec),
    ("profile", encodeProfile request.profile),
    ("limits", encodeLimits request.limits),
    ("query", encodeQuery request.query)
  ]

def encodeRequestText (request : Request) : String :=
  (encodeRequest request).compress

end Solcore.Oracle.V5.Wire
