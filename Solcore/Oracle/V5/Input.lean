import Solcore.Oracle.V5.Schema
import Solcore.ContractRuntime.RuntimeScalars

/-! Fully decoded, still-untrusted input values for Oracle v5. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Core.Wire
open Solcore.ContractRuntime

structure StaticMethodInput where
  name : String
  implementation : V3.Program
  deriving Repr, BEq, DecidableEq

inductive ContractSpec where
  | checkedCore (program : V3.Program)
  | staticWordAbi (methods : List StaticMethodInput)
  deriving Repr, BEq, DecidableEq

namespace ContractSpec

def programs : ContractSpec → List V3.Program
  | .checkedCore program => [program]
  | .staticWordAbi methods => methods.map (fun method => method.implementation)

def methodNames : ContractSpec → List String
  | .checkedCore _ => []
  | .staticWordAbi methods => methods.map (fun method => method.name)

def scenarioEntries : ContractSpec → Nat
  | .checkedCore _ => 0
  | .staticWordAbi methods => methods.length

end ContractSpec

structure ContractInput where
  id : String
  spec : ContractSpec
  deriving Repr, BEq, DecidableEq

structure StorageInput where
  slot : Core.Word
  value : Core.Word
  deriving Repr, BEq, DecidableEq

structure AccountInput where
  address : Address
  balance : Core.Word
  nonce : Core.Word
  storage : List StorageInput
  code : Option String
  deriving Repr, BEq, DecidableEq

structure WorldInput where
  accounts : List AccountInput
  deriving Repr, BEq, DecidableEq

structure CallRegistryInput where
  address : Address
  contract : String
  deriving Repr, BEq, DecidableEq

structure CreationTemplateInput where
  templateId : Core.Word
  initializer : String
  runtime : String
  deriving Repr, BEq, DecidableEq

structure CreationRouteInput where
  creator : Address
  nonce : Core.Word
  address : Address
  deriving Repr, BEq, DecidableEq

structure CreationAddressPolicyInput where
  routes : List CreationRouteInput
  defaultAddress : Address
  deriving Repr, BEq, DecidableEq

structure EnvironmentInput where
  callRegistry : List CallRegistryInput
  creationTemplates : List CreationTemplateInput
  creationAddressPolicy : CreationAddressPolicyInput
  deriving Repr, BEq, DecidableEq

inductive Probe where
  | accountPresence (address : Address)
  | storage (address : Address) (slot : Core.Word)
  | balance (address : Address)
  | nonce (address : Address)
  | code (address : Address)
  deriving Repr, BEq, DecidableEq

namespace Probe

def address : Probe → Address
  | .accountPresence address
  | .storage address _
  | .balance address
  | .nonce address
  | .code address => address

end Probe

structure InvocationInput where
  target : Address
  caller : Address
  callValue : Core.Word
  calldata : Bytes
  probes : List Probe
  deriving BEq, DecidableEq

structure Scenario where
  contracts : List ContractInput
  world : WorldInput
  environment : EnvironmentInput
  invocation : InvocationInput
  deriving BEq, DecidableEq

namespace Scenario

def programs (scenario : Scenario) : List V3.Program :=
  scenario.contracts.flatMap (fun contract => contract.spec.programs)

def scenarioEntries (scenario : Scenario) : Nat :=
  scenario.contracts.length +
    (scenario.contracts.map (fun contract =>
      contract.spec.scenarioEntries)).sum +
    scenario.world.accounts.length +
    (scenario.world.accounts.map (fun account => account.storage.length)).sum +
    scenario.environment.callRegistry.length +
    scenario.environment.creationTemplates.length +
    scenario.environment.creationAddressPolicy.routes.length +
    scenario.invocation.probes.length

def identifierTexts (scenario : Scenario) : List String :=
  let contractDefinitions := scenario.contracts.flatMap fun contract =>
    contract.id :: contract.spec.methodNames
  let accountCode := scenario.world.accounts.filterMap (fun account => account.code)
  let callReferences :=
    scenario.environment.callRegistry.map (fun binding => binding.contract)
  let templateReferences := scenario.environment.creationTemplates.flatMap fun template =>
    [template.initializer, template.runtime]
  contractDefinitions ++ accountCode ++ callReferences ++ templateReferences

def maxIdentifierBytes (scenario : Scenario) : Nat :=
  scenario.identifierTexts.foldl
    (fun current value => Nat.max current value.toUTF8.size) 0

def calldataBytes (scenario : Scenario) : Nat :=
  scenario.invocation.calldata.size

end Scenario

inductive Query where
  | capabilities
  | coreCheck (program : V3.Program)
  | execute (scenario : Scenario)
  deriving BEq, DecidableEq

namespace Query

def kind : Query → QueryKind
  | .capabilities => .capabilities
  | .coreCheck _ => .coreCheck
  | .execute _ => .execute

def programs : Query → List V3.Program
  | .capabilities => []
  | .coreCheck program => [program]
  | .execute scenario => scenario.programs

def scenarioEntries : Query → Nat
  | .capabilities
  | .coreCheck _ => 0
  | .execute scenario => scenario.scenarioEntries

def identifierTexts : Query → List String
  | .capabilities
  | .coreCheck _ => []
  | .execute scenario => scenario.identifierTexts

def calldataBytes : Query → Nat
  | .capabilities
  | .coreCheck _ => 0
  | .execute scenario => scenario.calldataBytes

end Query

structure Request where
  id : RequestId
  limits : Limits
  query : Query
  deriving BEq, DecidableEq

namespace Request

def schema (_request : Request) : String := schemaVersion
def spec (_request : Request) : String := Solcore.m3aLanguage.id
def profile (_request : Request) : ProfileRef := ProfileRef.canonical
def queryKind (request : Request) : QueryKind := request.query.kind

def maxIdentifierBytes (request : Request) : Nat :=
  Nat.max request.id.byteSize <|
    request.query.identifierTexts.foldl
      (fun current value => Nat.max current value.toUTF8.size) 0

end Request

end Solcore.Oracle.V5
