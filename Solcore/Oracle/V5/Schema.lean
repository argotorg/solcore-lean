import Solcore.Core.Wire.V3.Host
import Solcore.Profile

/-! Closed identities and resource types for the Oracle v5 boundary. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

def schemaVersion : String := "solcore-oracle/v5"
def capabilitiesSchema : String := "solcore-capabilities/v5"
def checkResultSchema : String := "solcore-core-check-result/v3"
def executionSchema : String := "solcore-contract-execution/v1"
def stateObservationSchema : String := "solcore-world-state-observation/v1"

def requestIdValid (value : String) : Bool :=
  !value.isEmpty

structure RequestId where
  value : String
  valid : requestIdValid value = true
  deriving Repr, DecidableEq

namespace RequestId

instance : BEq RequestId :=
  ⟨fun left right => left.value == right.value⟩

def ofString? (value : String) : Option RequestId :=
  if valid : requestIdValid value = true then
    some ⟨value, valid⟩
  else
    none

@[simp] theorem ofString?_value (id : RequestId) :
    ofString? id.value = some id := by
  cases id with
  | mk value valid => simp [ofString?, valid]

def byteSize (id : RequestId) : Nat :=
  id.value.toUTF8.size

end RequestId

private def asciiLetter (character : Char) : Bool :=
  let code := character.toNat
  (65 ≤ code && code ≤ 90) || (97 ≤ code && code ≤ 122)

private def asciiDigit (character : Char) : Bool :=
  let code := character.toNat
  48 ≤ code && code ≤ 57

private def contractIdStart (character : Char) : Bool :=
  asciiLetter character || character == '_'

private def contractIdContinue (character : Char) : Bool :=
  contractIdStart character || asciiDigit character ||
    character == '.' || character == '-'

/-- Decide the exact ASCII grammar `[A-Za-z_][A-Za-z0-9_.-]*`. -/
def contractIdValid (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest => contractIdStart first && rest.all contractIdContinue

structure ContractId where
  value : String
  valid : contractIdValid value = true
  deriving Repr, DecidableEq

namespace ContractId

instance : BEq ContractId :=
  ⟨fun left right => left.value == right.value⟩

def ofString? (value : String) : Option ContractId :=
  if valid : contractIdValid value = true then
    some ⟨value, valid⟩
  else
    none

@[simp] theorem ofString?_value (id : ContractId) :
    ofString? id.value = some id := by
  cases id with
  | mk value valid => simp [ofString?, valid]

def byteSize (id : ContractId) : Nat :=
  id.value.toUTF8.size

end ContractId

structure Limits where
  jsonDepth : Nat
  jsonNodes : Nat
  coreDepth : Nat
  coreNodes : Nat
  scenarioEntries : Nat
  identifierBytes : Nat
  calldataBytes : Nat
  evaluationSteps : Nat
  deriving Repr, BEq, DecidableEq

def Limits.default : Limits := {
  jsonDepth := 2048
  jsonNodes := 2000000
  coreDepth := 1024
  coreNodes := 1000000
  scenarioEntries := 100000
  identifierBytes := 256
  calldataBytes := 1048576
  evaluationSteps := 1000000
}

def Limits.Valid (limits : Limits) : Prop :=
  limits.calldataBytes < Core.wordModulus

def Limits.isValid (limits : Limits) : Bool :=
  decide (limits.calldataBytes < Core.wordModulus)

theorem Limits.isValid_iff (limits : Limits) :
    limits.isValid = true ↔ limits.Valid := by
  simp [Limits.isValid, Limits.Valid]

inductive QueryKind where
  | capabilities
  | coreCheck
  | execute
  deriving Repr, BEq, DecidableEq

namespace QueryKind

def all : Array QueryKind := #[.capabilities, .coreCheck, .execute]

end QueryKind

inductive ProfileRef where
  | contractM3aV1
  deriving Repr, BEq, DecidableEq

namespace ProfileRef

def canonical : ProfileRef := .contractM3aV1

def id : ProfileRef → String
  | .contractM3aV1 => Solcore.m3aContractProfile.id

def digest : ProfileRef → String
  | .contractM3aV1 => Solcore.m3aContractProfileDigest

end ProfileRef

inductive Phase where
  | protocol
  | requestPreflight
  | coreDecoding
  | coreChecking
  | contractAdmission
  | worldValidation
  | environmentValidation
  | probeValidation
  | rootInstallation
  | contractExecution
  | observationEncoding
  deriving Repr, BEq, DecidableEq

inductive ResourceKind where
  | jsonDepth
  | jsonNodes
  | coreDepth
  | coreNodes
  | scenarioEntries
  | identifierBytes
  | calldataBytes
  | evaluationSteps
  deriving Repr, BEq, DecidableEq

inductive PreflightResource where
  | jsonDepth
  | jsonNodes
  | coreDepth
  | coreNodes
  | scenarioEntries
  | identifierBytes
  | calldataBytes
  deriving Repr, BEq, DecidableEq

namespace PreflightResource

def toResourceKind : PreflightResource → ResourceKind
  | .jsonDepth => .jsonDepth
  | .jsonNodes => .jsonNodes
  | .coreDepth => .coreDepth
  | .coreNodes => .coreNodes
  | .scenarioEntries => .scenarioEntries
  | .identifierBytes => .identifierBytes
  | .calldataBytes => .calldataBytes

def phase : PreflightResource → Phase
  | .coreDepth
  | .coreNodes => .coreDecoding
  | .jsonDepth
  | .jsonNodes
  | .scenarioEntries
  | .identifierBytes
  | .calldataBytes => .requestPreflight

end PreflightResource

structure PreflightExhaustion where
  resource : PreflightResource
  limit : Nat
  consumed : Nat
  exceeded : limit < consumed
  deriving Repr, DecidableEq

namespace PreflightExhaustion

instance : BEq PreflightExhaustion :=
  ⟨fun left right =>
    left.resource == right.resource && left.limit == right.limit &&
      left.consumed == right.consumed⟩

def ofValues?
    (resource : PreflightResource)
    (limit consumed : Nat) : Option PreflightExhaustion :=
  if exceeded : limit < consumed then
    some ⟨resource, limit, consumed, exceeded⟩
  else
    none

@[simp] theorem ofValues?_fields (exhaustion : PreflightExhaustion) :
    ofValues? exhaustion.resource exhaustion.limit exhaustion.consumed =
      some exhaustion := by
  cases exhaustion with
  | mk resource limit consumed exceeded => simp [ofValues?, exceeded]

def phase (exhaustion : PreflightExhaustion) : Phase :=
  exhaustion.resource.phase

end PreflightExhaustion

inductive Exhaustion where
  | preflight (value : PreflightExhaustion)
  | evaluationSteps (limit : Nat)
  deriving Repr, BEq, DecidableEq

namespace Exhaustion

def resource : Exhaustion → ResourceKind
  | .preflight value => value.resource.toResourceKind
  | .evaluationSteps _ => .evaluationSteps

def phase : Exhaustion → Phase
  | .preflight value => value.phase
  | .evaluationSteps _ => .contractExecution

def limit : Exhaustion → Nat
  | .preflight value => value.limit
  | .evaluationSteps value => value

def consumed : Exhaustion → Nat
  | .preflight value => value.consumed
  | .evaluationSteps value => value

end Exhaustion

inductive InternalError where
  | coreWireProjectionFailed
  | worldCodeReferenceInvariant
  | oracleResponseInvariant
  deriving Repr, BEq, DecidableEq

namespace InternalError

def phase : InternalError → Option Phase
  | .coreWireProjectionFailed
  | .worldCodeReferenceInvariant => some .observationEncoding
  | .oracleResponseInvariant => none

def code : InternalError → String
  | .coreWireProjectionFailed => "core-wire-projection-failed"
  | .worldCodeReferenceInvariant => "world-code-reference-invariant"
  | .oracleResponseInvariant => "oracle-response-invariant"

end InternalError

end Solcore.Oracle.V5
