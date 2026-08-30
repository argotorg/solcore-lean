import Solcore.Core.Wire.V3.Codec
import Solcore.Oracle.V5.Wire.RequestShape

/-! Canonical embedded-Program decoding with cumulative Core resource state. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.Wire

open Solcore.Core.Wire

inductive ProgramDecodeFailure where
  | protocol (error : ProtocolError)
  | exhausted (exhaustion : V3.CoreBudgetExhaustion)

abbrev ProgramDecodeResult (α : Type) := Except ProgramDecodeFailure α

/-- A complete typed request retaining the sole non-structural Limits proof. -/
structure DecodedRequest where
  value : Request
  limitsValid : value.limits.Valid

private def liftCore {α : Type}
    (result : V3.CoreDecodeResult α) : ProgramDecodeResult α :=
  result.mapError fun failure =>
    match failure with
    | .protocol error => .protocol (.core error)
    | .exhausted exhaustion => .exhausted exhaustion

private def coreLimits (limits : Limits) : V3.CoreBudgetLimits := {
  maxDepth := limits.coreDepth
  maxNodes := limits.coreNodes
}

private def contractLE (left right : RawContract) : Bool :=
  (compare left.id right.id).isLE

def canonicalRawContracts
    (contracts : List RawContract) : List RawContract :=
  contracts.mergeSort contractLE

private def rawMethodSignature (method : RawStaticMethod) : String :=
  method.name ++ "(uint256)"

private def methodLE (left right : RawStaticMethod) : Bool :=
  (compare (rawMethodSignature left) (rawMethodSignature right)).isLE

def canonicalRawMethods
    (methods : List RawStaticMethod) : List RawStaticMethod :=
  methods.mergeSort methodLE

private def decodeOneProgram
    (limits : V3.CoreBudgetLimits)
    (state : V3.CoreBudgetState)
    (path : Path)
    (json : Lean.Json) :
    ProgramDecodeResult (V3.Program × V3.CoreBudgetState) :=
  liftCore <| V3.decodeProgramAtWithBudget limits state path json

private def decodeMethods
    (limits : V3.CoreBudgetLimits) :
    V3.CoreBudgetState → List RawStaticMethod →
      ProgramDecodeResult (List StaticMethodInput × V3.CoreBudgetState)
  | state, [] => pure ([], state)
  | state, method :: rest => do
      let (implementation, state) ← decodeOneProgram limits state
        method.implementationPath method.implementation
      let (methods, state) ← decodeMethods limits state rest
      pure ({ name := method.name, implementation } :: methods, state)

private def decodeContract
    (limits : V3.CoreBudgetLimits)
    (state : V3.CoreBudgetState)
    (contract : RawContract) :
    ProgramDecodeResult (ContractInput × V3.CoreBudgetState) := do
  match contract.spec with
  | .checkedCore json path =>
      let (program, state) ← decodeOneProgram limits state path json
      pure ({ id := contract.id, spec := .checkedCore program }, state)
  | .staticWordAbi rawMethods =>
      let (methods, state) ← decodeMethods limits state
        (canonicalRawMethods rawMethods)
      pure ({ id := contract.id, spec := .staticWordAbi methods }, state)

private def decodeContracts
    (limits : V3.CoreBudgetLimits) :
    V3.CoreBudgetState → List RawContract →
      ProgramDecodeResult (List ContractInput × V3.CoreBudgetState)
  | state, [] => pure ([], state)
  | state, contract :: rest => do
      let (contract, state) ← decodeContract limits state contract
      let (contracts, state) ← decodeContracts limits state rest
      pure (contract :: contracts, state)

def decodeScenarioPrograms
    (limits : Limits)
    (raw : RawScenario) :
    ProgramDecodeResult (Scenario × V3.CoreBudgetState) := do
  let (contracts, state) ← decodeContracts (coreLimits limits)
    .initial (canonicalRawContracts raw.contracts)
  pure ({
    contracts
    world := raw.world
    environment := raw.environment
    invocation := raw.invocation
  }, state)

def decodeQueryPrograms
    (limits : Limits)
    (raw : RawQuery) :
    ProgramDecodeResult (Query × V3.CoreBudgetState) :=
  match raw with
  | .capabilities => pure (.capabilities, .initial)
  | .coreCheck json path => do
      let (program, state) ← decodeOneProgram (coreLimits limits)
        .initial path json
      pure (.coreCheck program, state)
  | .execute rawScenario => do
      let (scenario, state) ← decodeScenarioPrograms limits rawScenario
      pure (.execute scenario, state)

def decodeRequestPrograms
    (raw : RawRequest) :
    ProgramDecodeResult (DecodedRequest × V3.CoreBudgetState) := do
  let (query, state) ← decodeQueryPrograms raw.limits raw.query
  let value : Request := { id := raw.id, limits := raw.limits, query }
  pure ({ value, limitsValid := raw.limitsValid }, state)

end Solcore.Oracle.V5.Wire
