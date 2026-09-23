import Solcore.Oracle.V5.EnvironmentMaterialization

/-! Executable regressions for Oracle v5 immutable-environment construction. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.ContractRuntime

private def addressA : Address := ⟨1, by decide⟩
private def addressB : Address := ⟨2, by decide⟩
private def addressC : Address := ⟨3, by decide⟩
private def createdA : Address := ⟨11, by decide⟩
private def createdB : Address := ⟨12, by decide⟩
private def createdC : Address := ⟨13, by decide⟩
private def fallback : Address := ⟨99, by decide⟩

private def template1 : Word := ⟨21, by decide⟩
private def template2 : Word := ⟨22, by decide⟩
private def nonce1 : Word := ⟨31, by decide⟩
private def nonce2 : Word := ⟨32, by decide⟩
private def payload1 : Word := ⟨41, by decide⟩
private def payload2 : Word := ⟨42, by decide⟩
private def payload3 : Word := ⟨43, by decide⟩

private def programFor (payload : Word) : Program := {
  resultType := .word
  dataDefinitions := []
  body := .word payload
}

private theorem programForChecked (payload : Word) :
    (programFor payload).checkHost = true := by rfl

private def contractFor (payload : Word) : CheckedCoreContract :=
  CheckedCoreContract.returnWord {
    code := ⟨programFor payload, programForChecked payload⟩
    resultType_eq_word := rfl
  }

private def callee : CheckedCoreContract := contractFor payload1
private def initializer : CheckedCoreContract := contractFor payload2
private def runtime : CheckedCoreContract := contractFor payload3

private def resolve : String → Option CheckedCoreContract
  | "callee" => some callee
  | "initializer" => some initializer
  | "runtime" => some runtime
  | _ => none

private def validInput : EnvironmentInput := {
  callRegistry := [
    { address := addressB, contract := "callee" },
    { address := addressA, contract := "runtime" }
  ]
  creationTemplates := [
    { templateId := template2, initializer := "callee", runtime := "runtime" },
    { templateId := template1, initializer := "initializer", runtime := "runtime" }
  ]
  creationAddressPolicy := {
    routes := [
      { creator := addressB, nonce := nonce1, address := createdC },
      { creator := addressA, nonce := nonce2, address := createdB },
      { creator := addressA, nonce := nonce1, address := createdA }
    ]
    defaultAddress := fallback
  }
}

private def reorderedInput : EnvironmentInput := {
  callRegistry := validInput.callRegistry.reverse
  creationTemplates := validInput.creationTemplates.reverse
  creationAddressPolicy := {
    validInput.creationAddressPolicy with
    routes := validInput.creationAddressPolicy.routes.reverse
  }
}

private def callProgram?
    (environment : ExecutionEnvironment)
    (address : Address) : Option Program :=
  (environment.callRegistry.lookup address).map (fun contract =>
    contract.code.program)

private def templatePrograms?
    (environment : ExecutionEnvironment)
    (templateId : Word) : Option (Program × Program) := do
  let template ← environment.creationTemplates.lookup templateId
  some (template.initializer.code.program, template.runtime.code.program)

private def mismatchWorld : WorldState :=
  WorldState.empty.putAccount addressA
    (Account.empty.withCode callee.code)

private structure EnvironmentSnapshot where
  callA : Option Program
  callB : Option Program
  callC : Option Program
  template1 : Option (Program × Program)
  template2 : Option (Program × Program)
  missingTemplate : Option (Program × Program)
  routeA1 : Address
  routeA2 : Address
  routeB1 : Address
  routeDefaultNonce : Address
  routeDefaultCreator : Address
  mismatchedWorldResolutionAbsent : Bool
  deriving BEq

private def snapshot (environment : ExecutionEnvironment) : EnvironmentSnapshot := {
  callA := callProgram? environment addressA
  callB := callProgram? environment addressB
  callC := callProgram? environment addressC
  template1 := templatePrograms? environment template1
  template2 := templatePrograms? environment template2
  missingTemplate := templatePrograms? environment Word.zero
  routeA1 := environment.creationAddressPolicy.derive addressA nonce1
  routeA2 := environment.creationAddressPolicy.derive addressA nonce2
  routeB1 := environment.creationAddressPolicy.derive addressB nonce1
  routeDefaultNonce :=
    environment.creationAddressPolicy.derive addressB nonce2
  routeDefaultCreator :=
    environment.creationAddressPolicy.derive addressC nonce1
  mismatchedWorldResolutionAbsent :=
    (environment.callRegistry.resolve? mismatchWorld addressA).isNone
}

private def expectedSnapshot : EnvironmentSnapshot := {
  callA := some runtime.code.program
  callB := some callee.code.program
  callC := none
  template1 := some (initializer.code.program, runtime.code.program)
  template2 := some (callee.code.program, runtime.code.program)
  missingTemplate := none
  routeA1 := createdA
  routeA2 := createdB
  routeB1 := createdC
  routeDefaultNonce := fallback
  routeDefaultCreator := fallback
  mismatchedWorldResolutionAbsent := true
}

private def successAndOrderIndependence : Bool :=
  match EnvironmentMaterialization.materializeWith resolve validInput,
      EnvironmentMaterialization.materializeWith resolve reorderedInput with
  | .ok first, .ok second =>
      snapshot first == expectedSnapshot && snapshot first == snapshot second
  | _, _ => false

private def failure?
    (input : EnvironmentInput) : Option EnvironmentMaterializationError :=
  match EnvironmentMaterialization.materializeWith resolve input with
  | .ok _ => none
  | .error failure => some failure

private def duplicateRoute : CreationRouteInput :=
  { creator := addressA, nonce := nonce1, address := createdC }

private def duplicateCallWins : Bool :=
  failure? {
    validInput with
    callRegistry := validInput.callRegistry ++
      [{ address := addressA, contract := "missing" }]
    creationTemplates := validInput.creationTemplates ++
      [{ templateId := template1, initializer := "missing", runtime := "missing" }]
    creationAddressPolicy := {
      validInput.creationAddressPolicy with
      routes := duplicateRoute :: validInput.creationAddressPolicy.routes
    }
  } == some (.duplicateCallAddress addressA)

private def duplicateTemplateWins : Bool :=
  failure? {
    validInput with
    callRegistry := [{ address := addressA, contract := "missing" }]
    creationTemplates := validInput.creationTemplates ++
      [{ templateId := template1, initializer := "missing", runtime := "missing" }]
    creationAddressPolicy := {
      validInput.creationAddressPolicy with
      routes := duplicateRoute :: validInput.creationAddressPolicy.routes
    }
  } == some (.duplicateTemplateId template1)

private def duplicateRouteWins : Bool :=
  failure? {
    validInput with
    callRegistry := [{ address := addressA, contract := "missing" }]
    creationAddressPolicy := {
      validInput.creationAddressPolicy with
      routes := duplicateRoute :: validInput.creationAddressPolicy.routes
    }
  } == some (.duplicateCreationRoute addressA nonce1)

private def danglingCallWins : Bool :=
  failure? {
    validInput with
    callRegistry := [{ address := addressA, contract := "missing-call" }]
    creationTemplates := [{
      templateId := template1
      initializer := "missing-initializer"
      runtime := "missing-runtime"
    }]
  } == some (.danglingCallContract addressA "missing-call")

private def danglingInitializerWins : Bool :=
  failure? {
    validInput with
    creationTemplates := [{
      templateId := template1
      initializer := "missing-initializer"
      runtime := "missing-runtime"
    }]
  } == some (.danglingInitializer template1 "missing-initializer")

private def danglingRuntimeRejected : Bool :=
  failure? {
    validInput with
    creationTemplates := [{
      templateId := template1
      initializer := "initializer"
      runtime := "missing-runtime"
    }]
  } == some (.danglingRuntime template1 "missing-runtime")

private theorem canonicalOrdersAreExact :
    (EnvironmentMaterialization.canonicalCalls validInput.callRegistry).map
        (fun binding => binding.address) = [addressA, addressB] ∧
    (EnvironmentMaterialization.canonicalTemplates
        validInput.creationTemplates).map
        (fun template => template.templateId) = [template1, template2] ∧
    (EnvironmentMaterialization.canonicalRoutes
        validInput.creationAddressPolicy.routes).map
        (fun route => (route.creator, route.nonce)) =
      [(addressA, nonce1), (addressA, nonce2), (addressB, nonce1)] := by
  native_decide

private theorem compileTimeEnvironmentRegressions :
    successAndOrderIndependence = true ∧
      duplicateCallWins = true ∧
      duplicateTemplateWins = true ∧
      duplicateRouteWins = true ∧
      danglingCallWins = true ∧
      danglingInitializerWins = true ∧
      danglingRuntimeRejected = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testOracleV5EnvironmentMaterialization : IO Unit := do
  assertTrue successAndOrderIndependence
    "Oracle v5 environment lookup or canonical order changed"
  assertTrue (duplicateCallWins && duplicateTemplateWins && duplicateRouteWins)
    "Oracle v5 environment duplicate precedence changed"
  assertTrue (danglingCallWins && danglingInitializerWins &&
    danglingRuntimeRejected)
    "Oracle v5 environment dangling-reference precedence changed"

end Tests
