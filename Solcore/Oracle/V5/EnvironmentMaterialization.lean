import Solcore.Oracle.V5.Input
import Solcore.Semantics.ExecutionEnvironment

/-! Canonical validation and materialization of the Oracle v5 environment. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5

open Solcore.Semantics

/-- Closed semantic failures produced by immutable-environment validation. -/
inductive EnvironmentMaterializationError where
  | duplicateCallAddress (address : Address)
  | duplicateTemplateId (templateId : Core.Word)
  | duplicateCreationRoute (creator : Address) (nonce : Core.Word)
  | danglingCallContract (address : Address) (id : String)
  | danglingInitializer (templateId : Core.Word) (id : String)
  | danglingRuntime (templateId : Core.Word) (id : String)
  deriving Repr, BEq, DecidableEq

namespace EnvironmentMaterialization

private def callLE (left right : CallRegistryInput) : Bool :=
  (compare left.address.val right.address.val).isLE

/-- Canonical call bindings use increasing unsigned Address value. -/
def canonicalCalls
    (bindings : List CallRegistryInput) : List CallRegistryInput :=
  bindings.mergeSort callLE

private def templateLE
    (left right : CreationTemplateInput) : Bool :=
  (compare left.templateId.val right.templateId.val).isLE

/-- Canonical templates use increasing unsigned Word identifier value. -/
def canonicalTemplates
    (templates : List CreationTemplateInput) : List CreationTemplateInput :=
  templates.mergeSort templateLE

private def routeLE
    (left right : CreationRouteInput) : Bool :=
  match compare left.creator.val right.creator.val with
  | .lt => true
  | .gt => false
  | .eq => (compare left.nonce.val right.nonce.val).isLE

/-- Canonical routes use `(creator, nonce)` lexicographic order. -/
def canonicalRoutes
    (routes : List CreationRouteInput) : List CreationRouteInput :=
  routes.mergeSort routeLE

private def firstDuplicateCall? :
    List CallRegistryInput → Option Address
  | []
  | [_] => none
  | first :: second :: rest =>
      if first.address = second.address then
        some first.address
      else
        firstDuplicateCall? (second :: rest)

private def firstDuplicateTemplate? :
    List CreationTemplateInput → Option Core.Word
  | []
  | [_] => none
  | first :: second :: rest =>
      if first.templateId = second.templateId then
        some first.templateId
      else
        firstDuplicateTemplate? (second :: rest)

private def firstDuplicateRoute? :
    List CreationRouteInput → Option (Address × Core.Word)
  | []
  | [_] => none
  | first :: second :: rest =>
      if first.creator = second.creator ∧ first.nonce = second.nonce then
        some (first.creator, first.nonce)
      else
        firstDuplicateRoute? (second :: rest)

private def firstDanglingCall?
    (resolve : String → Option CheckedCoreContract) :
    List CallRegistryInput → Option (Address × String)
  | [] => none
  | binding :: rest =>
      if (resolve binding.contract).isSome then
        firstDanglingCall? resolve rest
      else
        some (binding.address, binding.contract)

private def firstDanglingInitializer?
    (resolve : String → Option CheckedCoreContract) :
    List CreationTemplateInput → Option (Core.Word × String)
  | [] => none
  | template :: rest =>
      if (resolve template.initializer).isSome then
        firstDanglingInitializer? resolve rest
      else
        some (template.templateId, template.initializer)

private def firstDanglingRuntime?
    (resolve : String → Option CheckedCoreContract) :
    List CreationTemplateInput → Option (Core.Word × String)
  | [] => none
  | template :: rest =>
      if (resolve template.runtime).isSome then
        firstDanglingRuntime? resolve rest
      else
        some (template.templateId, template.runtime)

/-- Canonical input retained after every environment constraint succeeds. -/
structure CanonicalInput where
  calls : List CallRegistryInput
  templates : List CreationTemplateInput
  routes : List CreationRouteInput
  defaultAddress : Address
  deriving Repr, BEq, DecidableEq

/-- Validate with the exact v5 duplicate-before-reference precedence. -/
def validateWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput) :
    Except EnvironmentMaterializationError CanonicalInput :=
  let calls := canonicalCalls input.callRegistry
  let templates := canonicalTemplates input.creationTemplates
  let routes := canonicalRoutes input.creationAddressPolicy.routes
  match firstDuplicateCall? calls with
  | some address => .error (.duplicateCallAddress address)
  | none =>
      match firstDuplicateTemplate? templates with
      | some templateId => .error (.duplicateTemplateId templateId)
      | none =>
          match firstDuplicateRoute? routes with
          | some (creator, nonce) =>
              .error (.duplicateCreationRoute creator nonce)
          | none =>
              match firstDanglingCall? resolve calls with
              | some (address, id) =>
                  .error (.danglingCallContract address id)
              | none =>
                  match firstDanglingInitializer? resolve templates with
                  | some (templateId, id) =>
                      .error (.danglingInitializer templateId id)
                  | none =>
                      match firstDanglingRuntime? resolve templates with
                      | some (templateId, id) =>
                          .error (.danglingRuntime templateId id)
                      | none => .ok {
                          calls
                          templates
                          routes
                          defaultAddress :=
                            input.creationAddressPolicy.defaultAddress
                        }

private def callRegistryWith
    (resolve : String → Option CheckedCoreContract)
    (calls : List CallRegistryInput) : CheckedContractRegistry := {
  lookup := fun address => do
    let binding ← calls.find? (fun entry => decide (entry.address = address))
    resolve binding.contract
}

private def templateRegistryWith
    (resolve : String → Option CheckedCoreContract)
    (templates : List CreationTemplateInput) :
    CheckedCreationTemplateRegistry := {
  lookup := fun templateId => do
    let template ← templates.find?
      (fun entry => decide (entry.templateId = templateId))
    let initializer ← resolve template.initializer
    let runtime ← resolve template.runtime
    some { initializer, runtime }
}

private def addressPolicyWith
    (routes : List CreationRouteInput)
    (defaultAddress : Address) : CreationAddressPolicy := {
  derive := fun creator nonce =>
    match routes.find? (fun route =>
        decide (route.creator = creator ∧ route.nonce = nonce)) with
    | some route => route.address
    | none => defaultAddress
}

/-- Materialize all immutable execution capabilities after canonical validation. -/
def materializeWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput) :
    Except EnvironmentMaterializationError ExecutionEnvironment := do
  let canonical ← validateWith resolve input
  .ok {
    callRegistry := callRegistryWith resolve canonical.calls
    creationTemplates := templateRegistryWith resolve canonical.templates
    creationAddressPolicy :=
      addressPolicyWith canonical.routes canonical.defaultAddress
  }

end EnvironmentMaterialization

end Solcore.Oracle.V5
