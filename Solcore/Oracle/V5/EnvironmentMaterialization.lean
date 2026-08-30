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

/-- Select the unique canonical nested-call binding for an Address. -/
def callInput?
    (input : EnvironmentInput)
    (address : Address) : Option CallRegistryInput :=
  (canonicalCalls input.callRegistry).find?
    (fun binding => decide (binding.address = address))

/-- Select the unique canonical creation template for a Word identifier. -/
def templateInput?
    (input : EnvironmentInput)
    (templateId : Core.Word) : Option CreationTemplateInput :=
  (canonicalTemplates input.creationTemplates).find?
    (fun template => decide (template.templateId = templateId))

/-- Select the unique canonical creation route for `(creator, nonce)`. -/
def routeInput?
    (input : EnvironmentInput)
    (creator : Address)
    (nonce : Core.Word) : Option CreationRouteInput :=
  (canonicalRoutes input.creationAddressPolicy.routes).find?
    (fun route => decide (
      route.creator = creator ∧ route.nonce = nonce))

/-- Exact checked contract named by one finite call-registry lookup. -/
def callContractWith?
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (address : Address) : Option CheckedCoreContract := do
  let binding ← callInput? input address
  resolve binding.contract

/-- Exact checked initializer/runtime pair named by one finite template. -/
def creationTemplateWith?
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (templateId : Core.Word) : Option CheckedCreationTemplate := do
  let template ← templateInput? input templateId
  let initializer ← resolve template.initializer
  let runtime ← resolve template.runtime
  some { initializer, runtime }

/-- Total creation Address selected by a finite route or its explicit default. -/
def creationAddressOf
    (input : EnvironmentInput)
    (creator : Address)
    (nonce : Core.Word) : Address :=
  match routeInput? input creator nonce with
  | some route => route.address
  | none => input.creationAddressPolicy.defaultAddress

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

private theorem validateWith_ok_eq_canonicalInput
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (canonical : CanonicalInput)
    (accepted : validateWith resolve input = .ok canonical) :
    canonical = {
      calls := canonicalCalls input.callRegistry
      templates := canonicalTemplates input.creationTemplates
      routes := canonicalRoutes input.creationAddressPolicy.routes
      defaultAddress := input.creationAddressPolicy.defaultAddress
    } := by
  unfold validateWith at accepted
  dsimp only at accepted
  repeat first | split at accepted | simp_all

private theorem environment_eq_of_materializeWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment) :
    environment = {
      callRegistry :=
        callRegistryWith resolve (canonicalCalls input.callRegistry)
      creationTemplates :=
        templateRegistryWith resolve
          (canonicalTemplates input.creationTemplates)
      creationAddressPolicy :=
        addressPolicyWith
          (canonicalRoutes input.creationAddressPolicy.routes)
          input.creationAddressPolicy.defaultAddress
    } := by
  cases accepted : validateWith resolve input with
  | error failure =>
      unfold materializeWith at success
      simp only [accepted, bind, Except.bind] at success
      cases success
  | ok canonical =>
      have exactCanonical := validateWith_ok_eq_canonicalInput
        resolve input canonical accepted
      subst canonical
      unfold materializeWith at success
      simp only [accepted, bind, Except.bind, Except.ok.injEq] at success
      exact success.symm

/-- Every successful environment has exactly the finite call-registry lookup. -/
theorem callRegistry_lookup_of_materializeWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (address : Address) :
    environment.callRegistry.lookup address =
      callContractWith? resolve input address := by
  rw [environment_eq_of_materializeWith resolve input environment success]
  rfl

/-- A selected call binding resolves to exactly its named checked contract. -/
theorem callRegistry_lookup_of_input
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (address : Address)
    (binding : CallRegistryInput)
    (selected : callInput? input address = some binding) :
    environment.callRegistry.lookup address = resolve binding.contract := by
  rw [callRegistry_lookup_of_materializeWith resolve input environment
    success address]
  simp [callContractWith?, selected]

/-- No finite call binding means no checked contract registry entry. -/
theorem callRegistry_lookup_eq_none_of_input_absent
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (address : Address)
    (absent : callInput? input address = none) :
    environment.callRegistry.lookup address = none := by
  rw [callRegistry_lookup_of_materializeWith resolve input environment
    success address]
  simp [callContractWith?, absent]

/-- Every successful environment has exactly the finite template lookup. -/
theorem creationTemplates_lookup_of_materializeWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (templateId : Core.Word) :
    environment.creationTemplates.lookup templateId =
      creationTemplateWith? resolve input templateId := by
  rw [environment_eq_of_materializeWith resolve input environment success]
  rfl

/-- A selected template preserves its exact initializer/runtime provenance. -/
theorem creationTemplates_lookup_of_input
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (templateId : Core.Word)
    (template : CreationTemplateInput)
    (selected : templateInput? input templateId = some template) :
    environment.creationTemplates.lookup templateId = (do
      let initializer ← resolve template.initializer
      let runtime ← resolve template.runtime
      some { initializer, runtime }) := by
  rw [creationTemplates_lookup_of_materializeWith resolve input environment
    success templateId]
  simp [creationTemplateWith?, selected]

/-- No finite template entry means no checked creation capability. -/
theorem creationTemplates_lookup_eq_none_of_input_absent
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (templateId : Core.Word)
    (absent : templateInput? input templateId = none) :
    environment.creationTemplates.lookup templateId = none := by
  rw [creationTemplates_lookup_of_materializeWith resolve input environment
    success templateId]
  simp [creationTemplateWith?, absent]

/-- Every successful environment has exactly the finite total Address policy. -/
theorem creationAddressPolicy_derive_of_materializeWith
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (creator : Address)
    (nonce : Core.Word) :
    environment.creationAddressPolicy.derive creator nonce =
      creationAddressOf input creator nonce := by
  rw [environment_eq_of_materializeWith resolve input environment success]
  rfl

/-- A selected creation route preserves its exact output Address. -/
theorem creationAddressPolicy_derive_of_input
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (creator : Address)
    (nonce : Core.Word)
    (route : CreationRouteInput)
    (selected : routeInput? input creator nonce = some route) :
    environment.creationAddressPolicy.derive creator nonce = route.address := by
  rw [creationAddressPolicy_derive_of_materializeWith resolve input environment
    success creator nonce]
  simp [creationAddressOf, selected]

/-- A missing route selects exactly the input's required default Address. -/
theorem creationAddressPolicy_derive_of_input_absent
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success : materializeWith resolve input = .ok environment)
    (creator : Address)
    (nonce : Core.Word)
    (absent : routeInput? input creator nonce = none) :
    environment.creationAddressPolicy.derive creator nonce =
      input.creationAddressPolicy.defaultAddress := by
  rw [creationAddressPolicy_derive_of_materializeWith resolve input environment
    success creator nonce]
  simp [creationAddressOf, absent]

end EnvironmentMaterialization

end Solcore.Oracle.V5
