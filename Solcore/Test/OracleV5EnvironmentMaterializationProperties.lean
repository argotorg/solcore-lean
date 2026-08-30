import Solcore.Oracle.V5.EnvironmentMaterialization

/-! External-consumer checks for immutable-environment materialization laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.Semantics

private theorem exactEnvironmentProvenance
    (resolve : String → Option CheckedCoreContract)
    (input : EnvironmentInput)
    (environment : ExecutionEnvironment)
    (success :
      EnvironmentMaterialization.materializeWith resolve input =
        .ok environment)
    (callAddress absentCallAddress : Address)
    (binding : CallRegistryInput)
    (callSelected :
      EnvironmentMaterialization.callInput? input callAddress = some binding)
    (callAbsent :
      EnvironmentMaterialization.callInput? input absentCallAddress = none)
    (templateId absentTemplateId : Word)
    (template : CreationTemplateInput)
    (templateSelected :
      EnvironmentMaterialization.templateInput? input templateId =
        some template)
    (templateAbsent :
      EnvironmentMaterialization.templateInput? input absentTemplateId = none)
    (creator absentCreator : Address)
    (nonce absentNonce : Word)
    (route : CreationRouteInput)
    (routeSelected :
      EnvironmentMaterialization.routeInput? input creator nonce = some route)
    (routeAbsent :
      EnvironmentMaterialization.routeInput? input absentCreator absentNonce =
        none) :
    environment.callRegistry.lookup callAddress = resolve binding.contract ∧
    environment.callRegistry.lookup absentCallAddress = none ∧
    environment.creationTemplates.lookup templateId = (do
      let initializer ← resolve template.initializer
      let runtime ← resolve template.runtime
      some { initializer, runtime }) ∧
    environment.creationTemplates.lookup absentTemplateId = none ∧
    environment.creationAddressPolicy.derive creator nonce = route.address ∧
    environment.creationAddressPolicy.derive absentCreator absentNonce =
      input.creationAddressPolicy.defaultAddress := by
  constructor
  · exact EnvironmentMaterialization.callRegistry_lookup_of_input resolve
      input environment success callAddress binding callSelected
  constructor
  · exact
      EnvironmentMaterialization.callRegistry_lookup_eq_none_of_input_absent
        resolve input environment success absentCallAddress callAbsent
  constructor
  · exact EnvironmentMaterialization.creationTemplates_lookup_of_input
      resolve input environment success templateId template templateSelected
  constructor
  · exact
      EnvironmentMaterialization.creationTemplates_lookup_eq_none_of_input_absent
        resolve input environment success absentTemplateId templateAbsent
  constructor
  · exact EnvironmentMaterialization.creationAddressPolicy_derive_of_input
      resolve input environment success creator nonce route routeSelected
  · exact
      EnvironmentMaterialization.creationAddressPolicy_derive_of_input_absent
        resolve input environment success absentCreator absentNonce routeAbsent

def testOracleV5EnvironmentMaterializationProperties : IO Unit := do
  let _ := exactEnvironmentProvenance
  pure ()

end Tests
