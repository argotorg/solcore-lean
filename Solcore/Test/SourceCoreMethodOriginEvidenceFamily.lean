import Solcore.Test.SourceCoreMethodOriginEvidenceSupports
import Solcore.Test.SourceCoreMethodOriginEvidenceClosureSupport
import Solcore.Test.SourceCoreMethodOriginEvidenceCommon
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ receiver.issued
    support.toOrdinaryInventory actualRegistry

include support in
private theorem owners_physical : ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys fixture.recipe.compiled),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers support.toOrdinaryInventory.rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner fixture.recipe.compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver extension in
private theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial fixture.recipe.compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends fixture.recipe.compiled.compatible.checked.staticRegistry _
  rw [← receiver.registry]
  exact extension

include receiver support issued extension in
private theorem semantic_extension : ∀ reason token, initialFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present, _⟩ := support.wordHeader.diagnostic.actual
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
    receiver.issued issued present extension represented

include receiver support sources bodies methods issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  intro mapping world administrative actualContext environment canonical actual before store ξ
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.bodies support.supports (fun association => (chosen association).1)
    (fun association => (chosen association).2) (owners_physical receiver support)
    (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreMethodOriginEvidence
