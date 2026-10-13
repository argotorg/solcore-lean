import Solcore.Test.SourceCoreEvidenceMethodSupports
import Solcore.Test.SourceCoreEvidenceMethodMethodSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (bodies : MethodBodies fixture)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.MethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  exact bodies.support observed port.principal port.sourceAt ⟨port.diagnostics⟩ receiver.issued
    (headers support.toOrdinaryInventory.rows) actualRegistry

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

include receiver support bodies issued extension in
/-- Both body families are derived at the real reached metadata registry. -/
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts.preserves issued observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (StaticSupportPackage.method_supports receiver support bodies) header member selected budget

include receiver support bodies issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts.reflects issued (actualStagePrepared fixture) observed.profile
    fixture.source_wellFormed (support.toOrdinaryInventory.observations receiver)
    (static_extension receiver extension) (semantic_extension receiver support issued extension)
    support.terminals support.supports (StaticSupportPackage.method_supports receiver support bodies) rfl header member selected budget

end Tests.SourceCoreEvidenceMethod
