import Solcore.Test.SourceCoreCoercionPublicSupports
import Solcore.Test.SourceCoreCoercionPublicClosureSupport
import Solcore.Test.SourceCoreCoercionPublicCommon
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalBootstrap
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  (receiver : ObservedReceiver fixture observed)
  (support : StaticSupportPackage fixture observed receiver.completion)
  (sources : ObservedClosureSources fixture observed)
  (bodies : MethodBodies fixture)
  (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)

local notation "actualRegistry" => RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)
local notation "initialFaults" => CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics
local notation "functions" => support.toOrdinaryInventory.functions receiver

include receiver support bodies in
theorem StaticSupportPackage.method_supports :
    CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
      (compiled := fixture.recipe.compiled) (headers := headers support.toOrdinaryInventory.rows)
      (stages := actualRegistry) (semanticFaults := initialFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  obtain ⟨packet, same, supported⟩ := bodies.support observed port.principal port.sourceAt
    ⟨port.diagnostics⟩ receiver.issued (headers := headers support.toOrdinaryInventory.rows) actualRegistry
  exact ⟨.terminal packet, same, supported⟩

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

include sources bodies methods in
/-- The actual compiler packets supply the shared public program support. -/
theorem StaticSupportPackage.program_support :
    Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled) receiver.completion) := by
  let chosen := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association
      (headers support.toOrdinaryInventory.rows) (keys fixture.recipe.compiled)
      receiver.completion.result.context.registry initialFaults
      mapping world function native bindings parameter result) =>
    Classical.choice (closure_support observed sources bodies support.toOrdinaryInventory
      (actualStagePrepared fixture) receiver.issued methods association)
  exact ⟨{
    profile := observed.profile
    wellFormed := fixture.source_wellFormed
    issued := receiver.issued
    registry := receiver.registry
    diagnostics := by
      obtain ⟨program, present, _⟩ := support.makeHeader.diagnostic.actual
      exact ⟨program, present⟩
    bodies := support.bodies
    bodySupport := support.supports
    closurePackets := fun association => (chosen association).1
    closureSupport := fun association => (chosen association).2
    owners := owners_physical receiver support
    methods := StaticSupportPackage.method_supports receiver support bodies }⟩

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry)

include receiver support sources bodies methods issued extension in
theorem preserves_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support sources bodies methods
  exact CallableIndexedOwnedPreparedPhysicalProgramSupport.preserves_bodies
    program issued extension header member selected budget

include receiver support sources bodies methods issued extension in
theorem reflects_bodies (header) (member : header ∈ headers support.toOrdinaryInventory.rows)
    {child : Staging.Recursive.Scope} (selected : (actualRegistry).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers support.toOrdinaryInventory.rows) (keys := keys fixture.recipe.compiled) header
      (CompatibleAmbientHeap.payloadModel fixture.recipe.compiled.compatible.checked receiving.result.context.registry functions)
      actualRegistry child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support sources bodies methods
  exact CallableIndexedOwnedPreparedPhysicalProgramSupport.reflects_bodies
    program issued extension header member selected budget

end Tests.SourceCoreCoercionPublic
