import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension

/-! Static coverage of the actual named, closure and method bodies supplies both
semantic directions at every reached public receiver. A successful compilation
does not by itself supply this coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)

theorem stagePrepared (compiled : SourceCoreUnifiedCompilation.Compiled) :
    RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected

def stages (compiled : SourceCoreUnifiedCompilation.Compiled) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry (stagePrepared compiled)

/-- Every support field retains an actual compiler packet or original Source.
The body laws follow from the closed physical family below. -/
structure Support (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed) where
  profile : compiled.compatible.checked.catalog.callableContracts = true
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  issued : IssuedAt compiled.indexed initial.entry initial.result.context.registry
    initial.result.extension initial.result.diagnostics
  registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program
  bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header
  bodySupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := initial.result.context.registry)
      (stages := stages compiled)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      header (bodies header member)
  closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor association.original (stages compiled)
  closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original
      (stages compiled) (closurePackets association)
  owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers
  methods : CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
    (compiled := compiled) (headers := headers) (stages := stages compiled)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}

def functions (support : Support compiled headers keys initial) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions headers keys initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) support.profile

theorem observations (support : Support compiled headers keys initial) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions support) (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
    support.profile (registry := metadata)
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general support.profile origin)

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include support extension in
theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry _
  rw [← support.registry]
  exact extension

include support issued extension in
theorem semantic_extension : ∀ reason token,
    CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present⟩ := support.diagnostics
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved compiled
    support.issued issued present extension represented

include support issued extension in
theorem preserves_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods
    issued (stagePrepared compiled) support.profile support.wellFormed (observations support)
    (static_extension support extension) (semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
    header member selected budget

include support issued extension in
theorem reflects_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods
    issued (stagePrepared compiled) support.profile support.wellFormed (observations support)
    (static_extension support extension) (semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
    rfl header member selected budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
