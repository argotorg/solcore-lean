import Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics

/-! The actual missing-default phase yields its own terminal receipt using
 the existing ordered-key fault producer. The phase State, live root read,
 original raw root type and same emitted token remain together. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot
universe u v
variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {Records : Type v}
  {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
  {place : PlaceResolution} {prepared : Prepared} {leaf : TypeSystem.Ty}
  {initialIndex reachedIndex : ProtectedStateTransition.Index}
  {initial : protocol.State initialIndex} {reached : protocol.State reachedIndex}
  {reason : Dynamic.SemanticFault} {token : Word}

/-- This is the same genuine phase and root read retained by MissingWitness,
 with the existing terminal receipt at that exact phase mapping and world. -/
def MissingTerminalPhase (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (place : PlaceResolution)
    (prepared : Prepared) (leaf : TypeSystem.Ty)
    {initialIndex reachedIndex : ProtectedStateTransition.Index}
    (initial : protocol.State initialIndex) (reached : protocol.State reachedIndex)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ (phaseIndex : ProtectedStateTransition.Index) (phase : protocol.State phaseIndex)
    (location : Dynamic.Location) (target : Location) (cell : Dynamic.Cell)
    (optional : Value) (root : Dynamic.Value) (value : Value)
    (path : PreparedPath checked source site cell.type place.projections
      0 prepared.steps prepared.keys leaf),
    protocol.Relates initial phase ∧ protocol.Relates phase reached ∧
    phaseIndex.scope = initialIndex.scope ∧ phaseIndex.canonical = initialIndex.canonical ∧
    reachedIndex = phaseIndex.extend phaseIndex.mapping reachedIndex.world phaseIndex.heap reachedIndex.store ∧
    WorldExtends phaseIndex.world reachedIndex.world ∧
    AdministrativePreserved phaseIndex.mapping phaseIndex.store phaseIndex.mapping reachedIndex.store ∧
    RootRead checked registry functions phaseIndex.mapping phaseIndex.world prepared phaseIndex.heap phaseIndex.store
      location target cell optional root value ∧
    cell.type = prepared.route.rootSourceType ∧
    MissingTerminal (registry := registry) functions phaseIndex.mapping phaseIndex.world path reason token

/-- Token functionality identifies the terminal produced from these actual
 ordered keys with the original getter or setter fault token. -/
theorem MissingWitness.terminal
    (witness : MissingWitness checked registry functions protocol source site place prepared leaf
      initial reached reason token) :
    MissingTerminalPhase checked registry functions protocol source site place prepared leaf
      initial reached reason token := by
  obtain ⟨phaseIndex, phase, location, target, cell, optional, root, value, keys,
    resolved, count, path, relatedIn, relatedOut, sameScope, sameCanonical,
    sameIndex, worlds, frame, read, rootType, arguments, sourceFault, receipt, _tree⟩ := witness
  obtain ⟨otherToken, otherCount, otherReceipt, _otherTree, terminal⟩ :=
    arguments.faultTree_with_terminal read.payload sourceFault prepared
  obtain ⟨sameToken, _sameCount⟩ := receipt.functional otherReceipt
  exact ⟨phaseIndex, phase, location, target, cell, optional, root, value, path,
    relatedIn, relatedOut, sameScope, sameCanonical, sameIndex, worlds, frame, read, rootType,
    sameToken.symm ▸ terminal⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceReachedDiagnostics
