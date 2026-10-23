import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! Empty scoped flow preserves the actual mixed heap and every descriptor.
Function fallthrough is admitted only at its real Unit result type. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  (index : ActualBodyInvocation.Index compiled bodyRelation)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope) (mode : Bool)
  (expected : TypeSystem.Ty) (type : Ty)

theorem preserves (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  cases trace
  exact ⟨_, store, mapping, world,
    by simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem reflects (allowed : mode = false ∨ expected = .unit) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode [] expected type (LocalLoop.fallthrough type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  have expectedRun : Evaluates actual store ((LocalLoop.fallthrough type).rename embedding)
      (LocalLoop.fallthroughValue type) store := by
    simpa only [LoopRenaming.fallthrough] using LocalLoop.fallthrough_evaluates type actual store
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound expectedRun
  exact ⟨_, context, .fallthrough environment, before, mapping, world, .nil,
    .fallthrough environment allowed, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationEmptyFlow
