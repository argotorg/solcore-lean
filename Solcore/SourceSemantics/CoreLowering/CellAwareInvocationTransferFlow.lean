import Solcore.SourceSemantics.Staging.RecursiveControlViews
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! Loop transfer leaves the actual mixed heap and all generalized descriptors intact.
The source occurrence authenticates the selected break or continue statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
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


variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem breaking_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.breaking_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.breaking_evaluates type actual store,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem breaking_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.breaking type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.breaking_evaluates type actual store)
  exact ⟨_, context, .breaking environment, before, mapping, world,
    .breaking (lookupStatement?_sound found) form,
    .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

variable {id : StatementId} {node : StatementNode} {rest : List StatementId}

theorem continuing_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.continuing_view unique found form trace
  exact ⟨_, store, mapping, world,
    LocalLoop.continuing_evaluates type actual store,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

theorem continuing_reflects
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) expected type (LocalLoop.continuing type) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _typed
    initial admitted _authority _physical _owner _sameLocation _ready completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.continuing_evaluates type actual store)
  exact ⟨_, context, .continuing environment, before, mapping, world,
    .continuing (lookupStatement?_sound found) form,
    .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
    .refl _ _ _ _, initial, protocol.refl initial, admitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTransferFlow
