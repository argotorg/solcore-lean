import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForState
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! The actual for-loop prelude supplies its mixed state and unchanged caller
records. Its code typing follows from the real lexical environment renaming. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)
open CellAwareInvocationForState (State)
open CellAwareLoopState (Progress)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index whole bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {type : Ty} {condition body post : Expr} {reason : Word}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {embedding : Renaming}

include transport in
theorem install
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
      mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world heap store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerAt : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩) :
    ∃ state : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      store.length type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason mapping (installedWorld world type) heap
      (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual),
    Progress model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) heap heap mapping mapping world (installedWorld world type)
      store (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual) ∧
    protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  let state := CellAwareInvocationForState.install transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  have allocation := CellAwareForAllocation.install reason heaps actualTyped actualCode
  refine ⟨state, ⟨allocation.1, .refl mapping, allocation.2.1, allocation.2.2.2.2.2.1, .refl heap,
    allocation.2.2.2.2.2.2⟩, ?_, ?_⟩
  · exact CellAwareInvocationForState.install_related transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  · exact CellAwareInvocationForState.install_records transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
