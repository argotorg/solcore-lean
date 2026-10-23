import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForIterations
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForEntry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! The real for-loop prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {testCode loopCode postCode : Expr} {postItems : List ForItemForm}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)

include bridge model producer transport booleans in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context postItems final)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before test postItems statements outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareInvocationForEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  rw [LoopRenaming.iterate] at completed
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := completed.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress,
      reached, related, post⟩ :=
    CellAwareInvocationForIterations.reflects bridge model producer
      children found nodeType typed generated correct postCorrect agrees booleans runtime covers sameLedger bodyTyped postTyped entrySize
      (Nat.le_trans (Nat.le_of_lt entrySmaller) within) protectedState activated nativeEntry
  have total := installedProgress.trans progress
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    total.heaps, total.maps, total.worlds, total.preserved, total.metadata, total.effect,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

include bridge model producer transport booleans in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context postItems final)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.ForLoop program stages size invocation context environment before test postItems statements outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareInvocationForEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress,
      reached, related, post⟩ :=
    CellAwareInvocationForIterations.preserves bridge model producer
      children found nodeType typed generated correct postCorrect agrees booleans runtime covers sameLedger bodyTyped postTyped size within protectedState activated trace
  have total := installedProgress.trans progress
  exact ⟨value, finalStore, finalMap, finalWorld,
    by
      rw [LoopRenaming.iterate]
      apply LocalLoop.iterate_evaluates
      apply LocalLoop.invoke_success _ _ (.var rfl) _ nativeTrace
      exact protectedState.selfRead,
    represented, total.heaps, total.maps, total.worlds, total.preserved, total.metadata, total.effect,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForHeads
