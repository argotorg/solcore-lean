import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.Loops
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedWhileReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileEdges
import Solcore.SourceSemantics.CoreLowering.LoopCoreInversion
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationForLoops
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
import Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotHead
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping

/-!
# Cell-aware invocations: loops

`while` loops in one actual body invocation, and the loop heads and sequences that `for` shares with them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopState
/-! A live loop carries its actual self closure, the mixed Source heap and the
same caller frame. Child computation keeps its reached protocol state while
transporting every generalized descriptor through its concrete effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
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

structure State (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (administrative actualContext : Core.Context) (environment : Dynamic.Environment)
    (canonical actual : Environment) (location : Location) (type : Ty)
    (condition body : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions
  heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions
  authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
    bodyIndex.owner bodyIndex.active mapping world heap store environment
  physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  ownerAt : owner.key.frameLocation = physical.location
  ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body (LocalLoop.fallthrough type) reason location actual))
  selfUnmapped : location ∉ mapping
  retained : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩

variable {producer} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {location : Location} {type : Ty}
  {condition body : Expr} {reason : Word}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

/-- Retain the exact child post-state, rather than reconstructing an unrelated
state with the same heap. The loop's recursive closure remains unchanged. -/
def State.reach
    (state : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type condition body reason mapping world heap store)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) nextMap nextWorld after finalStore)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
      mapping world heap store nextMap nextWorld after finalStore)
    (frame : AdministrativePreserved mapping store nextMap finalStore)
    (reached : protocol.State ⟨scope,nextMap,nextWorld,after,finalStore,canonical⟩) :
    State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type condition body reason nextMap nextWorld after finalStore :=
  { environments := state.environments.extend effect.maps effect.worlds,
    heaps := heaps, locals := state.locals.mono effect.metadata, actualTyped := state.actualTyped.weaken effect.worlds,
    authority := state.authority.transport effect, physical := state.physical.transport effect frame,
    owner := state.owner, ownerAt := state.ownerAt, ready := state.ready,
    selfTyped := effect.worlds.lookup state.selfTyped,
    selfRead := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).2,
    selfUnmapped := (TypedLexicalWhile.retain state.selfUnmapped state.selfRead frame).1,
    retained := reached }

variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment)
    bodyIndex.owner bodyIndex.active mapping world heap store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) whole bodyIndex context scope canonical mapping world heap store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerAt : owner.key.frameLocation = physical.location)
  (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
  (typed : HasType actualContext (LocalLoop.whileLoop type condition body reason)
    (LocalLoop.resultType type) whole.indexed.layouts.definitions)
  (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩)

/-- Installing the real while self cell changes only administrative storage. -/
def install : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
    store.length type condition body reason mapping (installedWorld world type) heap
    (installedStore store type condition body (LocalLoop.fallthrough type) reason actual) := by
  have allocation := CellAwareLoopAllocation.install reason heaps actualTyped typed
  have worlds := allocation.2.1
  have frame := allocation.2.2.2.2.2.1
  have effect := allocation.2.2.2.2.2.2
  exact {
    environments := environments.extend (.refl mapping) worlds,
    heaps := allocation.1, locals := locals, actualTyped := actualTyped.weaken worlds,
    authority := authority.transport effect, physical := physical.transport effect frame,
    owner := owner, ownerAt := ownerAt, ready := ready,
    selfTyped := allocation.2.2.2.1, selfRead := allocation.2.2.2.2.1,
    selfUnmapped := allocation.2.2.1,
    retained := transport.extend initial (.refl mapping) worlds frame (.refl heap) }

theorem install_related : protocol.Relates initial
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained := by
  unfold install
  apply transport.related

theorem install_records : protocol.records
    (install transport environments heaps locals actualTyped authority physical owner ownerAt ready typed initial).retained =
    protocol.records initial := by
  unfold install
  apply transport.records_eq

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEdges
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEdges
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

theorem condition_preserves_at {size : Nat}
    (meaning : CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    meaning tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt trace
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    reflection tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩



theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected outcome reached.retained := by
  have bodyAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)))
      canonical (Core.LoopExecution.bodyEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit) (.bool true)
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals bodyAgrees
      (.cons .bool (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)))
      runtime covers sameLedger typed state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
        Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopIterations
/-! Repeated actual while steps preserve every generalized descriptor and
the installed recursive closure. Native completion reconstructs the independent
Source iteration trace, including faults, break, continue and early return. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopIterations
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

open CellAwareInvocationLoopEdges
variable {condition : ExpressionId} {node : ExpressionNode}
  {statements : List StatementId} {expected : TypeSystem.Ty}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (LocalLoop.fallthrough type) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.While program stages sourceSize invocation context environment before condition statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before store finalStore value state ready evaluation
    obtain ⟨conditionSize, conditionStore, conditionValue, conditionSmaller, conditionEval⟩ := evaluation.bind_computation
    obtain ⟨conditionSourceSize, conditionOutcome, conditionHeap, conditionMap, conditionWorld,
        conditionTrace, conditionRelated, conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
      condition_reflects_at bridge model producer (children _ (Nat.lt_of_lt_of_le conditionSmaller bounded))
        tree found typed agrees state ready conditionEval
    cases conditionRelated with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_failure conditionEval.sound)
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .conditionFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
      subst sameSource
      subst sameCore
      cases boolean with
      | false =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .done conditionTrace, .fallthrough environment (.inl rfl),
          conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
      | true =>
        obtain ⟨branchSize, branchSmaller, branch⟩ := evaluation.loop_true_branch conditionEval.sound
        obtain ⟨bodySize, bodyStore, bodyValue, bodySmaller, bodyEval⟩ := branch.bind_computation
        obtain ⟨bodySourceSize, bodyContext, bodyOutcome, bodyHeap, bodyMap, bodyWorld, bodyTrace,
            bodyRelated, bodyProgress, bodyState, bodyRetained, bodyPost⟩ :=
          body_reflects_at bridge model producer correct
            (Nat.le_trans (Nat.le_of_lt bodySmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
            agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyEval
        have progress := conditionProgress.trans bodyProgress
        cases bodyRelated with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_failure conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .bodyFault conditionTrace bodyTrace, .fault matched,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | returned payload =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .returned conditionTrace bodyTrace, .returned payload,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | fallthrough innerEnvironment allowed =>
          obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_fallthrough bodyEval.sound bodyState.selfRead
          obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
              finalState, finalRetained, finalPost⟩ :=
            ih nextSize (Nat.lt_trans smaller branchSmaller)
              (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) bodyState bodyPost nextEval
          exact ⟨_, _, after, finalMap, finalWorld, .next conditionTrace bodyTrace nextTrace, related,
            progress.trans nextProgress, finalState, callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

        | breaking innerEnvironment =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .breakFromBody conditionTrace bodyTrace,
            .fallthrough environment (.inl rfl), progress, bodyState,
            callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | continuing innerEnvironment =>
          obtain ⟨nextSize, smaller, nextEval⟩ := branch.loop_next_continuing bodyEval.sound bodyState.selfRead
          obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
              finalState, finalRetained, finalPost⟩ :=
            ih nextSize (Nat.lt_trans smaller branchSmaller)
              (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) bodyState bodyPost nextEval
          exact ⟨_, _, after, finalMap, finalWorld, .continueNext conditionTrace bodyTrace nextTrace, related,
            progress.trans nextProgress, finalState, callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type code budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (bodyIndex.source))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = bodyIndex.compilation.solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      Staging.Recursive.Size.While program stages size invocation context environment before condition statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Core.LoopExecution.WhileTrace type (conditionCode.rename ξ) (code.rename ξ) selfReason location actual store value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareInvocationLoopState.State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state ready trace
    cases trace with
    | done testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          exact ⟨_, conditionStore, conditionMap, conditionWorld, .done conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | conditionFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, .conditionFault conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returned testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | returned payload =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .returns conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | breakFromBody testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | breaking innerEnvironment =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .breaks conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFault testTrace bodyTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fault matched =>
            exact ⟨_, bodyStore, bodyMap, bodyWorld, .bodyFault conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | next testTrace bodyTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | fallthrough innerEnvironment allowed =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                finalState, finalRetained, finalPost⟩ :=
              ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                bodyState bodyPost next
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextFallthrough conditionEval bodyEval bodyState.selfRead nativeTrace,
              related, progress.trans finalProgress, finalState,
              callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

    | continueNext testTrace bodyTrace next =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | value payload =>
          rw [nodeType] at payload
          obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
          cases sameSource
          subst sameCore
          obtain ⟨bodyValue, bodyStore, bodyMap, bodyWorld, bodyEval, bodyRelated, bodyProgress,
              bodyState, bodyRetained, bodyPost⟩ :=
            body_preserves_at bridge model producer correct
              (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
              agrees conditionState runtime covers sameLedger bodyTyped conditionPost.at_value.2 bodyTrace
          cases bodyRelated with
          | continuing innerEnvironment =>
            have progress := conditionProgress.trans bodyProgress
            obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                finalState, finalRetained, finalPost⟩ :=
              ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                bodyState bodyPost next
            exact ⟨result, finalStore, finalMap, finalWorld,
              .nextContinue conditionEval bodyEval bodyState.selfRead nativeTrace,
              related, progress.trans finalProgress, finalState,
              callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopIterations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEntry
/-! The actual while prelude supplies its mixed state and unchanged caller
records. Its code typing follows from the real lexical environment renaming. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)
open CellAwareInvocationLoopState (State)
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
  {canonical actual : Environment} {type : Ty} {condition body : Expr} {reason : Word}
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
      (LocalLoop.whileLoop type condition body reason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩) :
    ∃ state : State (bodyIndex := bodyIndex) producer context scope administrative actualContext environment canonical actual
      store.length type (condition.rename embedding) (body.rename embedding) reason mapping (installedWorld world type) heap
      (installedStore store type (condition.rename embedding) (body.rename embedding) (LocalLoop.fallthrough type) reason actual),
    Progress model (GeneralizedLocalAcceptedInstances.modelWith whole.indexed attachment) heap heap mapping mapping world (installedWorld world type)
      store (installedStore store type (condition.rename embedding) (body.rename embedding) (LocalLoop.fallthrough type) reason actual) ∧
    protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.whileLoop] at actualCode
  let state := CellAwareInvocationLoopState.install transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  have allocation := CellAwareLoopAllocation.install reason heaps actualTyped actualCode
  refine ⟨state, ⟨allocation.1, .refl mapping, allocation.2.1, allocation.2.2.2.2.2.1, .refl heap,
    allocation.2.2.2.2.2.2⟩, ?_, ?_⟩
  · exact CellAwareInvocationLoopState.install_related transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  · exact CellAwareInvocationLoopState.install_records transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopHeads
/-! The real while prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopHeads
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
  {expected : TypeSystem.Ty} {testCode loopCode : Expr}
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
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
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
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.whileLoop type testCode loopCode selfReason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.While program stages sourceSize invocation context environment before test statements outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareInvocationLoopEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedWhileReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  rw [LoopRenaming.whileLoop] at completed
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := completed.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress,
      reached, related, post⟩ :=
    CellAwareInvocationLoopIterations.reflects bridge model producer
      children found nodeType typed generated correct agrees booleans runtime covers sameLedger bodyTyped entrySize
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
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
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
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.While program stages size invocation context environment before test statements outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.whileLoop type testCode loopCode selfReason).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareInvocationLoopEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedWhileReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress,
      reached, related, post⟩ :=
    CellAwareInvocationLoopIterations.preserves bridge model producer
      children found nodeType typed generated correct agrees booleans runtime covers sameLedger bodyTyped size within protectedState activated trace
  have total := installedProgress.trans progress
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [LoopRenaming.whileLoop] using nativeTrace.whileLoop_evaluates,
    represented, total.heaps, total.maps, total.worlds, total.preserved, total.metadata, total.effect,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopSequences
/-! The real while prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopSequences
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
  {expected : TypeSystem.Ty} {testCode loopCode : Expr}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)

variable {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId}
  (sourceEq : invocation.source = bodyIndex.source)

include bridge model producer transport booleans sourceEq in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.ReflectsAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope mode rest expected type body budget)
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
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    CellAwareInvocationLoopHeads.reflects bridge model producer transport booleans children
      found nodeType typed generated nativeTyped correct (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).1 innerEnvironment rfl).elim
  | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).2 innerEnvironment rfl).elim
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileReturned (lookupStatement?_sound statementFound) form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        .whileFault (lookupStatement?_sound statementFound) form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have same := SelectedCompilationStageLoopOutcomes.while_environment headTrace
      subst innerEnvironment
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
        remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
          middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        .whileFallthrough (lookupStatement?_sound statementFound) form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        callerProtocol.trans headRelated tailRelated, post⟩

include bridge model producer transport booleans sourceEq in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareInvocationExpressionBounds.PreservesAt (attachment := attachment) bridge context model bodyIndex stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (remaining : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope mode rest expected type body budget)
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
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : Staging.Recursive.Size.While program stages headSize invocation context environment before test statements headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type (LocalLoop.whileLoop type testCode loopCode selfReason) body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      CellAwareInvocationLoopHeads.preserves bridge model producer transport booleans children
        found nodeType typed generated nativeTyped correct bounded environments heaps locals agrees actualTyped
        runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).1 innerEnvironment rfl).elim
    | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed headTrace).2 innerEnvironment rfl).elim
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion.loop_and_tail unique statementFound form trace with
    ⟨loopSize, sourceValue, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, failure, sameSize, _contextEq, outcomeEq, loopTrace⟩ |
    ⟨loopSize, tailSize, middle, sameSize, loopTrace, tailTrace⟩
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · subst outcome
    exact finish loopTrace (by intros; intro impossible; cases impossible)
      (Nat.le_trans (Nat.le_of_lt (by rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
  · have headWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, effect, middleState, headRelated, headPost⟩ :=
      CellAwareInvocationLoopHeads.preserves bridge model producer transport booleans children
        found nodeType typed generated nativeTyped correct headWithin environments heaps locals agrees actualTyped
        runtime covers sameLedger bodyTyped initial admitted authority physical owner sameLocation ready loopTrace
    cases represented with
    | fallthrough _ _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport effect) (physical.transport effect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, effect.trans lastEffect, reached, callerProtocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationLoopSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForHeads
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialTerminal
/-! The real for-loop prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialTerminal
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
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context postItems final) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope [] test postItems statements expected type
      (LocalLoop.iterate type testCode loopCode postCode selfReason) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
  obtain ⟨loopSize, rawOutcome, sameSize, sameOutcome, loopTrace⟩ :=
    CallableIndexedOwnedAdmittedStagedForInitializerSource.nil trace
  have loopWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega)) within
  rw [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore loopTrace] at sameOutcome
  subst outcome
  exact CellAwareInvocationForHeads.preserves bridge model producer transport booleans
    children found nodeType typed generated nativeTyped correct postCorrect loopWithin
    environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
    initial admitted authority physical owner sameLocation ready loopTrace

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
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (bodyIndex.source) control context postItems final) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope [] test postItems statements expected type
      (LocalLoop.iterate type testCode loopCode postCode selfReason) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareInvocationForHeads.reflects bridge model producer transport booleans
      children found nodeType typed generated nativeTyped correct postCorrect within
      environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
      initial admitted authority physical owner sameLocation ready completed
  refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [], sourceSize], outcome,
    after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  simpa only [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore trace] using
    (CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop Staging.Recursive.Size.ForItems.empty trace)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialTerminal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForSequences
/-! The real while prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForSequences
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
  {expected : TypeSystem.Ty} {testCode loopCode headCode : Expr}
  {items postItems : List ForItemForm}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)

variable {mode : Bool} {id : StatementId} {statement : StatementNode} {rest : List StatementId}
  (sourceEq : invocation.source = bodyIndex.source)

include bridge model producer sourceEq in
theorem reflects {budget : Nat}
    (correct : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope items test postItems statements expected type headCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope mode rest expected type body budget)
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
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rw [LoopRenaming.sequence] at completed
  obtain ⟨headSize, middleStore, headValue, headSmaller, headEval⟩ := completed.bind_computation
  obtain ⟨headSourceSize, headOutcome, middle, middleMap, middleWorld, headTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, headRelated, headPost⟩ :=
    correct _ (Nat.le_trans (Nat.le_of_lt headSmaller) within)
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready headEval
  cases represented with
  | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).1 innerEnvironment rfl).elim
  | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).2 innerEnvironment rfl).elim
  | returned payload =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_returned _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form headTrace,
        .returned payload, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.sequence_failure _ headEval.sound)
      exact ⟨_, context, _, middle, middleMap, middleWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form headTrace,
        .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect,
        middleState, headRelated, headPost⟩
  | fallthrough innerEnvironment _ =>
      have same := CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough_environment headTrace
      subst innerEnvironment
      obtain ⟨tailSize, smaller, tailEval⟩ := completed.sequence_fallthrough headEval.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, represented,
          finalHeaps, maps, worlds, framePreserved, metadata, effect, reached, tailRelated, post⟩ :=
        remaining _ (Nat.le_trans (Nat.le_of_lt smaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
            (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
          (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken firstWorlds)))) runtime covers sameLedger suffixTyped
          middleState headPost (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready
          (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEval)
      exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form headTrace tailTrace,
        represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans framePreserved, firstMetadata.trans metadata, firstEffect.trans effect, reached,
        callerProtocol.trans headRelated tailRelated, post⟩

include bridge model producer sourceEq in
theorem preserves {budget : Nat}
    (correct : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope items test postItems statements expected type headCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model bodyIndex producer stages invocation faults
      administrative scope mode rest expected type body budget)
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
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (bodyIndex.source) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      bodyIndex.owner bodyIndex.active mapping world before store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have finish {headSize : Nat} {headOutcome : Staging.Recursive.BodyOutcome}
      (headTrace : CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace program stages invocation context environment before items test postItems statements headSize headOutcome after)
      (terminal : ∀ innerEnvironment, headOutcome ≠ .fallthrough innerEnvironment)
      (bounded : headSize ≤ budget) :
      ∃ value finalStore finalMap finalWorld,
        Evaluates actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore ∧
        Represents model finalMap finalWorld mode expected type faults headOutcome value ∧
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
        ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
          callerProtocol.Relates initial reached ∧ Post bridge context expected headOutcome reached := by
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      correct _ bounded environments heaps locals agrees actualTyped
        runtime covers sameLedger initial admitted authority physical owner sameLocation ready headTrace
    cases represented with
    | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).1 innerEnvironment rfl).elim
    | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed headTrace).2 innerEnvironment rfl).elim
    | returned payload =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .returned payload, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_returned _ evaluated
    | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
          maps, worlds, preservation, metadata, effect, reached, related, post⟩
        rw [LoopRenaming.sequence]
        exact LocalLoop.sequence_failure _ evaluated
    | fallthrough innerEnvironment _ => exact False.elim (terminal innerEnvironment rfl)
  rcases CallableIndexedOwnedPreparedStagedScopedForSourceInversion.initial_loop_and_tail unique statementFound form trace with
    ⟨initialSize, failedContext, failure, sameSize, _contextEq, outcomeEq, initialTrace⟩ |
    ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, sourceValue, sameSize, _contextEq, outcomeEq, initialTrace, loopTrace⟩ |
    ⟨initialSize, loopSize, loopContext, loopEnvironment, initialized, failure, sameSize, _contextEq, outcomeEq, initialTrace, loopTrace⟩ |
    ⟨initialSize, loopSize, tailSize, loopContext, loopEnvironment, initialized, middle, sameSize, initialTrace, loopTrace, tailTrace⟩
  · subst outcome
    exact finish (.initializerFault initialTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.loop initialTrace loopTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · subst outcome
    exact finish (.loop initialTrace loopTrace) (by intros; intro impossible; cases impossible) (sameSize ▸ within)
  · have headWithin : Staging.Recursive.Size.stepSize [initialSize, loopSize] ≤ budget := Nat.le_trans (by
      rw [sameSize]
      simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
      omega) within
    obtain ⟨value, middleStore, middleMap, middleWorld, headEval, represented, middleHeaps,
        maps, worlds, preservation, metadata, effect, middleState, headRelated, headPost⟩ :=
      correct _ headWithin environments heaps locals agrees actualTyped
        runtime covers sameLedger initial admitted authority physical owner sameLocation ready (.loop initialTrace loopTrace)
    cases represented with
    | fallthrough _ _ =>
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEval, represented, finalHeaps,
            lastMaps, lastWorlds, lastFrame, lastMetadata, lastEffect, reached, tailRelated, post⟩ :=
          remaining _ tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix
              (GenericExpressionMeaning.agree_prefix agrees (.inLeft LocalLoop.transferType (.inLeft type .unit))) (.inLeft type .unit)) .unit)
            (.cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit)) (actualTyped.weaken worlds)))) runtime covers sameLedger suffixTyped
            middleState headPost (authority.transport effect) (physical.transport effect preservation)
            owner sameLocation ready tailTrace
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame,
          metadata.trans lastMetadata, effect.trans lastEffect, reached, callerProtocol.trans headRelated tailRelated, post⟩
        rw [LoopRenaming.sequence]
        simp only [GenericExpressionMeaning.rename_prefix] at tailEval
        exact LocalLoop.sequence_fallthrough _ headEval tailEval

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedBitNot
/-! Accepted bare bit-not headers use their actual compiler receipt and the
original Source typing to construct the native target before dispatch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty} {assignment : AssignmentResolution}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr}
  (receipt : AcceptedBareBitNotReceipt.Receipt bodyIndex.policy fuel bodyIndex.compilerSource
    scope site assignment (LocalLoop.controlType type) body bodyIndex.reasonAt code)
  (targetType : receipt.binder.scheme.body = assignment.target.type)
  (diagnostic : faults (.semantic (.invalidUnaryOperand .bitNot))
    (receipt.invalidUnary site assignment.target.root))
  {control : ControlContext} {final : SourceSemantics.Context}
  (sourceTyped : ForItemsHaveType invocation.source control context (.assignBitNot assignment :: rest) final)

include transport targetType diagnostic sourceTyped in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements
      expected type code budget := by
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, sourceTyped⟩).1
  rw [receipt.head_emitted targetType typed]
  exact CellAwareInvocationForInitialBitNot.preserves bridge transport functions producer
    (receipt.head targetType typed) typed (receipt.head_errors targetType typed diagnostic) budget tail

include transport targetType diagnostic sourceTyped in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest test postItems statements expected type body budget) :
    CellAwareInvocationForInitialBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      test postItems statements
      expected type code budget := by
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, sourceTyped⟩).1
  rw [receipt.head_emitted targetType typed]
  exact CellAwareInvocationForInitialBitNot.reflects bridge transport functions producer
    (receipt.head targetType typed) typed (receipt.head_errors targetType typed diagnostic) budget tail

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForInitialAcceptedBitNot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedBitNot
/-! Accepted bare bit-not headers use their actual compiler receipt and the
original Source typing to construct the native target before dispatch. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedBitNot
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty} {assignment : AssignmentResolution}
  {rest : List ForItemForm} {body : Expr}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {fuel : Nat} {site : SourceCoreElaboration.ErrorSite} {code : Expr}
  (receipt : AcceptedBareBitNotReceipt.Receipt bodyIndex.policy fuel bodyIndex.compilerSource
    scope site assignment (LocalLoop.controlType type) body bodyIndex.reasonAt code)
  (targetType : receipt.binder.scheme.body = assignment.target.type)
  (diagnostic : faults (.semantic (.invalidUnaryOperand .bitNot))
    (receipt.invalidUnary site assignment.target.root))
  (sourceEq : invocation.source = bodyIndex.source)

include transport targetType diagnostic sourceEq in
theorem preserves (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    CellAwareInvocationForPostBounds.PreservesAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
  obtain ⟨control, final, original⟩ := sourceTyped
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩).1
  have assignmentTyped := sourceEq.symm ▸ typed
  have sound := CellAwareInvocationForPostBitNot.preserves bridge transport functions producer
    (receipt.head targetType assignmentTyped) sourceEq
    (receipt.head_errors targetType assignmentTyped diagnostic) budget tail
  rw [← receipt.head_emitted targetType assignmentTyped] at sound
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    ⟨control, final, original⟩

include transport targetType diagnostic sourceEq in
theorem reflects (budget : Nat)
    (tail : CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope rest expected type body budget) :
    CellAwareInvocationForPostBounds.ReflectsAtMost (attachment := attachment)
      bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      bodyIndex producer stages invocation faults administrative scope (.assignBitNot assignment :: rest)
      expected type code budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
  obtain ⟨control, final, original⟩ := sourceTyped
  have typed := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot ⟨final, original⟩).1
  have assignmentTyped := sourceEq.symm ▸ typed
  have sound := CellAwareInvocationForPostBitNot.reflects bridge transport functions producer
    (receipt.head targetType assignmentTyped) sourceEq
    (receipt.head_errors targetType assignmentTyped diagnostic) budget tail
  rw [← receipt.head_emitted targetType assignmentTyped] at sound
  exact sound size within environments heaps locals agrees actualTyped runtime covers sameLedger
    ⟨control, final, original⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationForPostAcceptedBitNot
end
