import Solcore.SourceSemantics.CoreLowering.TypedImperativeForNative
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileAllocation
import Solcore.SourceSemantics.CoreLowering.GenericCellHeapOperations
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeStatements
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LoopAndMatchBounds
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.Loops
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedFlows
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ScopeAssignments
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StatementContracts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForPost
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.NamedExpressionCertificates

/-!
# Cell-aware for loops

`for` loops over mixed cells: state, edges and entry, the header tree and its collectors, iterations and sequences, and initial and post statements by form.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForAllocation
/-! The real for prelude installs its recursive Core closure while retaining
all ordinary cells and exact generalized bundles. Source allocation and lexical
scope are unchanged by this administrative self cell. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForAllocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (installedStore installedWorld)

theorem install {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {environment : Environment} {context : Core.Context} {type : Ty} {condition body post : Expr}
    (reason : Word)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (typed : HasType context (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) definitions) :
    GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model instances) mapping (installedWorld world type) heap
      (installedStore store type condition body post reason environment) ∧
    WorldExtends world (installedWorld world type) ∧ store.length ∉ mapping ∧
    (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) ∧
    (installedStore store type condition body post reason environment).read? store.length =
      some (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) ∧
    AdministrativePreserved mapping store mapping (installedStore store type condition body post reason environment) ∧
    CellAwareScopeAuthority.Effect instances mapping world heap store mapping (installedWorld world type) heap
      (installedStore store type condition body post reason environment) := by
  have worlds : WorldExtends world (installedWorld world type) := ⟨_, rfl⟩
  have found : (installedWorld world type)[store.length]? = some (OptionalCell.cellType (LocalLoop.functionType type)) := by
    rw [← heaps.runtime_hasTypes.length_eq]
    simp [installedWorld, LoopAdministration.installedWorld]
  have closureTyped : RuntimeValueHasType (installedWorld world type)
      (LocalLoop.installedClosure type condition body post reason store.length environment)
      (LocalLoop.functionType type) definitions :=
    .closure (.cons (.cellRef found) (environmentTyped.weaken worlds)) (TypedImperativeFor.Native.installed_body typed)
  have absentTyped : RuntimeValueHasType world (.inLeft (LocalLoop.functionType type) .unit)
      (OptionalCell.cellType (LocalLoop.functionType type)) definitions := .inLeft .unit
  have allocated := heaps.allocate_administrative absentTyped
  have written : (store.allocate (.inLeft (LocalLoop.functionType type) .unit)).1.write? store.length
      (.inRight .unit (LocalLoop.installedClosure type condition body post reason store.length environment)) =
      some (installedStore store type condition body post reason environment) := by
    simp [Store.allocate, Store.write?, installedStore, LoopAdministration.installedStore]
  have filled := allocated.write_administrative heaps.fresh_unmapped found (.inRight closureTyped) written
  refine ⟨filled, worlds, ?_, found, ?_, AdministrativePreserved.allocate_administrative _ _ _, ?_⟩
  · intro member
    obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
    exact heaps.fresh_unmapped lookup
  · simp [installedStore, LoopAdministration.installedStore, Store.read?]

  · exact CellAwareScopeAuthority.Effect.append store _ (.refl heap) (.refl mapping) worlds

end Solcore.SourceSemantics.CoreLowering.CellAwareForAllocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForState
/-! A live loop carries its actual self closure, the mixed Source heap and the
same caller frame. Child computation keeps its reached protocol state while
transporting every generalized descriptor through its concrete effect. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForState
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))

structure State (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (administrative actualContext : Core.Context) (environment : Dynamic.Environment)
    (canonical actual : Environment) (location : Location) (type : Ty)
    (condition body post : Expr) (reason : Word)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) where
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    mapping world administrative scope environment canonical whole.indexed.layouts.definitions
  heaps : GenericHeap.CellHeapRepresents
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions
  authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
    named.signature.key [] mapping world heap store environment
  physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  ownerAt : owner.key.frameLocation = physical.location
  ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native
  selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type))
  selfRead : store.read? location = some (.inRight .unit
    (LocalLoop.installedClosure type condition body post reason location actual))
  selfUnmapped : location ∉ mapping
  retained : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩

variable {producer} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {location : Location} {type : Ty}
  {condition body post : Expr} {reason : Word}
  {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
  {heap after : Dynamic.Heap} {store finalStore : Store}

/-- Retain the exact child post-state, rather than reconstructing an unrelated
state with the same heap. The loop's recursive closure remains unchanged. -/
def State.reach
    (state : State (named := named) producer context scope administrative actualContext environment canonical actual
      location type condition body post reason mapping world heap store)
    (heaps : GenericHeap.CellHeapRepresents
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) nextMap nextWorld after finalStore)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model whole.indexed)
      mapping world heap store nextMap nextWorld after finalStore)
    (frame : AdministrativePreserved mapping store nextMap finalStore)
    (reached : protocol.State ⟨scope,nextMap,nextWorld,after,finalStore,canonical⟩) :
    State (named := named) producer context scope administrative actualContext environment canonical actual
      location type condition body post reason nextMap nextWorld after finalStore :=
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
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store)
  (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
    named.signature.key [] mapping world heap store environment)
  (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerAt : owner.key.frameLocation = physical.location)
  (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
  (typed : HasType actualContext (LocalLoop.iterate type condition body post reason)
    (LocalLoop.resultType type) whole.indexed.layouts.definitions)
  (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩)

/-- Installing the real for self cell changes only administrative storage. -/
def install : State (named := named) producer context scope administrative actualContext environment canonical actual
    store.length type condition body post reason mapping (installedWorld world type) heap
    (installedStore store type condition body post reason actual) := by
  have allocation := CellAwareForAllocation.install reason heaps actualTyped typed
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

end Solcore.SourceSemantics.CoreLowering.CellAwareForState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForEdges
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForEdges
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

theorem condition_preserves_at {size : Nat}
    (meaning : CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    meaning tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt trace
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated,
    related, progress, reached, retained, post⟩

theorem condition_reflects_at {size : Nat}
    (reflection : CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults size)
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (found : invocation.source.lookupExpression? condition = some node)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason mapping world before store)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before condition outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        PostAdmission bridge context node.type outcome reached.retained := by
  have actualAgrees : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical
      (Core.LoopExecution.entryEnvironment type location actual) := GenericExpressionMeaning.agree_prefix
    (GenericExpressionMeaning.agree_prefix agrees (.cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location)) .unit
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    reflection tree found typed state.environments state.heaps state.locals actualAgrees
      (.cons .unit (.cons (.cellRef state.selfTyped) state.actualTyped)) state.retained ready state.authority state.physical state.owner state.ownerAt
      (by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.conditionCode, Core.LoopExecution.entryEnvironment] using evaluated)
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) body postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, progress, reached, retained, post⟩



theorem body_preserves_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome}
    (trace : Staging.Recursive.Size.StatementsIn program stages false size invocation context environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
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
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [GenericExpressionMeaning.rename_prefix, Core.LoopExecution.bodyCode,
      Core.LoopExecution.bodyEnvironment, Core.LoopExecution.entryEnvironment] using evaluated,
    represented, progress, reached, retained, post⟩

theorem body_reflects_at {budget size : Nat} {statements : List StatementId} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (typed : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages false sourceSize invocation context environment before statements finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore,
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
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode (code.rename ξ) postCode selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareForEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForEntry
/-! The actual for-loop prelude supplies its mixed state and unchanged caller
records. Its code typing follows from the real lexical environment renaming. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForEntry
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open TypedLexicalWhile (installedStore installedWorld)
open CellAwareForState (State)
open CellAwareLoopState (Progress)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
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
      (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree embedding canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext whole.indexed.layouts.definitions)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model whole.indexed)
      named.signature.key [] mapping world heap store environment)
    (physical : CellAwareScopePhysical.Physical whole named context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerAt : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type condition body post reason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (initial : protocol.State ⟨scope,mapping,world,heap,store,canonical⟩) :
    ∃ state : State (named := named) producer context scope administrative actualContext environment canonical actual
      store.length type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason mapping (installedWorld world type) heap
      (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual),
    Progress model (GeneralizedLocalInstanceValues.model whole.indexed) heap heap mapping mapping world (installedWorld world type)
      store (installedStore store type (condition.rename embedding) (body.rename embedding) (post.rename embedding) reason actual) ∧
    protocol.Relates initial state.retained ∧ protocol.records state.retained = protocol.records initial := by
  have actualCode := typed.rename (TypedLexicalWhile.environment_respects environments.runtime_hasTypes actualTyped agrees)
  rw [LoopRenaming.iterate] at actualCode
  let state := CellAwareForState.install transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  have allocation := CellAwareForAllocation.install reason heaps actualTyped actualCode
  refine ⟨state, ⟨allocation.1, .refl mapping, allocation.2.1, allocation.2.2.2.2.2.1, .refl heap,
    allocation.2.2.2.2.2.2⟩, ?_, ?_⟩
  · exact CellAwareForState.install_related transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial
  · exact CellAwareForState.install_records transport environments heaps locals actualTyped authority physical owner ownerAt ready actualCode initial

end Solcore.SourceSemantics.CoreLowering.CellAwareForEntry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
/-! The finite header profile retains original declarations and bare writable
places. Actual Source typing determines every context along the header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
open Core Frontend SourceInference

inductive Scan (source : TypedSource) (approved : ExpressionId → Prop) : List ForItemForm → Prop where
  | nil : Scan source approved []
  | absent {binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder none :: rest)
  | initialized {binder expression expressionNode rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body) (value : approved expression)
      (remaining : Scan source approved rest) : Scan source approved (.letDecl binder (some expression) :: rest)
  | discard {expression expressionNode rest}
      (found : source.lookupExpression? expression = some expressionNode)
      (value : approved expression) (remaining : Scan source approved rest) :
      Scan source approved (.expression expression :: rest)
  | assign {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type) (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)

  | assignProjected {assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (value : approved rhs)
      (remaining : Scan source approved rest) : Scan source approved (.assignValue assignment operator rhs :: rest)


def approvedKeys? {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) :
    (ids : List ExpressionId) → Option (PLift (∀ id ∈ ids, approved id))
  | [] => some ⟨by intro id member; cases member⟩
  | id :: ids => do
    let ⟨head⟩ ← expression id
    let ⟨tail⟩ ← approvedKeys? expression ids
    pure ⟨by intro child member; rcases List.mem_cons.mp member with same | rest
             · exact same ▸ head
             · exact tail child rest⟩

def scan? (source : TypedSource) {approved : ExpressionId → Prop}
    (expression : (id : ExpressionId) → Option (PLift (approved id))) :
    (items : List ForItemForm) → Option (PLift (Scan source approved items))
  | [] => some ⟨.nil⟩
  | .letDecl binder initializer :: rest =>
    match declaration : SourceCoreDataPlaces.rootBinder source binder.id with
    | .error _ => none
    | .ok actual =>
      if same : actual = binder then
        have declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder := same ▸ declaration
        if mono : binder.scheme.quantified = [] then
          if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
            match initializer with
            | none => do
              let ⟨remaining⟩ ← scan? source expression rest
              pure ⟨.absent declaration mono ordinary remaining⟩
            | some value =>
              match found : source.lookupExpression? value with
              | none => none
              | some node =>
                if valueType : node.type = binder.scheme.body then do
                  let ⟨approved⟩ ← expression value
                  let ⟨remaining⟩ ← scan? source expression rest
                  pure ⟨.initialized declaration mono ordinary found valueType approved remaining⟩
                else none
          else none
        else none
      else none
  | .expression value :: rest =>
    match found : source.lookupExpression? value with
    | none => none
    | some _ => do
      let ⟨approved⟩ ← expression value
      let ⟨remaining⟩ ← scan? source expression rest
      pure ⟨.discard found approved remaining⟩
  | .assignValue assignment operator rhs :: rest =>
    match declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root with
    | .error _ => none
    | .ok binder =>
      if profile : operator = .equal ∨ assignment.target.type = .word then
        match rhsFound : source.lookupExpression? rhs with
        | none => none
        | some rhsNode =>
          if rhsType : rhsNode.type = assignment.target.type then do
            let ⟨value⟩ ← expression rhs
            let ⟨remaining⟩ ← scan? source expression rest
            if bare : assignment.target.projections = [] then
              if targetType : binder.scheme.body = assignment.target.type then
                pure ⟨.assign declaration targetType profile bare rhsFound rhsType value remaining⟩
              else none
            else
              let ⟨route⟩ ← AcceptedProjectedAssignmentRoute.check source binder.scheme.body assignment.target.projections assignment.target.type
              let ⟨keys⟩ ← CellAwareForHeaderAdmission.approvedKeys? expression (DataPlaceKeyOrder.sourceKeys assignment.target.projections)
              pure ⟨.assignProjected declaration route profile bare keys rhsFound rhsType value remaining⟩
          else none
      else none
  | .assignBitNot _ :: _ => none

inductive Syntax (source : TypedSource) (approved : ExpressionId → Prop) :
    SourceSemantics.Context → List ForItemForm → SourceSemantics.Context → Prop where
  | nil {context} : Syntax source approved context [] context
  | absent {context nextContext final binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (remaining : Syntax source approved nextContext rest final) :
      Syntax source approved context (.letDecl binder none :: rest) final
  | initialized {context nextContext final binder initializer node rest}
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends source.owner context binder nextContext)
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : source.lookupExpression? initializer = some node)
      (sourceType : node.type = binder.scheme.body)
      (typed : ExpressionHasType source context initializer node.type)
      (value : approved initializer)
      (remaining : Syntax source approved nextContext rest final) :
      Syntax source approved context (.letDecl binder (some initializer) :: rest) final
  | discard {context final expression node rest}
      (found : source.lookupExpression? expression = some node)
      (typed : ExpressionHasType source context expression node.type)
      (value : approved expression)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.expression expression :: rest) final
  | assign {context final assignment operator rhs node binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (targetType : binder.scheme.body = assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (bare : assignment.target.projections = [])
      (found : source.lookupExpression? rhs = some node)
      (sourceType : node.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs)
      (value : approved rhs)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.assignValue assignment operator rhs :: rest) final

  | assignProjected {context final assignment operator rhs rhsNode binder rest}
      (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
      (route : AcceptedProjectedAssignmentRoute.Route source binder.scheme.body assignment.target.projections assignment.target.type)
      (profile : operator = .equal ∨ assignment.target.type = .word)
      (projected : assignment.target.projections ≠ [])
      (keys : ∀ key ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections, approved key)
      (rhsFound : source.lookupExpression? rhs = some rhsNode)
      (rhsType : rhsNode.type = assignment.target.type)
      (typed : SourceAssignmentHasType source context assignment operator rhs)
      (value : approved rhs)
      (remaining : Syntax source approved context rest final) :
      Syntax source approved context (.assignValue assignment operator rhs :: rest) final


private theorem expression_at {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) : ExpressionHasType source context id node.type := by
  obtain ⟨original, contains, same⟩ := typed.stored_type
  cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact same ▸ typed

theorem Scan.syntax {source approved items} (scan : Scan source approved items)
    {context final : SourceSemantics.Context} {control : ControlContext}
    (unique : NodeOccurrencesUnique source) (typed : ForItemsHaveType source control context items final) :
    Syntax source approved context items final := by
  induction scan generalizing context final with
  | nil => cases typed; exact .nil
  | absent declaration mono ordinary remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letUninitialized _ _ extended => exact .absent declaration mono extended ordinary (ih tail)
  | initialized declaration mono ordinary found sourceType value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | letInitialized actual _ _ extended =>
        exact .initialized declaration mono extended ordinary found sourceType (expression_at unique found actual) value (ih tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard found value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | expression actual => exact .discard found (expression_at unique found actual) value (ih tail)
  | assign declaration targetType profile bare found sourceType value remaining ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | assignValue actual => exact .assign declaration targetType profile bare found sourceType actual value (ih tail)

  | assignProjected declaration route profile projected keys rhsFound rhsType value _ ih =>
    cases typed with
    | cons head tail =>
      cases head with
      | assignValue actual =>
        exact .assignProjected declaration route profile projected keys rhsFound rhsType actual value (ih tail)

theorem Syntax.signatures {source approved context items final}
    (tree : Syntax source approved context items final) : final.signatures = context.signatures := by
  induction tree with
  | nil => rfl
  | absent _ _ extended _ _ ih | initialized _ _ extended _ _ _ _ _ _ ih =>
    cases extended
    exact ih
  | discard _ _ _ _ ih | assign _ _ _ _ _ _ _ _ _ ih | assignProjected _ _ _ _ _ _ _ _ _ _ ih => exact ih

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
/-! A finite header retains its actual compiler continuation and the exact
scope at that continuation. It contains only static typing and lowering data. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)
open TypedLexicalWhile (initializedRequest sequence)

inductive Tree {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (administrative : Core.Context) (type : Ty)
    (finalContext : SourceSemantics.Context) (finalScope : SourceCoreLocalCell.Scope)
    (terminal : Expr) :
    SourceSemantics.Context → SourceCoreLocalCell.Scope → List ForItemForm → Expr → Prop where
  | nil : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
      finalContext finalScope [] terminal
  | absent {context nextContext scope binder rest body payload}
      (declaration : SourceCoreDataPlaces.rootBinder (source named) binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (projected : checked.catalog.project binder.scheme.body = .ok payload)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (TypedLexicalControl.absentRequest (source named) scope binder payload))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        nextContext ((binder.id, payload) :: scope) rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.letDecl binder none :: rest) (.letE annotation.expression body)
  | initialized {context nextContext scope binder initializer node rest lowered body}
      (declaration : SourceCoreDataPlaces.rootBinder (source named) binder.id = .ok binder)
      (mono : binder.scheme.quantified = [])
      (extended : BinderExtends (source named).owner context binder nextContext)
      (ordinary : (source named).inputs.any (fun input => decide (input.id = binder.id)) = false)
      (found : (source named).lookupExpression? initializer = some node)
      (sourceType : node.type = binder.scheme.body)
      (typed : ExpressionHasType (source named) context initializer node.type)
      (value : certificates context scope initializer lowered)
      (allocation : SourceCoreAllocationLayouts.Allocation prepared.layouts named.signature.key []
        (initializedRequest (source named) scope binder lowered.type))
      (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated prepared.ancestry.layout.frame
        prepared.base.globals.length
        (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error)))
        (initializedRequest (source named) scope binder lowered.type))
      (same : annotation.original = allocation.expression)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        nextContext ((binder.id, lowered.type) :: scope) rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.letDecl binder (some initializer) :: rest)
        (sequence type lowered.expression annotation.expression body)
  | discard {context scope expression node rest lowered body}
      (found : (source named).lookupExpression? expression = some node)
      (typed : ExpressionHasType (source named) context expression node.type)
      (value : certificates context scope expression lowered)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.expression expression :: rest)
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)
  | assign {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) context
        (certificates context) scope administrative prepared.layouts.definitions assignment operator rhs)
      (bare : assignment.target.projections = [])
      (typed : SourceAssignmentHasType (source named) context assignment operator rhs)
      (operands : AssignmentOperandDiagnostics.OperandsLaw
        (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) operator head.invalid)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.assignValue assignment operator rhs :: rest)
        (head.emit body (LocalLoop.controlType type))

  | assignProjected {context scope assignment operator rhs rest body}
      (head : GenericAssignmentStatements.Head (.initial checked) (source named) context
        (certificates context) scope administrative prepared.layouts.definitions assignment operator rhs)
      (projected : assignment.target.projections ≠ [])
      (typed : SourceAssignmentHasType (source named) context assignment operator rhs)
      (site : ∀ registry, PreparedBranchingCatalogSites.AssignmentSite
        (fun site root => diagnostics.placeReason named.signature.key site root none)
        (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
        registry (GenericAssignmentDiagnostics.OperandRep compiled.own.assignments) head)
      (remaining : Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope rest body) :
      Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope (.assignValue assignment operator rhs :: rest)
        (head.emit body (LocalLoop.controlType type))

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
/-! Actual header lowering determines every child, marked allocation and
operand token. Its final continuation is a static compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

private theorem operands_at {source : TypedSource} {context : SourceSemantics.Context}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    AssignmentOperandDiagnostics.OperandsLaw (GenericAssignmentDiagnostics.OperandRep table)
      operator (GenericAssignmentDiagnostics.token table site assignment.target.root operator) := by
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands prepared present.1 (.statement form)
      (AssignmentDiagnosticOrigins.raw_profile typed)
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands prepared present.1 (.header form member)
      (AssignmentDiagnosticOrigins.raw_profile typed)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

theorem collected
    (unique : NodeOccurrencesUnique (source named))
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    (assignmentPolicy : ∀ fuel scope site assignment operator rhs output next reasonAt,
      SourceCoreLoops.assignValue policy fuel (source named) scope site assignment operator rhs output next reasonAt =
      SourceCoreCompatibleDataPlaces.lower (.initial checked) checked.signatures policy.lowerExpression
        fuel (source named) scope site assignment operator (some rhs) output next reasonAt
        (diagnostics.placeReason named.signature.key site assignment.target.root none)
        (GenericAssignmentDiagnostics.token compiled.own.assignments site assignment.target.root operator)
        (fun type => diagnostics.placeReason named.signature.key site assignment.target.root (some type)))
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder (source named) scope binder = SourceCoreCompatibleDataExpressions.lowerBinder checked (source named) scope binder)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {finalContext : SourceSemantics.Context} {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {continuation : SourceCoreLocalCell.Scope → Expr → Prop}
    (nextCertificate : ∀ scope code,
      CompatibleExpressionReads.ScopeDeclarations (source named) scope finalContext →
      next scope = .ok code → ∀ {nativeType},
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions →
      continuation scope code)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    (syntaxTree : CellAwareForHeaderAdmission.Syntax (source named) approved context items finalContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope context)
    (sourceSignatures : context.signatures = checked.signatures)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor true (source named) site items)
    {fuel : Nat} {type : Ty} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy site fuel (source named) scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    ∃ finalScope terminal,
      continuation finalScope terminal ∧
      CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope items code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil =>
    refine ⟨scope, code, nextCertificate scope code declarations ?_ nativeTyped, .nil⟩
    cases fuel <;> exact accepted
  | @absent context nextContext finalContext binder rest declaration mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate
        (scope_bind payload declarations declaration extended)
        (by cases extended; exact sourceSignatures) origin.tail generated
        (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      exact ⟨finalScope, terminal, nextReceipt, .absent declaration mono extended ordinary
        (binder_projected (binderPolicy scope binder mono ▸ projected)) allocation annotation same tail⟩
  | @initialized context nextContext finalContext binder initializer node rest declaration mono extended ordinary found sourceType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, checkedTypeEq, accepted⟩ := bind_ok accepted
      cases checkedType
      have sameType := ensure_same checkedTypeEq
      subst payload
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have child := children context declarations value found typed generated childTyped
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate
        (scope_bind lowered.type declarations declaration extended)
        (by cases extended; exact sourceSignatures) origin.tail generatedBody
        (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact ⟨finalScope, terminal, nextReceipt, .initialized declaration mono extended ordinary found sourceType
        typed child allocation annotation same tail⟩
  | @discard context finalContext expression node rest found typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate declarations sourceSignatures origin.tail generatedBody tailTyped
      exact ⟨finalScope, terminal, nextReceipt,
        .discard found typed (children context declarations value found typed generated childTyped) tail⟩
  | @assign context finalContext assignment operator rhs node binder rest declaration targetType profile bare found sourceType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨_projections, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare typed
      obtain ⟨actualBinder, preparedPlace, index, lowered, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
      obtain ⟨_, rhsNative⟩ := (CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_children
        (codeEq ▸ nativeTyped)).1
      have child : certificates context scope rhs lowered :=
        children context declarations value found (sourceType.symm ▸ rightTyped) generated rhsNative
      obtain ⟨head, emitted, token⟩ := GenericAssignmentStatements.Head.of_lower_bare_with_token
        (administrative := administrative) (definitions := prepared.layouts.definitions)
        bare unique writable rightTyped runtimeProfile (fun actual acceptedRight => by
          have same : actual = lowered := Except.ok.inj (acceptedRight.symm.trans generated)
          subst actual
          exact ⟨node, found, child⟩) accepted
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have operands := operands_at tablePrepared origin.operand typed
      rw [← token] at operands
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate declarations sourceSignatures origin.tail generatedBody tailTyped
      rw [emitted]
      exact ⟨finalScope, terminal, nextReceipt, .assign head bare typed operands tail⟩

  | @assignProjected context finalContext assignment operator rhs rhsNode binder rest declaration route profile projected keys rhsFound rhsType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨sourceTyped, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.projected_assignment_facts unique declaration route typed
      obtain ⟨head, emitted, token, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped runtimeProfile
          (certificate := certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨_, native⟩ := raw
            rcases List.mem_cons.mp member with same | member
            · subst child
              exact ⟨rhsNode, rhsFound, children context declarations value rhsFound
                (rhsType.symm ▸ rightTyped) generated native⟩
            · obtain ⟨node, found, childTyped⟩ := route.key_typed unique (sourceTyped binder declaration) member
              exact ⟨node, found, children context declarations (keys _ member) found childTyped generated native⟩)
          accepted nativeTyped
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have operands := operands_at tablePrepared origin.operand typed
      rw [← token] at operands
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate declarations sourceSignatures
        origin.tail generatedBody tailTyped
      rw [emitted]
      exact ⟨finalScope, terminal, nextReceipt, .assignProjected head projected typed
        (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
          origin.operand sourceSignatures preparedAt operands registry) tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForPostEdges
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostEdges
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)

theorem preserves_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final)
    (ready : Admission bridge context state.retained)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (TypedImperativeFor.postValues type location continuing ++ actual) store
        (ForLoop.postCode (code.rename ξ)) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready trace
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨value, finalStore, finalMap, finalWorld,
    by simpa only [TypedImperativeFor.post_rename] using evaluated,
    represented, progress, reached, retained, post⟩

theorem reflects_at {continuing : Bool} {budget size : Nat} {items : List ForItemForm} {expected : TypeSystem.Ty}
    (correct : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope items expected type code budget)
    (within : size ≤ budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason mapping world before store)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context items final)
    (ready : Admission bridge context state.retained)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size (TypedImperativeFor.postValues type location continuing ++ actual) store
      (ForLoop.postCode (code.rename ξ)) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧
        Post bridge context expected (restoredOutcome environment outcome) reached.retained := by
  have postAgrees : EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical
      (TypedImperativeFor.postValues type location continuing ++ actual) :=
    TypedImperativeFor.postValues_agree agrees type location continuing
  obtain ⟨postContext, actualPostTyped⟩ := TypedImperativeFor.postValues_typed continuing state.selfTyped state.actualTyped
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, preserved, metadata, effect, last, retained, post⟩ :=
    correct size within state.environments state.heaps state.locals postAgrees actualPostTyped
      runtime covers sameLedger postTyped state.retained ready state.authority state.physical state.owner state.ownerAt state.ready
      (by simpa only [TypedImperativeFor.post_rename] using evaluated)
  have progress : Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore :=
    ⟨heaps, maps, worlds, preserved, metadata, effect⟩
  let reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type conditionCode body (code.rename ξ) selfReason finalMap finalWorld after finalStore :=
    state.reach heaps effect preserved last
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace,
    represented, progress, reached, retained, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForIterations
/-! Actual condition and body children execute under the installed self cell.
The reached mixed heap, exact descriptor effect and caller admission survive
both Source preservation and native reflection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForIterations
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code postCode : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

open CellAwareForEdges
variable {condition : ExpressionId} {node : ExpressionNode}
  {statements : List StatementId} {expected : TypeSystem.Ty} {post : List ForItemForm}

theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
      {store finalStore : Store} {value : Value},
    ∀ state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      EvaluationSize size (Core.LoopExecution.entryEnvironment type location actual) store
        (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before condition post statements outcome after ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
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
      exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .testFault conditionTrace, .fault matched,
        conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | value payload =>
      rw [nodeType] at payload
      obtain ⟨boolean, sameSource, sameCore⟩ := booleans payload
      subst sameSource
      subst sameCore
      cases boolean with
      | false =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound (Core.LoopExecution.condition_false conditionEval.sound)
        exact ⟨_, _, conditionHeap, conditionMap, conditionWorld, .finished conditionTrace, .fallthrough environment (.inl rfl),
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
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .bodyFailure conditionTrace bodyTrace, .fault matched,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | returned payload =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_returned conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .returnedFromBody conditionTrace bodyTrace, .returned payload,
            progress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | fallthrough innerEnvironment allowed =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size false branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CellAwareForPostEdges.reflects_at (continuing := false) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_fallthrough_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .postFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_fallthrough branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .iterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

        | breaking innerEnvironment =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
            (Core.LoopExecution.body_breaking conditionEval.sound bodyEval.sound)
          exact ⟨_, _, bodyHeap, bodyMap, bodyWorld, .forBreakFromBody conditionTrace bodyTrace,
            .fallthrough environment (.inl rfl), progress, bodyState,
            callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
        | continuing innerEnvironment =>
          obtain ⟨postSize, postStore, postValue, postSmaller, postEval⟩ :=
            RecursiveNamedForContracts.post_computation_size true branch bodyEval.sound
          obtain ⟨postSourceSize, postContext, postOutcome, postHeap, postMap, postWorld, postTrace,
              postRelated, postProgress, postState, postRetained, postPost⟩ :=
            CellAwareForPostEdges.reflects_at (continuing := true) bridge model producer postCorrect
              (Nat.le_trans (Nat.le_of_lt postSmaller) (Nat.le_trans (Nat.le_of_lt branchSmaller) bounded))
              agrees bodyState runtime covers sameLedger postTyped bodyPost postEval
          cases postOutcome with
          | fault failure =>
            cases postRelated with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluation.sound
                (ForLoop.body_continuing_post_fault conditionEval.sound bodyEval.sound postEval.sound)
              exact ⟨_, _, postHeap, postMap, postWorld, .continuePostFailure conditionTrace bodyTrace postTrace,
                .fault matched, progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
          | done postEnvironment =>
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨nextSize, smaller, nextEval⟩ :=
                ForLoop.next_continuing branch bodyEval.sound postEval.sound postState.selfRead
              obtain ⟨nextSourceSize, outcome, after, finalMap, finalWorld, nextTrace, related, nextProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih nextSize (Nat.lt_trans smaller branchSmaller)
                  (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) bounded) postState postPost nextEval
              exact ⟨_, _, after, finalMap, finalWorld, .continueIterate conditionTrace bodyTrace postTrace nextTrace, related,
                prefixProgress.trans nextProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? condition = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context condition node.type)
    (tree : certificate scope condition ⟨.bool, conditionCode⟩)
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type code budget)
    (postCorrect : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope post expected type postCode budget)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context post final) :
    ∀ size, size ≤ budget → ∀ {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
      {store : Store} {outcome : Staging.Recursive.BodyOutcome},
    ∀ state : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
      location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason mapping world before store,
      Admission bridge context state.retained →
      Staging.Recursive.Size.ForLoop program stages size invocation context environment before condition post statements outcome after →
      ∃ value finalStore finalMap finalWorld,
        Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
          (LocalLoop.loopBody type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason) value finalStore ∧
        Represents model finalMap finalWorld false expected type faults outcome value ∧
        Progress model (GeneralizedLocalInstanceValues.model compiled.indexed) before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : CellAwareForState.State (named := named) producer context scope administrative actualContext environment canonical actual
        location type (conditionCode.rename ξ) (code.rename ξ) (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        callerProtocol.Relates state.retained reached.retained ∧ Post bridge context expected outcome reached.retained := by
  intro size
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro bounded mapping world before after store outcome state ready trace
    cases trace with
    | finished testTrace =>
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
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_false conditionEval,
            .fallthrough environment (.inl rfl), conditionProgress, conditionState, conditionRetained, conditionPost.at_value.2⟩
    | testFault testTrace =>
        obtain ⟨conditionValue, conditionStore, conditionMap, conditionWorld, conditionEval, conditionRelated,
            conditionProgress, conditionState, conditionRetained, conditionPost⟩ :=
          condition_preserves_at bridge model producer
            (children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) bounded))
            tree found typed agrees state ready testTrace
        cases conditionRelated with
        | fault matched =>
          exact ⟨_, conditionStore, conditionMap, conditionWorld, Core.LoopExecution.condition_failure conditionEval,
            .fault matched, conditionProgress, conditionState, conditionRetained, conditionPost.at_fault_type⟩
    | returnedFromBody testTrace bodyTrace =>
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
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_returned conditionEval bodyEval, .returned payload,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | forBreakFromBody testTrace bodyTrace =>
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
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_breaking conditionEval bodyEval, .fallthrough environment (.inl rfl),
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | bodyFailure testTrace bodyTrace =>
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
            exact ⟨_, bodyStore, bodyMap, bodyWorld, Core.LoopExecution.body_failure conditionEval bodyEval, .fault matched,
              conditionProgress.trans bodyProgress, bodyState, callerProtocol.trans conditionRetained bodyRetained, bodyPost⟩
    | postFailure testTrace bodyTrace postTrace =>
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
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_fallthrough_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | iterate testTrace bodyTrace postTrace next =>
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
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareForPostEdges.preserves_at (continuing := false) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_fallthrough conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

    | continuePostFailure testTrace bodyTrace postTrace =>
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
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fault matched =>
              exact ⟨_, postStore, postMap, postWorld,
                ForLoop.body_continuing_post_fault conditionEval bodyEval postEval, .fault matched,
                progress.trans postProgress, postState,
                callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained, postPost⟩
    | continueIterate testTrace bodyTrace postTrace next =>
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
            obtain ⟨postValue, postStore, postMap, postWorld, postEval, postRelated, postProgress,
                postState, postRetained, postPost⟩ :=
              CellAwareForPostEdges.preserves_at (continuing := true) bridge model producer postCorrect
                (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                agrees bodyState runtime covers sameLedger postTyped bodyPost postTrace
            cases postRelated with
            | fallthrough _ _ =>
              have prefixProgress := progress.trans postProgress
              obtain ⟨result, finalStore, finalMap, finalWorld, nativeTrace, related, finalProgress,
                  finalState, finalRetained, finalPost⟩ :=
                ih _ (Staging.Recursive.Size.child_lt_stepSize (by simp))
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) bounded)
                  postState postPost next
              exact ⟨result, finalStore, finalMap, finalWorld,
                ForLoop.body_continuing conditionEval bodyEval postEval postState.selfRead nativeTrace,
                related, prefixProgress.trans finalProgress, finalState,
                callerProtocol.trans (callerProtocol.trans (callerProtocol.trans conditionRetained bodyRetained) postRetained) finalRetained, finalPost⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForIterations
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForHeads
/-! The real for-loop prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeads
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
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
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.ForLoop program stages sourceSize invocation context environment before test postItems statements outcome after ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareForEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  rw [LoopRenaming.iterate] at completed
  obtain ⟨entrySize, entrySmaller, nativeEntry⟩ := completed.iterate_entry
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, progress,
      reached, related, post⟩ :=
    CellAwareForIterations.reflects bridge model producer
      children found nodeType typed generated correct postCorrect agrees booleans runtime covers sameLedger bodyTyped postTyped entrySize
      (Nat.le_trans (Nat.le_of_lt entrySmaller) within) protectedState activated nativeEntry
  have total := installedProgress.trans progress
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
    total.heaps, total.maps, total.worlds, total.preserved, total.metadata, total.effect,
    reached.retained, callerProtocol.trans installedRelated related, post⟩

include bridge model producer transport booleans in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.ForLoop program stages size invocation context environment before test postItems statements outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.iterate type testCode loopCode postCode selfReason).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  obtain ⟨protectedState, installedProgress, installedRelated, installedRecords⟩ :=
    CellAwareForEntry.install producer transport environments heaps locals agrees actualTyped
      authority physical owner sameLocation ready nativeTyped initial
  have activated := (CallableIndexedOwnedAdmittedForReadiness.activation bridge).ready initial
    protectedState.retained installedProgress.preserved installedRelated installedRecords admitted
  obtain ⟨value, finalStore, finalMap, finalWorld, nativeTrace, represented, progress,
      reached, related, post⟩ :=
    CellAwareForIterations.preserves bridge model producer
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

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeads
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForInitialAssignment
/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining header items. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport unique bare assignmentTyped extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment snapshot trace with
    ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
    ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, outcomeEq, childTrace,
      currentRead, rootType, initialized, path, invalid⟩ |
    ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_operands bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type) invalidToken
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot childTrace write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport unique bare assignmentTyped extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareScopeBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
      assignment_fault snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
      assignment_operands snapshot trace currentRead rootType initialized path invalid,
      .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
      prepend_assignment snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForInitialDiscard
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialDiscard
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions)
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


variable {expression : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {expressionNode : ExpressionNode} {rest : List ForItemForm}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope (.expression expression :: rest) test postItems statements expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.expression trace with
    ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
    ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
  · subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
        middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
            finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
          tail tailSize tailWithin (environments.extend firstMaps firstWorlds)
            middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            runtime covers sameLedger middleState firstPost.at_value.2 (authority.transport firstEffect)
            (physical.transport firstEffect firstFrame) owner sameLocation ready remainingTrace
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
          firstMetadata.trans metadata, firstEffect.trans effect, reached, protocol.trans expressionRelated tailRelated, post⟩

include expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope (.expression expression :: rest) test postItems statements expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  rw [LoopRenaming.discard] at completed
  obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
    children childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [sourceSize]], _, middle, middleMap, middleWorld,
        expression_fault childTrace, .fault matched, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost.at_fault_type⟩
  | @value sourceValue coreValue payload =>
      obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
      obtain ⟨tailSourceSize, outcome, after, finalMap, finalWorld, tailTrace, related,
          finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
        tail tailSize (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix agrees coreValue)
          (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) runtime covers sameLedger
          middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], outcome, after, finalMap, finalWorld,
        prepend_expression childTrace tailTrace, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialDiscard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForInitialProjectedAssignment
/-! Projected assignment sequences retain the reached key, getter, RHS and
write states before continuing through the same mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialProjectedAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceAssignmentHasType invocation.source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions protocol
        invocation.source context certificate scope administrative environment assignment.target head.prepared operator head.invalid
        initial (fun reason token => faults (.semantic reason) token) head.shape)

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready outcome after trace
  have splitTrace := CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion.projected_assignment projected trace
  cases splitTrace with
  | rootFault failed => exact False.elim (failed.excluded head.writable locals)
  | keysFault ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | getterFault keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | rhsFault keyTrace snapshot childTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | writeFault keyTrace snapshot childTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_write_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success keyTrace snapshot childTrace write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport unique projected assignmentTyped extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForInitialBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest test postItems statements expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForInitialBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) test postItems statements expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger
    initial admitted authority physical owner sameLocation ready completed
  have result := CellAwareScopeProjectedAssignmentHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected keyTrace snapshot childTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_, _]], _, _, _, _,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected keyTrace snapshot childTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], outcome, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment projected keyTrace snapshot childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialProjectedAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTerminal
/-! The real for-loop prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTerminal
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
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
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final) :
    CellAwareScopeForInitialBounds.PreservesAtMost bridge context model named producer stages invocation faults
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
  exact CellAwareForHeads.preserves bridge model producer transport booleans
    children found nodeType typed generated nativeTyped correct postCorrect loopWithin
    environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
    initial admitted authority physical owner sameLocation ready loopTrace

include bridge model producer transport booleans in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final) :
    CellAwareScopeForInitialBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope [] test postItems statements expected type
      (LocalLoop.iterate type testCode loopCode postCode selfReason) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareForHeads.reflects bridge model producer transport booleans
      children found nodeType typed generated nativeTyped correct postCorrect within
      environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
      initial admitted authority physical owner sameLocation ready completed
  refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [], sourceSize], outcome,
    after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  simpa only [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore trace] using
    (CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop Staging.Recursive.Size.ForItems.empty trace)

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTerminal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTreeBounds
/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTreeBounds
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForInitializerSource
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    functions protocol (source named)
    (fun site root => diagnostics.placeReason named.signature.key site root none)
    (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
    receiving (fun reason token => faults (.semantic reason) token))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

private theorem rep_restore {mapping world expected type outcome value environment}
    (related : Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      mapping world false expected type faults outcome value) :
    Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      mapping world false expected type faults (outcome.restore environment) value := by
  cases related with
  | returned payload => exact .returned payload
  | fault matched => exact .fault matched
  | fallthrough _ allowed => exact .fallthrough environment allowed
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment

private theorem post_restore {context expected outcome environment index}
    {reached : protocol.State index}
    (post : Post bridge context expected outcome reached) :
    Post bridge context expected (outcome.restore environment) reached := by
  cases outcome <;> exact post

include bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code terminal : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope terminal context scope items code)
    (last : CellAwareScopeForInitialBounds.PreservesAtMost bridge finishContext (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative finishScope [] test postItems statements expected type terminal budget) :
    CellAwareScopeForInitialBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items test postItems statements expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
      outcome after trace
    have member := member_of_root declaration
    obtain ⟨tailSize, location, bound, nextOutcome, sameSize, sameOutcome, allocated, remainingTrace⟩ :=
      CallableIndexedOwnedAdmittedStagedForInitializerSource.absent
        (by simpa only [sourceEq] using extended) trace
    subst outcome
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
    obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, rep_restore functions represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_restore bridge
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
      outcome after trace
    have member := member_of_root declaration
    rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.initialized mono
        (by simpa only [sourceEq] using extended) trace with
      ⟨childSize, failure, sameSize, outcomeEq, child⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, bound, nextOutcome, sameSize, sameOutcome, child, allocated, remainingTrace⟩
    · subst outcome
      have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
    · subst outcome
      have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
      obtain ⟨value, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | @value _ coreValue payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEvaluated, represented, finalHeaps,
            tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
          ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
        let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, rep_restore functions represented, finalHeaps,
          maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
          frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
          effect.trans (allocationEffect.trans finalEffect), finalState,
          protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
        apply post_restore bridge
        exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | nil => exact last
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready outcome after trace
    exact CellAwareForInitialDiscard.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready trace
  | @assign context scope assignment operator rhs rest body head bare assignmentTyped operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForInitialAssignment.preserves bridge transport functions producer runtime.graph.nodeOccurrencesUnique
        head bare assignmentTyped extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready trace

  | @assignProjected context scope assignment operator rhs rest body head projected assignmentTyped site remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareForInitialProjectedAssignment.preserves bridge transport functions producer runtime.graph.nodeOccurrencesUnique
        head projected assignmentTyped extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial) budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready trace

include bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code terminal : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope terminal context scope items code)
    (last : CellAwareScopeForInitialBounds.ReflectsAtMost bridge finishContext (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative finishScope [] test postItems statements expected type terminal budget) :
    CellAwareScopeForInitialBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items test postItems statements expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
      completed
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
    have member := member_of_root declaration
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome.restore environment, after, finalMap, finalWorld,
      prepend_absent mono (by simpa only [sourceEq] using extended) allocated trace,
      rep_restore functions represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_restore bridge
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready
      completed
    have member := member_of_root declaration
    have original := completed
    rw [TypedLexicalControl.sequence_rename] at original
    obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
    obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
        maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
      children context runtime covers sameLedger childSize (Nat.lt_of_lt_of_le childSmaller within) certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
        (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [childSourceSize]], _, middle, middleMap, middleWorld,
        initializer_fault mono child,
        .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
    | @value sourceValue coreValue payload =>
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
          childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], outcome.restore environment, after, finalMap, finalWorld,
        prepend_initialized mono (by simpa only [sourceEq] using extended) child allocated trace,
        rep_restore functions represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      apply post_restore bridge
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | nil => exact last
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareForInitialDiscard.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready completed
  | @assign context scope assignment operator rhs rest body head bare assignmentTyped operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForInitialAssignment.reflects bridge transport functions producer runtime.graph.nodeOccurrencesUnique
        head bare assignmentTyped extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready completed

  | @assignProjected context scope assignment operator rhs rest body head projected assignmentTyped site remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareForInitialProjectedAssignment.reflects bridge transport functions producer runtime.graph.nodeOccurrencesUnique
        head projected assignmentTyped extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial) functionTypes budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger
        initial admitted authority physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForPostAssignment
/-! Mixed bare assignments execute the real target snapshot, RHS, modifier
and write before the remaining header items. Every reached descriptor survives
both successful updates and genuine failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
    (fun reason token => faults (.semantic reason) token) operator head.invalid)

include transport sourceEq unique bare extension invalidToken in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final := ⟨control, facts.2⟩
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, contextEq, outcomeEq, childTrace,
      currentRead, rootType, initialized, path, invalid⟩ |
    ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_fault bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) childTrace body (LocalLoop.controlType type)
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, stable⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_operands bridge functions extension head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type) invalidToken
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
      preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
        effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
      CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
        (children childSize childStrict) snapshot childTrace write
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail tailSize tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
    have native := (continuation body (LocalLoop.controlType type)).wrap (by
      simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
        SourceCoreDataPlaces.shift] using evaluated)
    exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
      effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique bare extension invalidToken in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final := ⟨control, facts.2⟩
  have result := CellAwareScopeBareAssignmentHeads.reflects_bounded bridge functions extension transport
    head bare environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children invalidToken completed within
  cases result with
  | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignmentFailure snapshot trace, .fault matched,
      finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, fault_post bridge reached stable⟩
  | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
    cases same
    exact ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
      .assignmentOperands snapshot trace currentRead rootType initialized path invalid,
      .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related,
      fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | success snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
        finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
      tail _ (Nat.le_trans (Nat.le_of_lt strict) within) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
        reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using remaining)
    exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .assignment snapshot childTrace write trace, represented,
      finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
      metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForPostDiscard
/-! Discarded expressions execute once before their actual remaining flow.
Their concrete descriptor effects compose at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostDiscard
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
  (named : SourceCoreGeneralFunctions.Function)
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (administrative : Core.Context)
  (scope : SourceCoreLocalCell.Scope)
  (expected : TypeSystem.Ty) (type : Ty)


variable {expression : ExpressionId}
  {expressionNode : ExpressionNode} {rest : List ForItemForm}
  {lowered : SourceCoreBasic.LoweredExpr} {body : Expr}
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
  (typed : ExpressionHasType invocation.source context expression expressionNode.type)
  (certified : certificate scope expression lowered)

include expressionFound typed certified in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer registry invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope (.expression expression :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final :=
    ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.expression ⟨final, original⟩⟩
  rw [LoopRenaming.discard]
  rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression trace with
    ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
    ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
  · subst finalContext
    subst outcome
    have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, post.at_fault_type⟩
  · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
        middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
      children childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
        initial admitted authority physical owner sameLocation childTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
            finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
          tail tailSize tailWithin (environments.extend firstMaps firstWorlds)
            middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
            runtime covers sameLedger suffix middleState firstPost.at_value.2 (authority.transport firstEffect)
            (physical.transport firstEffect firstFrame) owner sameLocation ready remainingTrace
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
          firstMetadata.trans metadata, firstEffect.trans effect, reached, protocol.trans expressionRelated tailRelated, post⟩

include expressionFound typed certified in
theorem reflects (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context model named registry invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer registry invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.ReflectsAt bridge context model named producer registry invocation faults
      administrative scope (.expression expression :: rest) expected type
      (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final :=
    ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.expression ⟨final, original⟩⟩
  rw [LoopRenaming.discard] at completed
  obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
      middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost⟩ :=
    children childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
      environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
  cases represented with
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
        .expressionFailure childTrace, .fault matched, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, expressionRelated, firstPost.at_fault_type⟩
  | @value sourceValue coreValue payload =>
      obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
      obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
          finalHeaps, maps, worlds, preservation, metadata, effect, reached, tailRelated, post⟩ :=
        tail tailSize (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
          (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
          (GenericExpressionMeaning.agree_prefix agrees coreValue)
          (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) runtime covers sameLedger suffix
          middleState firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame)
          owner sameLocation ready (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
      exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .expression childTrace tailTrace, related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
        firstFrame.trans preservation, firstMetadata.trans metadata, firstEffect.trans effect,
        reached, protocol.trans expressionRelated tailRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostDiscard
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForPostProjectedAssignment
/-! Projected assignment sequences retain the reached key, getter, RHS and
write states before continuing through the same mixed scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostProjectedAssignment
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CallableIndexedOwnedAdmittedStagedImperativeFlow (fault_post)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
  {expected : TypeSystem.Ty} {type : Ty}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {rest : List ForItemForm} {body : Expr}
variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalInstanceValues.model compiled.indexed)))
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)
  (unique : NodeOccurrencesUnique invocation.source)
  (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context certificate
    scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (projected : assignment.target.projections ≠ [])
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (diagnostics : SourceAssignmentHasType invocation.source context assignment operator rhs →
    ∀ {environment : Dynamic.Environment} {initialIndex : ProtectedStateTransition.Index}
      (initial : protocol.State initialIndex),
      ProtectedPlaceReachedDiagnostics.ShapeErrors (.initial compiled.compatible.checked) registry functions protocol
        invocation.source context certificate scope administrative environment assignment.target head.prepared operator head.invalid
        initial (fun reason token => faults (.semantic reason) token) head.shape)

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem preserves (budget : Nat)
    (children : CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.PreservesAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready finalContext outcome after trace
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final := ⟨control, facts.2⟩
  cases trace with
  | assignment snapshot _ _ _ | assignmentFailure snapshot _ | assignmentOperands snapshot _ _ _ _ _ _ =>
    cases snapshot with | intro empty _ _ _ => exact (projected empty).elim
  | unbound empty _ | dangling empty _ _ => exact (projected empty).elim
  | projectedAssignmentRootFault _ failed => exact False.elim (failed.excluded head.writable locals)
  | projectedAssignmentKeysFault _ ready keyTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_key_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | projectedAssignmentGetterFault _ keyTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_getter_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | projectedAssignmentRhsFault _ keyTrace snapshot childTrace =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
  | projectedAssignmentWriteFault _ keyTrace snapshot childTrace failed =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
          preservation, metadata, effect, reached, related, stable⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_write_fault
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children (diagnostics assignmentTyped initial)
          keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
        preservation, metadata, effect, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
  | projectedAssignment _ keyTrace snapshot childTrace write remainingTrace =>
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
          effect, count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
        CellAwareScopeProjectedAssignmentHeads.preserves_value
          (compiled := compiled)
          (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations
          head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          budget children keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready remainingTrace
      have native := (continuation body (LocalLoop.controlType type)).wrap (by
        simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
          SourceCoreDataPlaces.shift] using evaluated)
      exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
        maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
        effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

include transport sourceEq unique projected extension faithful observations diagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) (budget : Nat)
    (children : CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named stages invocation certificate faults budget)
    (tail : CellAwareScopeForPostBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope rest expected type body budget) :
    ∀ size, size ≤ budget → CellAwareScopeForPostBounds.ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) named producer stages invocation faults
      administrative scope (.assignValue assignment operator rhs :: rest) expected type (head.emit body (LocalLoop.controlType type)) size := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation ready completed
  obtain ⟨control, final, original⟩ := sourceTyped
  have facts := CallableIndexedOwnedPreparedStagedForItemsTyping.assignment ⟨final, original⟩
  have assignmentTyped := sourceEq.symm ▸ facts.1
  have suffix : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context rest final := ⟨control, facts.2⟩
  have result := CellAwareScopeProjectedAssignmentHeads.reflects_bounded (compiled := compiled)
    (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport faithful observations
    head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
    budget children functionTypes
      (diagnostics assignmentTyped initial) completed within
  cases result with
  | keyFault ready keyTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedAssignmentKeysFault projected ready keyTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | getterFault keyTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
        .projectedAssignmentGetterFault projected keyTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | rhsFault keyTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .projectedAssignmentRhsFault projected keyTrace snapshot childTrace, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge reached stable
  | writeFault keyTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata effect reached related stable =>
      cases same
      refine ⟨Staging.Recursive.Size.stepSize [_, _], context, _, _, _, _,
        .projectedAssignmentWriteFault projected keyTrace snapshot childTrace failed, .fault matched,
        finalHeaps, maps, worlds, preservation, metadata, effect, reached, related, ?_⟩
      exact fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable
  | success keyTrace snapshot childTrace write middleHeaps maps worlds preservation metadata effect count typed reached related nextAdmitted strict remaining =>
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, finalEffect, last, lastRelated, post⟩ :=
        tail _ (Nat.le_trans (Nat.le_of_lt strict) within)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees _) typed runtime covers sameLedger suffix
          reached nextAdmitted (authority.transport effect) (physical.transport effect preservation) owner sameLocation ready
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
      exact ⟨Staging.Recursive.Size.stepSize [_, _, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .projectedAssignment projected keyTrace snapshot childTrace write trace, represented,
        finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
        metadata.trans finalMetadata, effect.trans finalEffect, last, protocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostProjectedAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForPostTreeBounds
/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForPostTreeBounds
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial whole.compatible.checked)
    functions protocol (source named)
    (fun site root => diagnostics.placeReason named.signature.key site root none)
    (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw))
    receiving (fun reason token => faults (.semantic reason) token))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      mapping world false expected type faults (restoredOutcome second outcome) value := by
  cases outcome with
  | done environment => cases related with | fallthrough _ allowed => exact .fallthrough _ allowed
  | fault failure => exact related

private theorem post_environment {context expected outcome first second index}
    {reached : protocol.State index}
    (post : Post bridge context expected (restoredOutcome first outcome) reached) :
    Post bridge context expected (restoredOutcome second outcome) reached := by
  cases outcome <;> exact post

private theorem absent_typed {source : TypedSource} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {rest : List ForItemForm}
    (typed : ∃ control final, ForItemsHaveType source control context (.letDecl binder none :: rest) final)
    (extended : BinderExtends source.owner context binder nextContext) :
    ∃ control final, ForItemsHaveType source control nextContext rest final := by
  obtain ⟨control, final, typed⟩ := typed
  exact ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.absent ⟨final, typed⟩ extended⟩

private theorem initialized_typed {source : TypedSource} {context nextContext : SourceSemantics.Context}
    {binder : TypedBinder} {initializer : ExpressionId} {rest : List ForItemForm}
    (typed : ∃ control final, ForItemsHaveType source control context (.letDecl binder (some initializer) :: rest) final)
    (mono : binder.scheme.quantified = []) (extended : BinderExtends source.owner context binder nextContext) :
    ∃ control final, ForItemsHaveType source control nextContext rest final := by
  obtain ⟨control, final, typed⟩ := typed
  exact ⟨control, CallableIndexedOwnedPreparedStagedForItemsTyping.initialized ⟨final, typed⟩ mono extended⟩

include bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics in
theorem preserves {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.PreservesBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope (LocalLoop.fallthrough type) context scope items code) :
    CellAwareScopeForPostBounds.PreservesAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have member := member_of_root declaration
    obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
      CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent
        (by simpa only [sourceEq] using extended) trace
    have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
    obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (absent_typed sourceTyped extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap evaluated, rep_environment functions represented, finalHeaps,
      effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_environment bridge (first := (binder.id, location) :: environment)
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    have member := member_of_root declaration
    rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized mono
        (by simpa only [sourceEq] using extended) trace with
      ⟨childSize, failure, sameSize, contextEq, outcomeEq, child⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, bound, sameSize, child, allocated, remainingTrace⟩
    · subst finalContext
      subst outcome
      have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, CellAwareOrdinaryContinuation.failure evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post.at_fault_type⟩
    · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨value, middleStore, middleMap, middleWorld, evaluated, represented, middleHeaps,
          maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
        children context runtime covers sameLedger childSize childStrict certified
          (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation child
      cases represented with
      | @value _ coreValue payload =>
        let middlePhysical := physical.transport effect frame
        obtain ⟨marker, agreement, _smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
          CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
            evaluated (valueType ▸ payload) (valueType ▸ post.at_value.1)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            middleState post.at_value.2 (authority.transport effect) middlePhysical
            (ready middleState middlePhysical.read) allocated type body
        have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
          intro index current stored
          have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
          simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
        obtain ⟨value, finalStore, finalMap, finalWorld, tailEvaluated, represented, finalHeaps,
            tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
          ih _ tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
            (runtime.transport (.ofBinderExtends extended))
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
            ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
            (initialized_typed sourceTyped mono extended)
            reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady remainingTrace
        let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
        refine ⟨value, finalStore, finalMap, finalWorld, agreement.wrap tailEvaluated, rep_environment functions represented, finalHeaps,
          maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
          frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
          effect.trans (allocationEffect.trans finalEffect), finalState,
          protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
            (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
        apply post_environment bridge (first := (binder.id, location) :: environment)
        exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | nil =>
    intro size _within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      finalContext outcome after trace
    obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.empty trace
    rw [LoopRenaming.fallthrough]
    exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates type actual store,
      .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
      initial, protocol.refl initial, admitted⟩
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    exact CellAwareForPostDiscard.preserves bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready trace
  | @assign context scope assignment operator rhs rest body head bare _typed operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForPostAssignment.preserves bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head bare extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

  | @assignProjected context scope assignment operator rhs rest body head projected _typed site remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready finalContext outcome after trace
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareForPostProjectedAssignment.preserves bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head projected extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial) budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready trace

include bindings transport extension registered operandIncluded faithful observations assignmentDiagnostics in
theorem reflects (functionTypes : FunctionRuntimeViews functions) {budget : Nat}
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      CellAwareScopeExpressionBounds.ReflectsBelow bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
      (certificates context) faults budget)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope (LocalLoop.fallthrough type) context scope items code) :
    CellAwareScopeForPostBounds.ReflectsAtMost bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named producer registry invocation faults
      administrative scope items expected type code budget := by
  induction tree with
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let bound : Dynamic.Heap := ⟨before.cells ++ [⟨binder.scheme.body, none, none⟩]⟩
    have allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound := .append
    have member := member_of_root declaration
    obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
        preserved, effect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
      CellAwareNamedAbsentPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
        projected environments heaps locals agrees actualTyped initial admitted authority physical
        (ready initial physical.read) allocated body
    obtain ⟨tailSize, strict, tailCompleted⟩ := smaller completed
    have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
      intro index current stored
      have previous := ready current (by simpa only [locationEq, nativeEq] using stored)
      simpa only [locationEq, nativeEq] using previous
    obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, finalFrame, metadata, finalEffect, tailState, tailRelated, post⟩ :=
      ih _ (Nat.le_trans (Nat.le_of_lt strict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
        (runtime.transport (.ofBinderExtends extended))
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
        ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
        (absent_typed sourceTyped extended)
        reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailCompleted
    let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
    refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
      .absent mono (by simpa only [sourceEq] using extended) allocated trace,
      rep_environment functions represented, finalHeaps, effect.maps.trans maps, effect.worlds.trans worlds, preserved.trans finalFrame,
      effect.metadata.trans metadata, effect.trans finalEffect, finalState,
      protocol.trans related (protocol.trans tailRelated (bindings.restore_related
        (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload)
        (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
    apply post_environment bridge (first := (binder.id, location) :: environment)
    exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post

  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
      completed
    have member := member_of_root declaration
    have original := completed
    rw [TypedLexicalControl.sequence_rename] at original
    obtain ⟨childSize, middleStore, input, childSmaller, childEvaluation⟩ := original.bind_computation
    obtain ⟨childSourceSize, sourceOutcome, middle, middleMap, middleWorld, child, represented, middleHeaps,
        maps, worlds, frame, metadata, effect, middleState, expressionRelated, post⟩ :=
      children context runtime covers sameLedger childSize (Nat.lt_of_lt_of_le childSmaller within) certified
        (by simpa only [sourceEq] using initializerFound) (by simpa only [sourceEq] using typed)
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation childEvaluation
    cases represented with
    | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound
        (CellAwareOrdinaryContinuation.failure childEvaluation.sound)
      exact ⟨Staging.Recursive.Size.stepSize [childSourceSize], context, _, middle, middleMap, middleWorld,
        .initializerFault mono child,
        .fault matched, middleHeaps, maps, worlds, frame, metadata, effect, middleState, expressionRelated, post.at_fault_type⟩
    | @value sourceValue coreValue payload =>
      let location : Dynamic.Location := ⟨middle.cells.length⟩
      let bound : Dynamic.Heap := ⟨middle.cells ++ [⟨binder.scheme.body, some sourceValue, none⟩]⟩
      have allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound := .append
      let middlePhysical := physical.transport effect frame
      obtain ⟨marker, _agreement, smaller, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
          preserved, allocationEffect, nextAuthority, reached, related, nextAdmitted, nextPhysical, locationEq, nativeEq⟩ :=
        CellAwareNamedOrdinaryPrefix.complete bridge mono member extended ordinary allocation annotation same producer registered
          childEvaluation.sound (valueType ▸ payload) (valueType ▸ post.at_value.1)
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          middleState post.at_value.2 (authority.transport effect) middlePhysical
          (ready middleState middlePhysical.read) allocated type body
      obtain ⟨tailSize, tailStrict, tailEvaluation⟩ := smaller completed
      have nextReady : ProtectedStateTransition.CellAllocation.ReadyAt producer nextPhysical.location nextPhysical.native := by
        intro index current stored
        have previous := ready current (by simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using stored)
        simpa only [locationEq, nativeEq, middlePhysical, CellAwareScopePhysical.Physical.transport_location, CellAwareScopePhysical.Physical.transport_native] using previous
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          tailMaps, tailWorlds, finalFrame, finalMetadata, finalEffect, tailState, tailRelated, tailPost⟩ :=
        ih _ (Nat.le_trans (Nat.le_of_lt tailStrict) within) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          (runtime.transport (.ofBinderExtends extended))
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).covers covers)
          ((Dynamic.RuntimeContextFields.ofBinderExtends extended).solvedRequirements.trans sameLedger)
          (initialized_typed sourceTyped mono extended)
          reached nextAdmitted nextAuthority nextPhysical owner (sameLocation.trans locationEq.symm) nextReady tailEvaluation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := lowered.type)
        (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [childSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .initialized mono (by simpa only [sourceEq] using extended) child allocated trace,
        rep_environment functions represented, finalHeaps, maps.trans (allocationEffect.maps.trans tailMaps), worlds.trans (allocationEffect.worlds.trans tailWorlds),
        frame.trans (preserved.trans finalFrame), metadata.trans (allocationEffect.metadata.trans finalMetadata),
        effect.trans (allocationEffect.trans finalEffect), finalState,
        protocol.trans expressionRelated (protocol.trans related (protocol.trans tailRelated (bindings.restore_related
          (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
      apply post_environment bridge (first := (binder.id, location) :: environment)
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState tailPost
  | nil =>
    intro size _within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready completed
    rw [LoopRenaming.fallthrough] at completed
    obtain ⟨rfl,rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨1, _, _, before, mapping, world, .empty,
      .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _ _,
      initial, protocol.refl initial, admitted⟩
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    exact CellAwareForPostDiscard.reflects bridge context (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions)
      named producer registry invocation faults administrative scope expected type
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      budget (children context runtime covers sameLedger) ih size within
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
  | @assign context scope assignment operator rhs rest body head bare _typed operands remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      have invalid : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid :=
        fun previous right different => operandIncluded _ _ (operands previous right different)
      exact CellAwareForPostAssignment.reflects bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head bare extension invalid budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

  | @assignProjected context scope assignment operator rhs rest body head projected _typed site remaining ih =>
    intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
      environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
      initial admitted authority physical owner sameLocation ready completed
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareForPostProjectedAssignment.reflects bridge transport functions producer rfl runtime.graph.nodeOccurrencesUnique
        head projected extension faithful observations
        (fun typed _ _ initial => PreparedAssignmentReachedDiagnostics.shape_errors
          (site receiving) operandIncluded assignmentDiagnostics typed initial) functionTypes budget (children context runtime covers sameLedger) ih size within
        environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
        initial admitted authority physical owner sameLocation ready completed

end Solcore.SourceSemantics.CoreLowering.CellAwareForPostTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareForSequences
/-! The real while prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForSequences
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
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
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
  (sourceEq : invocation.source = CallableIndexedNamedGeneration.source named)

include bridge model producer sourceEq in
theorem reflects {budget : Nat}
    (correct : CellAwareScopeForInitialBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope items test postItems statements expected type headCode budget)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    (completed : EvaluationSize size actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        (id :: rest) finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
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
    (correct : CellAwareScopeForInitialBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope items test postItems statements expected type headCode budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope mode rest expected type body budget)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (runtime : Dynamic.SourceRuntimeValid program context (CallableIndexedNamedGeneration.source named))
    (covers : invocation.evidence.Covers context)
    (sameLedger : context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context (id :: rest))
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed)
      named.signature.key [] mapping world before store environment)
    (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    (ready : ProtectedStateTransition.CellAllocation.ReadyAt producer physical.location physical.native)
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.sequence type headCode body).rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
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
        GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed)
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

end Solcore.SourceSemantics.CoreLowering.CellAwareForSequences
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
/-! Pointwise static certificate inclusion retains every original statement,
initializer packet, marked allocation and emitted native expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
open Core Frontend SourceInference

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode}
  {first second : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {reasonAt : ExpressionId → Word}

theorem map_tree
    (included : ∀ context scope id lowered, first context scope id lowered → second context scope id lowered)
    {context scope mode statements expected type code}
    (tree : CellAwareNativeBodyTree.Tree prepared named compiled first administrative reasonAt
      context scope mode statements expected type code) :
    CellAwareNativeBodyTree.Tree prepared named compiled second administrative reasonAt
      context scope mode statements expected type code := by
  induction tree with
  | returning rest found form expressionFound valueType typed value =>
    exact .returning rest found form expressionFound valueType typed (included _ _ _ _ value)
  | tail found form expressionFound valueType typed value =>
    exact .tail found form expressionFound valueType typed (included _ _ _ _ value)
  | generalizedInitialized found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same copied _remaining ih =>
    exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same copied ih

def map_body
    (included : ∀ context scope id lowered, first context scope id lowered → second context scope id lowered)
    {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled first administrative context expected) :
    CellAwareNamedBodySupport.Body compiled second administrative context expected :=
  ⟨body.flow, map_tree included body.tree, body.emitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
end
