import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection

/-! Pointwise stored calls retain positive cells and result origins at the
original returned caller. Source admission comes from the original whole
Source trace, its real initial admission and cumulative frame preservation.
The receiving model is the positive model throughout; neither an erased
representation nor a completed body law supplies a stronger result.
Preservation derives its application leaf from strict body children, while
reflection reuses the receiving-model endpoint. The joint child/body family
and per-input live callee invariant remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallOriginPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureInvocation (Association)
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedStoredIndirectCallBounds
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Result
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context}
  {firstMap : LocationMap} {firstWorld : StoreTyping} {before : Dynamic.Heap} {firstStore : Store}
  {canonical : Environment}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)

/-- Every effect and the stronger post belong to the same returned caller.
The closure body registry is kept independently of outer payload metadata. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
    finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧
    PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile compiler.original.type lowered.type outcome value reached

/-- The model-generic producer already derives PostAdmission from its actual
whole Source trace. Its positive heap and result attach to that exact witness;
this projection performs no invocation or restoration. -/
theorem of_result_at {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler first outcome after value finalStore finalMap finalWorld) :
    ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, cells, maps, worlds, frame, metadata, reached, related, admitted⟩ := result
  exact ⟨represented, cells, maps, worlds, frame, metadata, reached, related,
    post_at_same_state bridge profile reached admitted cells represented⟩

/-- Forgetting only the stronger facets reconstructs the original causal
result, with the very same returned state, pool and independent effects. -/
theorem ResultAt.forget {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld) :
    ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨represented, cells, maps, worlds, frame, metadata, reached, related, post⟩ := result
  exact ⟨represented, cells, maps, worlds, frame, metadata, reached, related, post.admission⟩

/-- Sequential use receives the same successful caller together with its raw
value type, deep heap admission, all rows, positive cells and native payload. -/
theorem ResultAt.at_value {raw : Dynamic.Value} {native : Value}
    {after : Dynamic.Heap} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (result : ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (context := context) bridge profile compiler first (.value raw) after (.inRight .word native)
      finalStore finalMap finalWorld) :
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates first reached ∧ Admission bridge context reached ∧
      Dynamic.ValueHasType context after raw compiler.original.type ∧
      CellOrigins headers keys bodyRegistry registry faults profile finalMap finalWorld after finalStore ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        finalMap finalWorld compiler.original.type raw native lowered.type := by
  obtain ⟨_, _, _, _, _, _, reached, related, post⟩ := result
  have successful := post.at_value
  exact ⟨reached, related, successful.1, successful.2.1, post.cells, successful.2.2⟩
end Result

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Closure} {calleeNative : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function calleeNative bindings parameterCore resultCore)
  (heaps : CellOrigins headers keys bodyRegistry registry faults profile mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- The application leaf is derived internally from the actual admitted ordered
arguments and strict body children. The original whole call and single caller
restoration then return the same positive cells/result and Source admission. -/
theorem preserves_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) wellFormed budget)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix (Program.ofChecked compiled.sourceProgram) context evidence source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  have original : ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ForModel.ResultAt (registry := registry) (faults := faults) (context := context)
        bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        compiler first outcome after value finalStore finalMap finalWorld := by
    apply ForModel.preserves_selected_with_application bridge
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
      calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata (Association.native_typed association)
      heaps rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation selected budget children suffix argumentsWithin callWithin
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState argumentAdmission maps worlds frame metadata calleeTyped extension representedValues
      middleHeaps rawTyped packing bundle argumentsSize callSize outcome after argumentsTrace called _sameSuffix callWithin
    have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
      simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
    have valuesCount : _ = bindings.length := representedValues.length.1.symm.trans nativeCount
    have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings representedValues
      valuesCount sourceBundle nativeBundle
    have future := association.extend maps worlds
    have rawArity := arity_of_association future representedArguments
    obtain ⟨result, finalStore, evaluated, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
      CallableIndexedOwnedAdmittedStoredClosureInvocation.preserves_at bridge
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        wellFormed runtime future argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps
        rawTyped packing bundle rawArity budget below called callWithin
    exact ⟨result, finalStore, finalMap, finalWorld,
      application_gate dispatch selected ((Association.binding_count association).symm.trans binderCount.symm)
        native.diagnostics.unknown,
      evaluated, resultRep, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, lastRelated⟩
  obtain ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceTrace, evaluated, result⟩ := original
  exact ⟨sourceSize, value, finalStore, finalMap, finalWorld, sourceTrace, evaluated,
    of_result_at bridge profile compiler first result⟩

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- Reflection reuses the receiving-model whole parent exactly once. Its
independently constructed Source grade and exact returned caller are retained. -/
theorem reflects_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile))
      context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile) wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      ResultAt (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (context := context) bridge profile compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result⟩ :=
    CallableIndexedOwnedStoredIndirectCallForModelReflection.reflects_selected
      bridge (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      compiler prepared parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
      calleeState calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
      rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation selected budget children below completed within
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace,
    of_result_at bridge profile compiler first result⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallOriginPosts
