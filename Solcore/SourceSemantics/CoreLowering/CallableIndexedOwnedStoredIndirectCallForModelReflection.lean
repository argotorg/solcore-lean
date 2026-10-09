import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

/-! Finite accepted stored-call reflection for an arbitrary authenticated receiving
model. The actual callee Association and ordered argument bundles feed the original
model-generic payload invocation once. Only genuine strict expression/body IH is
required. ResultAt retains that model's result and heap at the same returned caller,
with raw Source admission derived from the reconstructed whole Source trace.
This endpoint does not close any child family, classify arbitrary callees, recover
strong payloads from the erased model or retain a discarded body-state witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureInvocation (Association)
open CallableIndexedOwnedStoredClosureArgumentReceipts
open CallableIndexedOwnedStoredIndirectCallBounds
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world calleeHeap store)
  (binderCount : ids.length = bindings.length)
  (sourceBundle : TypeSystem.Ty.productMany sourceTypes = TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)))
  (nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd))
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids (.closure function) calleeNative)
  (accepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar) prepared.site.call ids (.closure function))
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.closure function) calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}

include association binderCount sourceBundle nativeBundle wellFormed runtime in
/-- The exact ordered bundle at the actual argument post supplies the original
receiving-model payload invocation. Its body obligation is only strict same-family
IH. The selected callee association is extended along the real map and world. -/
theorem application_reflects_of_bundles (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value}
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩)
    (argumentAdmission : Admission bridge context argumentState)
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter sourceResult))
    (extension : Dynamic.HeapTypesExtend calleeHeap middle)
    (represented : DataExpressionSequence.Values model middleMap middleWorld sourceTypes
      (compiler.codes.map (·.type)) arguments payloads)
    (middleHeaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      middleMap middleWorld middle middleStore)
    (rawTyped : Dynamic.ValuesHaveTypes context middle arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [calleeNative, DataPatternValues.packValues payloads] middleStore
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ callSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize
        context evidence function.evidence middle (.closure function) arguments outcome after ∧
      CallableIndexedOwnedStoredClosureInvocation.CallerResultAt
        (registry := registry) (faults := faults) functions bridge argumentState
        function resultCore outcome after value finalStore := by
  have nativeCount : (compiler.codes.map (·.type)).length = bindings.length := by
    simpa only [List.length_map] using compiler.ordered_children.1.symm.trans binderCount
  have valuesCount : _ = bindings.length := represented.length.1.symm.trans nativeCount
  have representedArguments := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    bindings represented valuesCount sourceBundle nativeBundle
  have future := association.extend maps worlds
  have rawArity := arity_of_association future representedArguments
  exact CallableIndexedOwnedAdmittedStoredClosureInvocation.reflects_at bridge functions wellFormed runtime future
    argumentState argumentAdmission calleeTyped extension representedArguments middleHeaps rawTyped packing
    bundle rawArity budget below completed within

include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata association heaps binderCount sourceBundle nativeBundle
  rawResult nativeResult dispatch accepted calleeTrace calleeEvaluation in
/-- The original finite whole-call inversion retains independent Source/native
grades. Argument faults keep the actual child post; successful arguments call the
receiving-model payload reflector once at their genuine reached state. -/
theorem reflects_selected
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original dispatch.row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      CallableIndexedOwnedStoredIndirectCallBounds.ForModel.ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      (.closure function) (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have stage := CallableIndexedOwnedSelectedCallStageAcceptance.before_arguments dispatch accepted native.diagnostics.unknown
  have arity := application_gate dispatch selected ((Association.binding_count association).symm.trans binderCount.symm) native.diagnostics.unknown
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  rw [emitted] at completed
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons (Association.native_typed association) (typed.weaken calleeWorlds))
  cases accepted_completed dispatch.shape calleeEvaluation stage arity completed within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, after, finalMap, finalWorld, sourceArguments, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases sourceArguments with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, original,
          CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
          calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
          reached, callerProtocol.trans calleeRelated related,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | applied argumentsTrace applicationTrace smaller applicationSmaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, middle, middleMap, middleWorld, sourceArguments, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | values represented =>
      cases sourceArguments with
      | values sourceArguments =>
        obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
          after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping sourceArguments
        obtain ⟨callSize, outcome, after, called, finalMap, finalWorld, resultRep, finalHeaps, lastMaps, lastWorlds,
            lastFrame, lastMetadata, _baseReached, _baseRelated, _stable, returned, _samePool, lastRelated⟩ :=
          application_reflects_of_bundles (bridge := bridge) (functions := functions) (compiler := compiler)
            (association := association) (binderCount := binderCount) (sourceBundle := sourceBundle)
            (nativeBundle := nativeBundle) (wellFormed := wellFormed) (runtime := runtime)
            budget below argumentState (argumentPost.successful _ rfl) maps worlds
            calleeTyped extension represented middleHeaps rawTyped packing
            (empty_bundle application compiler.argumentCoercions) applicationTrace (Nat.le_of_lt applicationSmaller)
        obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (SourceSuffix.called sourceArguments called)
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
          CallableIndexedOwnedStoredIndirectCallBounds.ForModel.parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
          (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
          (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
          returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
          after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
            ((calleeFrame.trans frame).trans lastFrame)⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection
