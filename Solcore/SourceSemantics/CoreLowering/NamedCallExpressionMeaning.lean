import Solcore.SourceSemantics.CoreLowering.NamedCallExpressionSource
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning

/-! Ordinary named call heads retain actual selection, static concrete bodies
and real protected installed globals. Canonical administrative observations are
transported separately from temporary actual binders. Recursive child meaning
is an inner composition interface, never a field of the static head.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

abbrev Bodies (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) :=
  List (BuiltinNamedCalls.Body prepared values definitions program)

/-- The actual administrative global cells, captures and histories for every
retained body. They are independent of source/native body execution. -/
def Entry (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry)
    (bodies : Bodies prepared values ambient.definitions program) (administrativePrefix : Nat) :
    ProtectedExpressionMeaning.Entry := fun scope mapping world before store canonical =>
  ∀ body, body ∈ bodies →
    ∃ installed : BuiltinNamedCalls.Installed functions body registry mapping world before store canonical,
      installed.globalIndex = scope.length + administrativePrefix + body.slot

theorem entry_transport (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry)
    (bodies : Bodies prepared values ambient.definitions program) (administrativePrefix : Nat) :
    ProtectedExpressionMeaning.Transport (Entry functions registry bodies administrativePrefix) := by
  constructor
  intro scope mapping world before store canonical futureMap futureWorld after futureStore installed
    maps worlds preserved metadata body member
  obtain ⟨observed, located⟩ := installed body member
  exact ⟨observed.extend maps worlds preserved metadata, located⟩

/-- Inserted temporary binders change the global variable index through the
actual renaming. The stored closure environment itself stays exact. -/
def reindex (functions : FunctionModel values.checked.catalog ambient)
    {body : BuiltinNamedCalls.Body prepared values ambient.definitions program}
    {registry mapping world before store canonical actual ξ}
    (installed : BuiltinNamedCalls.Installed functions body registry mapping world before store canonical)
    (agrees : EnvironmentsAgree ξ canonical actual) :
    BuiltinNamedCalls.Installed functions body registry mapping world before store actual :=
  { installed with
    globalIndex := ξ installed.globalIndex
    globalReference := agrees installed.globalReference }

inductive Head (bodies : Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (children : GenericExpressionMeaning.Certificate) (scope : Scope) :
    ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | named {id callee arguments body node calleeNode name codes expression}
      (member : body ∈ bodies)
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node body.output)
      (sourceType : node.type = body.function.resultType)
      (form : node.form = .call callee arguments (.declaration body.instantiation))
      (calleeFound : source.lookupExpression? callee = some calleeNode)
      (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
      (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
      (valid : SourceSemantics.DeclarationInstantiation.Valid context body.instantiation)
      (predicates : body.instantiation.predicates = []) (evidence : body.function.evidence = [])
      (arity : body.function.parameters.length = arguments.length)
      (emission : NamedCalls.Arguments.Emission compilation source scope id callee arguments
        body.instantiation body.named.signature codes ⟨body.output, expression⟩)
      (selectedSlot : emission.index = body.slot)
      (sequence : DataExpressionSequence.Tree source children scope arguments
        (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
      (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd) :
      Head bodies compilation source context children scope id ⟨body.output, expression⟩

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions

-- Ordered arguments and the concrete body.
namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates
open SourceCoreCallableIndexedFrames
open BuiltinNamedCalls (Installed)
open NamedCalls.Arguments (Trace arguments_complete body_complete)
private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} (body : BuiltinNamedCalls.Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
variable {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment}
  {scope : Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (children : DataExpressionSequence.Tree callerSource certificate scope ids
    (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd)
  (packedType : body.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)

include transport extension uninitialized missing faithful functionLeaves functionTypes children nativeTypes packedType in
theorem call_preserves
    (argumentMeaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (_unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      ProtectedDataExpressionSequence.preserves_fault transport children argumentMeaning environments heaps locals layout actualTyped installedEntry failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
    simpa only [body.resultType] using
      (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
        (sourceType := body.function.resultType) (type := body.output) matched)
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      ProtectedDataExpressionSequence.preserves_values transport children argumentMeaning environments heaps locals layout actualTyped installedEntry argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments body.bindings represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩  := BuiltinNamedCalls.body_preserves functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType body.named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩


include transport extension uninitialized missing faithful functionLeaves functionTypes children nativeTypes packedType in
theorem call_reflects
    (argumentMeaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (installedEntry : entry scope mapping world before store canonical)
    (completed : Evaluates callerEnvironment store (SourceCoreCalls.call body.named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
        before ids body.sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentValue, middleStore, argumentEvaluation⟩ := arguments_complete completed
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    ProtectedDataExpressionSequence.reflects transport children argumentMeaning environments heaps locals layout actualTyped installedEntry argumentEvaluation
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluated := SourceCoreCalls.call_argument_failure (signature := body.named.signature) (index := installed.globalIndex)
        (internalReason := reason) (packedType.symm ▸ argumentEvaluation)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      refine ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, ?_, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
      simpa only [body.resultType] using
        (FunctionCalls.ResultRepresents.fault (model := CompatibleAmbientHeap.payloadModel values.checked registry functions)
          (sourceType := body.function.resultType) (type := body.output) matched)
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments body.bindings represented
      have bodyEvaluation := body_complete argumentEvaluation installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩  := BuiltinNamedCalls.body_reflects functions extension body uninitialized missing faithful functionLeaves functionTypes next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions

namespace Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableAncestryPairedLookup SourceCoreCallableIndexedFrames

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} {bodies : Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {context : SourceSemantics.Context}
  (caller : Dynamic.EvidenceEnvironment) {certificate : GenericExpressionMeaning.Certificate}
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Source expression outcomes dispatch to the exact retained body, with
ordered arguments and concrete builtin body semantics. The global/frame entry
is obtained from actual protected observations rather than payload typing. -/
theorem Head.preserves
    (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (meaning : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source certificate faults (Entry functions registry bodies compilation.administrativePrefix)) :
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Head bodies compilation source context certificate) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | @named callee arguments body node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed installedEntry trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨observed, located⟩ := installedEntry body member
    let installed := reindex functions observed agrees
    have location : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + emission.index) := by
      change ξ observed.globalIndex = _
      rw [located, selectedSlot]
    have independent := source_inv metadata form calleeFound calleeForm predicates evidence body.frame unique owners arity trace
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preserved, heapMetadata, current, snapshots⟩ :=
      call_preserves (reason := compilation.internalReason) functions extension body (uninitialized body member) (missing body member)
        faithful functionLeaves functionTypes sequence nativeTypes packed
        (entry_transport functions registry bodies compilation.administrativePrefix) meaning installed
        environments heaps locals agrees typed installedEntry unique independent
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    · change Evaluates actual store (expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, ← location]
      exact evaluated
    · simpa only [sourceType] using represented

include extension uninitialized missing faithful functionLeaves functionTypes in
/-- Whole native completion constructs the independent ordinary named-call
expression, including first argument faults and the real source body dispatch. -/
theorem Head.reflects
    (meaning : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source certificate faults (Entry functions registry bodies compilation.administrativePrefix)) :
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context caller source (Head bodies compilation source context certificate) faults
      (Entry functions registry bodies compilation.administrativePrefix) := by
  intro scope id lowered head
  cases head with
  | @named callee arguments body node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
      calleeRequirements calleeCoercions valid predicates evidence arity emission selectedSlot sequence nativeTypes =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed installedEntry evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    obtain ⟨observed, located⟩ := installedEntry body member
    let installed := reindex functions observed agrees
    have location : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + emission.index) := by
      change ξ observed.globalIndex = _
      rw [located, selectedSlot]
    obtain ⟨emitted, packed, target, selected⟩ := emission.equation
    change expression = _ at emitted
    change Evaluates actual store (expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, ← location] at evaluated
    obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preserved, heapMetadata, current, snapshots⟩ :=
      call_reflects functions extension body (uninitialized body member) (missing body member)
        faithful functionLeaves functionTypes sequence nativeTypes packed
        (entry_transport functions registry bodies compilation.administrativePrefix) meaning installed
        environments heaps locals agrees typed installedEntry evaluated
    have closed : Dynamic.DirectCallProducesEvidence context caller node.requirements node.coercions
        body.instantiation.predicates body.function.evidence := by
      rw [metadata.requirements, metadata.coercions, predicates, evidence]
      exact .intro (selected := []) (contextual := []) (signatureRequirements := []) rfl rfl .nil
    refine ⟨outcome, after, finalMap, finalWorld,
      NamedCalls.Arguments.expression body.frame metadata.found form calleeFound calleeForm calleeRequirements
        calleeCoercions metadata.coercions valid closed trace,
      ?_, finalHeaps, maps, worlds, preserved, heapMetadata⟩
    simpa only [sourceType] using represented

end Solcore.SourceSemantics.CoreLowering.NamedCallExpressions
