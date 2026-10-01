import Solcore.SourceSemantics.CoreLowering.NamedCallMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralMeaning
import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentSource
import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentCertificates

/-! Ordinary named calls compose concrete recursive argument trees with a
concrete lexical named-body certificate. Installed globals and caller frames
are transported along the actual argument heap effects before body entry. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableAncestryPairedLookup
open CallableIndexedHistory CallableIndexedParameterCertificates
open SourceCoreCallableIndexedFrames

abbrev ValuesContext := SourceCoreCompatibleValues.Context

/-- Static body compilation and independent declaration attribution. There
is no source execution, native execution or body meaning field. -/
structure Body {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base) (values : ValuesContext)
    (definitions : DataEnvironment) (program : Program) where
  function : Dynamic.Closure
  instantiation : DeclarationInstantiation
  sourceBody : Dynamic.BodyInstance
  frame : NamedCalls.SourceFrame program instantiation sourceBody function
  named : SourceCoreGeneralFunctions.Function
  agreement : CompatibleNamedBody.NamedAgreement named function
  closed : named.specialized.assumptions = []
  ordinaryReturn : named.specialized.function.returnComptime = false
  ordinaryParameters : ∀ binder, binder ∈ function.parameters → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey base.plan instantiation = .ok named.signature.key
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  bindings : List Binding
  parameters : function.parameters = bindings.map Prod.fst
  inputs : function.source.inputs = bindings.map Prod.fst
  extended : MonoBindersExtend function.source.owner function.context function.parameters types context
  solved : List SolvedRequirement
  reasonAt : ExpressionId → Word
  readFuel : Nat
  output : Ty
  policy : SourceCoreLoops.Policy
  fuel : Nat
  fellThrough : Word
  escaped : Word
  body : Expr
  parameterCode : Expr
  code : Expr
  layouts : SourceCoreAllocationLayouts.Prepared
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  globals : Nat
  onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error
  certificate : TypedLexicalNamedBody.Certificate layouts owner active prepared.layout.frame globals onError readFuel values
    function.source context solved reasonAt (bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    function.body function.resultType output policy fuel fellThrough escaped body
  acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame globals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode
  hook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code
  definitions_eq : layouts.definitions = definitions
  registered : prepared.layout.frame.Registered definitions
  valid : CompatibleExpressionLiterals.ContextValid solved context function.evidence
  unique : NodeOccurrencesUnique function.source
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  resultType : named.signature.resultType = output
  representation : SourceCoreGeneralFunctions.Representation
  compiledFuel : Nat
  compiled : SourceCoreCompatibleMarkedFunctions.Compilation base representation compiledFuel
  slot : Nat
  selected : base.functions[slot]? = some named
  cached : compiled.closures[slot]? = some (.lambda named.signature.parameterType
    (LanguageResult.resultType named.signature.resultType) code)

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

private theorem arguments_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {bindings : List Binding}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads) :
    RuntimeValueHasType world (DataPatternValues.packValues payloads)
      (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)) definitions := by
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => simpa [DataPatternValues.packValues, SourceCoreCompatibleCatalog.packTypes] using model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

/-- Rename the complete helper, preserving the inserted argument/function
binders and moving only its real caller environment slot. -/
theorem call_rename (signature : SourceCoreCalls.Signature) (index : Nat)
    (arguments : Expr) (reason : Word) (ξ : Renaming) :
    (SourceCoreCalls.call signature index arguments reason).rename ξ =
      SourceCoreCalls.call signature (ξ index) (arguments.rename ξ) reason := by
  simp [SourceCoreCalls.call, LanguageResult.bind, OptionalCell.read, LanguageResult.success,
    LanguageResult.failure, Expr.rename, Renaming.lift]

/-- A finite whole call necessarily completes its first argument bundle. -/
theorem arguments_complete {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {store finalStore : Store} {value : Value}
    (completed : Evaluates environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    ∃ argumentValue argumentStore, Evaluates environment store arguments argumentValue argumentStore := by
  cases completed with
  | caseLeft argument _ => exact ⟨_, _, argument⟩
  | caseRight argument _ => exact ⟨_, _, argument⟩

/-- With the observed argument result and authenticated installed global,
actual call completion enters the exact saved body; no body trace is supplied. -/
theorem body_complete {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment captured : Environment} {store middle finalStore : Store} {value argument : Value}
    {location : Location} {body : Expr}
    (argumentsEvaluated : Evaluates environment store arguments (.inRight .word argument) middle)
    (reference : environment[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : middle.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : Evaluates environment store (SourceCoreCalls.call signature index arguments reason) value finalStore) :
    Evaluates (argument :: captured) middle body value finalStore := by
  have selected := OptionalCell.read_success reason
    (show Evaluates (argument :: environment) middle (.var (index + 1))
      (.cellRef (OptionalCell.cellType signature.functionType) location) middle from .var reference) read
  obtain ⟨_, sized⟩ := evaluation_has_size completed
  obtain ⟨_, _, following⟩ := sized.bind_success argumentsEvaluated
  obtain ⟨_, _, applied⟩ := following.bind_success selected
  obtain ⟨_, _, bodyEvaluation⟩ := applied.apply_body (.var rfl) (.var rfl)
  exact bodyEvaluation.sound

/-- Real installed environments, code and frame state. These observational
facts grant no source declaration or body semantics; those are in `Body`. -/
structure Installed {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient)
    {program : Program} (body : Body prepared values ambient.definitions program)
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)
    (before : Dynamic.Heap) (store : Store) (callerEnvironment : Environment) where
  administrative : Core.Context
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before body.function.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[body.globals]? = some (.cellRef prepared.layout.frame.type frameLocation)
  capturedReference : captured[embedding base.globals.length]? = some (.cellRef prepared.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType body.named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure body.named.signature.parameterType (LanguageResult.resultType body.named.signature.resultType)
      (body.code.rename embedding.lift) captured))

/-- Argument effects preserve the exact installed closure and both protected
administrative histories. Captured environment typing is weakened along the
actual world extension, including all non-source slots. -/
def Installed.extend {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {functions : FunctionModel values.checked.catalog ambient} {program : Program}
    {body : Body prepared values ambient.definitions program} {registry : SourceCoreRawMetadata.Registry}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed functions body registry futureMapping futureWorld after futureStore callerEnvironment := by
  have frameBound := (List.getElem?_eq_some_iff.mp installed.caller.read).1
  have globalBound := (List.getElem?_eq_some_iff.mp installed.globalRead).1
  have frame := preserved installed.frameLocation installed.unmapped frameBound
  have global := preserved installed.globalLocation installed.globalUnmapped globalBound
  exact { installed with
    environments := installed.environments.extend maps worlds
    locals := installed.locals.mono metadata
    captureTyped := installed.captureTyped.weaken worlds
    unmapped := frame.1
    frameTyped := worlds.lookup installed.frameTyped
    caller := ⟨frame.2.trans installed.caller.read, installed.caller.history⟩
    snapshots := installed.snapshots.transport preserved
    globalUnmapped := global.1
    globalRead := global.2.trans installed.globalRead }

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program} (body : Body prepared values ambient.definitions program)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include extension uninitialized missing in
/-- The concrete parameter/body certificates close this body invocation after
the real argument effects. The only source execution premise is the particular
independent invocation being preserved. -/
theorem body_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (body.code.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  have arity : body.function.parameters.length = arguments.length := by
    rw [body.parameters, List.length_map]; exact represented.length.1
  obtain ⟨environment, bound, allocated, trace⟩ := body.frame.trace_of_body body.extended arity executed
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluation, result, finalHeaps,
    maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    NamedCalls.hook_preserves prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots allocated trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds,
    preserved, metadata, current, snapshots⟩

include extension uninitialized missing in
/-- Completed actual body execution constructs parameter allocation and the
independent invocation from the concrete lexical tree, with frame restoration. -/
theorem body_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {value : Value}
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world body.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (executed : Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
      (body.code.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program body.sourceBody body.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace, result,
    finalHeaps, maps, worlds, preserved, metadata, current, snapshots, _⟩ :=
    NamedCalls.hook_reflects prepared functions extension program body.onError body.certificate body.parameters body.inputs body.extended
      body.valid body.unique uninitialized missing body.acceptedPrefix body.definitions_eq body.registered body.hook represented
      installed.environments heaps installed.locals (ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (.cons (arguments_typed represented) installed.captureTyped) installed.canonicalReference installed.capturedReference
      installed.unmapped installed.frameTyped installed.caller installed.snapshots executed
  exact ⟨outcome, after, finalMap, finalWorld, body.frame.body_of_trace body.extended allocated trace,
    result, finalHeaps, maps, worlds, preserved, metadata, current, snapshots⟩

variable {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (callerValid : CompatibleExpressionLiterals.ContextValid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (body.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = body.bindings.map Prod.snd)
  (packedType : body.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Concrete General argument trees close all child meaning. Arguments are
evaluated before the global read; their first fault skips the body. The body
uses its actual static parameter/lexical certificates at the intervening heap. -/
theorem preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
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
    (unique : NodeOccurrencesUnique callerSource)
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
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionGeneral.preserves functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
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
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments body.bindings represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ := body_preserves functions extension body uninitialized missing next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType body.named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes packedType in
/-- Every finite native call completion reconstructs its ordered source
argument trace and concrete independent named-body invocation. Neither child
evaluations nor a universal body preservation hypothesis are supplied. -/
theorem reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
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
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionGeneral.Tree readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionGeneral.reflects functions extension faithful functionLeaves functionTypes
    program callerEvidence callerValid callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation
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
        bodyFrame, bodyMetadata, current, snapshots⟩ := body_reflects functions extension body uninitialized missing next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Actual compiler success, independent source attribution and concrete
argument/body certificates close reflection at the emitted expression itself. -/
theorem accepted_reflects {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  rw [emitted, call_rename, ← located] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    reflects functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed trace,
    result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

include extension uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
  children nativeTypes in
/-- Preservation starts with this exact independently instantiated source body
and ordered argument trace. The actual accepted emitted expression is evaluated,
including argument faults and lexical body faults with their preceding writes. -/
theorem accepted_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {canonical : Environment}
    {administrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome} {compilation : SourceCoreFunctions.Context}
    {id callee : ExpressionId} {calleeNode : ExpressionNode} {name : String} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope id callee ids body.instantiation body.named.signature codes lowered)
    (installed : Installed functions body registry mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.index))
    (calleeFound : callerSource.lookupExpression? callee = some calleeNode)
    (calleeForm : calleeNode.form = .reference name (.declaration body.instantiation))
    (calleeRequirements : calleeNode.requirements = []) (calleeCoercions : calleeNode.coercions = [])
    (coercions : receipt.node.coercions = [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid callerContext body.instantiation)
    (closed : Dynamic.DirectCallProducesEvidence callerContext callerEvidence receipt.node.requirements receipt.node.coercions
      body.instantiation.predicates body.function.evidence)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : Trace program callerContext callerEvidence body.function.evidence callerSource sourceEnvironment
      before ids body.sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      SourceCompilationPlan.exactInstantiationKey compilation.plan body.instantiation = .ok body.named.signature.key ∧
      compilation.globals[receipt.index]? = some body.named.signature ∧
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld body.function.resultType body.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame installed.frameLocation
        installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore installed.records := by
  obtain ⟨emitted, packed, target, global⟩ := receipt.equation
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩ :=
    preserves functions extension body uninitialized missing faithful functionLeaves functionTypes callerValid callerUninitialized callerMissing
      children nativeTypes packed installed environments heaps locals layout actualTyped unique execution
  have completed : Evaluates callerEnvironment store (lowered.expression.rename ξ) value finalStore := by
    rw [emitted, call_rename, ← located]; exact evaluation
  exact ⟨value, finalStore, finalMap, finalWorld, target, global,
    expression body.frame receipt.found receipt.form calleeFound calleeForm calleeRequirements calleeCoercions coercions valid closed execution,
    completed, result, finalHeaps, maps, worlds, frame, metadata, current, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.NamedCalls.Arguments
