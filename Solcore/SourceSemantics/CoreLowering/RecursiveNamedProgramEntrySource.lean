import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.Dynamic.Program
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion

/-! The independent whole-program entry selects the Header's exact body.
Admission, raw argument typing and initial heap typing remain source facts.
This connects ProgramEvaluates to the body relation used by Core meaning;
the actual completed body machine is connected below. Public session
preparation remains a separate connection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

def entry (header : Header prepared values definitions program) (arguments : List Dynamic.Value) :
    Dynamic.ProgramEntry := ⟨header.instantiation, header.function.evidence, arguments⟩

/-- The real input binders determine argument types. Source heap validity and
argument validity are independent of native representation or decoding. -/
theorem entry_valid (header : Header prepared values definitions program)
    {before : Dynamic.Heap} {arguments : List Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    Dynamic.ProgramEntryValid program (entry header arguments) before header.sourceBody := by
  have extended := header.extended
  rw [header.frame.source, header.frame.context, header.frame.parameters] at extended
  have typesEq := Dynamic.MonoBindersExtend.bodyTypes_eq extended
  refine ⟨header.frame.instantiated, header.frame.covers, ?_, ?_⟩
  · simpa only [header.frame.context] using heapTyped
  · simpa only [entry, typesEq, header.frame.context] using argumentsTyped

/-- A whole-program source execution carries its own admission and entry
validation. Body uniqueness identifies its hidden instance with the Header. -/
theorem invokes_from_program (header : Header prepared values definitions program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (evaluated : Dynamic.ProgramEvaluates program (entry header arguments) before value after) :
    Dynamic.BodyInvokes program header.sourceBody header.function.evidence before arguments value after := by
  cases evaluated with
  | run admitted valid invoked =>
    have same := BuiltinNamedCalls.instantiation_unique_of_wellFormed admitted.staticallyValid
      valid.instantiates header.frame.instantiated
    cases same
    exact invoked

/-- A body execution becomes a whole-program execution only after genuine
source staging admission and raw external-input validity have been supplied. -/
theorem program_from_invokes (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (invoked : Dynamic.BodyInvokes program header.sourceBody header.function.evidence before arguments value after) :
    Dynamic.ProgramEvaluates program (entry header arguments) before value after :=
  .run admitted (entry_valid header heapTyped argumentsTyped) invoked

/-- The successful whole-program observation is exactly the real Header body
observation under the independent entry conditions. Faults retain BodyFaults;
they are not encoded as successful ProgramEvaluates. -/
theorem program_iff_body_value (header : Header prepared values definitions program)
    (admitted : Staging.ProgramHasStages program)
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {value : Dynamic.Value}
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types) :
    Dynamic.ProgramEvaluates program (entry header arguments) before value after ↔
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments (.value value) after := by
  constructor
  · intro evaluated
    exact .value (invokes_from_program header evaluated)
  · intro outcome
    cases outcome with
    | value invoked => exact program_from_invokes header admitted heapTyped argumentsTyped invoked

section Evidence
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RecursiveNamedCatalogMutualMeaning.MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel_evidence {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (evaluated : Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults (.value sourceValue) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have invoked := RecursiveNamedProgramEntrySource.invokes_from_program header evaluated
  exact RecursiveNamedCatalogFiniteCompletion.has_sufficient_fuel_with_evidence authenticated runtime functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles caller member represented heaps (.value invoked)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- A native success reconstructs an independent whole-program source run.
Source staging and raw initial-input validity are separate entry conditions. -/
theorem native_success_reflects_program_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {payload : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done (.inRight .word payload) finalStore) :
    ∃ sourceValue after finalMap finalWorld,
      Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry functions).Represents
        finalMap finalWorld header.function.resultType sourceValue payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨outcome, after, finalMap, finalWorld, traced, result, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.completed_run_reflects_with_evidence authenticated runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller member represented heaps capture completed
  cases result with
  | value representedResult =>
    cases traced with
    | value invoked =>
      exact ⟨_, after, finalMap, finalWorld,
        RecursiveNamedProgramEntrySource.program_from_invokes header admitted heapTyped argumentsTyped invoked,
        representedResult, finalHeaps, maps, worlds, administrative, metadata, finalEntry⟩

end Evidence

section Native
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
theorem program_has_sufficient_native_fuel {sourceValue : Dynamic.Value} {after : Dynamic.Heap}
    (evaluated : Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults (.value sourceValue) value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact program_has_sufficient_native_fuel_evidence false false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match.toMatchProfileWith) caller member represented heaps evaluated

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- A native success reconstructs an independent whole-program source run.
Source staging and raw initial-input validity are separate entry conditions. -/
theorem native_success_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {payload : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done (.inRight .word payload) finalStore) :
    ∃ sourceValue after finalMap finalWorld,
      Dynamic.ProgramEvaluates program (RecursiveNamedProgramEntrySource.entry header arguments) before sourceValue after ∧
      (CompatibleAmbientHeap.payloadModel values.checked registry functions).Represents
        finalMap finalWorld header.function.resultType sourceValue payload header.output ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact native_success_reflects_program_evidence false false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match.toMatchProfileWith) caller member represented heaps admitted heapTyped argumentsTyped capture completed

end Native

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramEntrySource
