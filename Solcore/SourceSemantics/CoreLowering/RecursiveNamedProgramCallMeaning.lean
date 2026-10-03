import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramOutcomeMeaning
import Solcore.SourceSemantics.CoreLowering.CoreContinuationSize

/-! Emitted optional-cell calls select the real catalog capture after their
native argument bundle succeeds. This connects the admitted source program
observation to the call wrapper used at public roots. Input encoding, the
actual root factory equation and argument-bundle evaluation remain separate
receipts; no capture is inferred from a native type or decoded value. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup
section Match
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
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {callerPrefix : Nat}
  (caller : Entry headers locations capturePrefix callerPrefix scope mapping world before store canonical)
  {header : Header prepared values ambient.definitions program} (member : header ∈ headers)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel_match
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  have traced := RecursiveNamedProgramOutcomeMeaning.body_from_program header executed
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.preserves_match functions extension faithful observations runtimeViews
      executed.program_well_formed.function_ids uninitialized missing escaped prefixMatches profiles caller member represented heaps traced
  have selected := OptionalCell.read_success reason
    (show Evaluates (DataPatternValues.packValues payloads :: actual) store
      (.var (ξ (scope.length + callerPrefix + header.slot) + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (locations header)) store
      from .var (agrees (caller.globals header member))) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated selected evaluated
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel called
  exact ⟨value, finalStore, finalMap, finalWorld, required, run, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program_match
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨capture⟩ := caller.authority.captures header member
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated (agrees (caller.globals header member)) capture.read measured
  obtain ⟨outcome, after, finalMap, finalWorld, traced, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    RecursiveNamedCatalogFiniteCompletion.reflects_sized_match functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller member represented heaps
      size bodySize (Nat.le_of_lt smaller) capture bodyEvaluation
  exact ⟨outcome, after, finalMap, finalWorld,
    RecursiveNamedProgramOutcomeMeaning.program_from_body header admitted heapTyped argumentsTyped traced,
    result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

end Match

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


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The real global reference and capture supply the emitted call's read.
Source execution supplies the body; original native completeness supplies a
budget for the complete call, including argument packing and dispatch. -/
theorem emitted_call_has_sufficient_fuel
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreCalls.call header.named.signature
          (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact emitted_call_has_sufficient_fuel_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem completed_call_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {actual : Environment} {ξ : Renaming} (agrees : EnvironmentsAgree ξ canonical actual)
    {argumentCode : Expr} {reason : Word}
    (argumentsEvaluated : Evaluates actual store argumentCode
      (.inRight .word (DataPatternValues.packValues payloads)) store)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : runStateful fuel
      (.initial (SourceCoreCalls.call header.named.signature
        (ξ (scope.length + callerPrefix + header.slot)) argumentCode reason) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_call_reflects_program_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

end Native
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning
