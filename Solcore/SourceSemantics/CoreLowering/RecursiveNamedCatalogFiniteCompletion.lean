import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
import Solcore.Core.Correspondence

/-! All finite derivation grades have already been closed by catalog mutual
induction. Erasing independent Source/Core grades gives invocation meaning and
connects it to the actual machine. A finite source derivation supplies sufficient
native fuel; a completed native run supplies a source derivation. Fuel exhaustion
is not completion, and no source termination claim follows from static typing.
Initial catalog authority and real-entry static profiles remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Common
variable (runtime : Bool) {checked : Checked} {base : Base checked}
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
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
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
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves_with {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨size, measured⟩ := RecursiveNamedCallBounds.BodyOutcome.has_size trace
  exact invocation_preserves_bounded (functions := functions) (registry := registry) (faults := faults) size
    (fun child _ => RecursiveNamedCatalogMutualMeaning.preserves_at_with runtime functions extension faithful observations runtimeViews owners
      uninitialized missing escaped prefixMatches profiles child header member)
    caller member represented heaps measured (Nat.le_refl size)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_sized_with (budget size : Nat) (within : size ≤ budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨_, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    invocation_reflects_bounded (functions := functions) (registry := registry) (faults := faults) budget
      (fun child _ => RecursiveNamedCatalogMutualMeaning.reflects_at_with runtime functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)
      caller member represented heaps capture measured within
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_with
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨size, measured⟩ := evaluation_has_size completed
  exact reflects_sized_with runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps size size (Nat.le_refl size) capture measured

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel_with {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves_with runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles
      caller member represented heaps trace
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨capture, value, finalStore, finalMap, finalWorld, required, run, result, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects_with
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_with runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles
    caller member represented heaps capture (runStateful_evaluation_sound completed)

end Common

section Match
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

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves_match {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact preserves_with false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_sized_match (budget size : Nat) (within : size ≤ budget)
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (measured : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_sized_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps budget size within capture measured

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects_match
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps capture completed

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel_match {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact has_sufficient_fuel_with false functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects_match
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller member represented heaps capture completed

end Match

section Legacy
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
/-- The source derivation chooses its own grade. All callee meaning is
provided by the catalog theorem for every grade, rather than a fixed budget. -/
theorem preserves {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld,
        Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
          (header.code.rename capture.embedding.lift) value finalStore ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact preserves_match functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Reflection consumes only the original native completion and runtime
representation inputs. Its independent source grade is erased after induction. -/
theorem reflects
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {value : Value} {finalStore : Store}
    (completed : Evaluates (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact reflects_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps capture completed

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Sufficient fuel follows from a finite independent source execution,
including language faults represented by the normal result carrier. -/
theorem has_sufficient_fuel {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after) :
    ∃ capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial (header.code.rename capture.embedding.lift)
            (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) ∧
        FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
          finalMap finalWorld header.function.resultType header.output faults outcome value ∧
        CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
        LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
        AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
        Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact has_sufficient_fuel_match functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps trace

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- Every machine completion reflects. No relation between source and
native fuel, and no assumption of source termination, enters this consumer. -/
theorem completed_run_reflects
    (capture : Capture headers locations capturePrefix caller.authority.frameLocation header mapping world before store)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial (header.code.rename capture.embedding.lift)
        (DataPatternValues.packValues payloads :: capture.captured) store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program header.sourceBody header.function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix callerPrefix scope finalMap finalWorld after finalStore canonical) := by
  exact completed_run_reflects_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) caller member represented heaps capture completed

end Legacy
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogFiniteCompletion
