import Solcore.SourceSemantics.CoreLowering.RecursiveNamedProgramCallMeaning

/-! Public Match consumers retain real caller state, raw source admission and
argument-code evaluation. They obtain every callee law from the same static
BodyState-indexed Match profile. Existing runtime suites cover emitted calls,
recursive Match bodies, source faults and public resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedMatchProgramMeaning
open Solcore SourceSemantics SourceSemantics.CoreLowering
open Core Frontend SourceInference RecursiveNamedCatalog CallableAncestryPairedLookup

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
theorem actual_call_has_fuel
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
  exact RecursiveNamedProgramCallMeaning.emitted_call_has_sufficient_fuel_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps agrees argumentsEvaluated executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- An original completed call exposes the same smaller body derivation.
Reflection uses the independent source entry conditions and never a source
execution or body-preservation law as an input. -/
theorem actual_completed_call
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
  exact RecursiveNamedProgramCallMeaning.completed_call_reflects_program_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps admitted heapTyped argumentsTyped agrees argumentsEvaluated completed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller member represented heaps in
/-- The original native body grade stays strictly below its enclosing call. -/
theorem original_body_reflects (budget size : Nat) (strict : size < budget)
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
  exact RecursiveNamedCatalogFiniteCompletion.reflects_sized_match functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller member represented heaps
    budget size (Nat.le_of_lt strict) capture measured

/-- Program outcomes include success and language fault under the same profile. -/
abbrev program_has_fuel := @RecursiveNamedProgramOutcomeMeaning.program_has_sufficient_native_fuel_match

/-- Native completion supplies a source outcome without prior source execution. -/
abbrev program_reflects := @RecursiveNamedProgramOutcomeMeaning.completed_run_reflects_program_match

end Tests.SourceCoreRecursiveNamedMatchProgramMeaning
