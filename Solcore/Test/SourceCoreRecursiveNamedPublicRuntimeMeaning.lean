import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning

/-! These consumers use the actual public checkpoint, retained full data receipt
and runtime profiles. Independent source arguments/types, heap, staging and Entry
remain explicit. Execution regressions reuse the existing public data, simple
input and Match runners; no second executable fixture is introduced. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_start_has_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_start
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations capturePrefix 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning
/-- Source arguments come from the real data codec; body meaning is not an input. -/
abbrev actual_encoded_arguments := @RecursiveNamedPublicRuntimeMeaning.source_arguments
/-- This consumer keeps the original body EvaluationSize and its enclosing bound. -/
abbrev original_body_reflects := @RecursiveNamedCatalogFiniteCompletion.reflects_sized_with
/-- The original successful session start retains every indexed receipt. -/
abbrev actual_start_receipt := @RecursiveNamedPublicStartMeaning.actual_start

/-- Duplicate keys retain their first value and the full ordered tail. -/
theorem duplicate_order :
    DataInput.publicValue (.mapping .bool .bool
      [(.bool true, .bool false), (.bool true, .bool true)]) ≠
    DataInput.publicValue (.mapping .bool .bool
      [(.bool true, .bool true), (.bool true, .bool false)]) := by
  simp [DataInput.publicValue, DataInput.publicEntries]

/-- Raw staging wrappers on proxy types cannot be identified by native erasure. -/
theorem raw_proxy :
    DataInput.publicValue (.proxy (.comptime .word)) ≠ DataInput.publicValue (.proxy .word) := by
  simp only [DataInput.publicValue]
  intro impossible
  cases impossible

/-- Empty source argument order is distinct from a single Unit argument. -/
theorem empty_not_unit : ([] : List SourceCorePublicValues.Value) ≠ [.unit] := by decide

/-- The independent meaning relation fixes the exact source list, including raw rows. -/
theorem same_arguments {publicValues : List SourceCorePublicValues.Value} {left right : List Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Meanings publicValues left)
    (second : RecursiveNamedPublicDataInputs.Meanings publicValues right) : left = right :=
  RecursiveNamedPublicRuntimeMeaning.meanings_functional first second

/-- Equal public inputs cannot change constructor metadata or payload order. -/
theorem same_constructor {value : SourceCorePublicValues.Value}
    {left right : DataConstructorInstantiation} {first second : List Dynamic.Value}
    (one : RecursiveNamedPublicDataInputs.Means value (.constructed left first))
    (two : RecursiveNamedPublicDataInputs.Means value (.constructed right second)) :
    left = right ∧ first = second :=
  Dynamic.Value.constructed.inj (RecursiveNamedPublicRuntimeMeaning.means_functional one two)

end Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning
