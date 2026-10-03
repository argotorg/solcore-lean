import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! Consumers keep the actual startup state and encoded registry. Source input
representation and Entry authority are independent; no public encoder law or
result decoder is inferred from native typing. Runtime regressions are reused. -/
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicStartMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedPublicStartMeaning

abbrev actual_start := @RecursiveNamedPublicStartMeaning.actual_start
abbrev actual_selection := @StartAt.selection
abbrev original_native_state := @CheckpointInitial.native_done_iff

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
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
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations capturePrefix 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (represented : CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem actual_has_sufficient_fuel
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
  exact RecursiveNamedPublicStartMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem actual_completed_reflects_program
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
  exact RecursiveNamedPublicStartMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started represented heaps
    admitted heapTyped argumentsTyped completed

end Meaning

/-- Two views of the same checkpoint cannot replace any part of its initial state. -/
theorem same_initial {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {left right : Expr} {first second : Environment} {before after : Store}
    (one : CheckpointInitial checkpoint left first before)
    (two : CheckpointInitial checkpoint right second after) :
    Core.State.initial left first before = Core.State.initial right second after := by
  cases checkpoint
  change _ = Core.State.initial left first before at one
  change _ = Core.State.initial right second after at two
  exact one.symm.trans two

/-- Recipe equality preserves the full object, including roots and cached code. -/
theorem same_recipe {artifact : Artifact} {left right : Recipe}
    (one : ArtifactRecipe artifact left) (two : ArtifactRecipe artifact right) : left = right := by
  cases artifact
  exact one.symm.trans two

/-- Metadata values are the exact retained context, including every unused row. -/
theorem same_metadata {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {left right : SourceCoreCompatibleValues.Context}
    (one : CheckpointValues checkpoint left) (two : CheckpointValues checkpoint right) : left = right := by
  cases checkpoint
  exact one.symm.trans two

end Tests.SourceCoreRecursiveNamedPublicStartMeaning
