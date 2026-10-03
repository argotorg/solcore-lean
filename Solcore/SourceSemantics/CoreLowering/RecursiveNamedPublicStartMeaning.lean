import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootMeaning

/-! Public startup fixes the original recipe, store and encoded native prefix.
The views below return propositions only; they expose no executable state or
authority accessor. Independent source arguments and catalog Entry evidence
remain separate from the encoder's native typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Equality with the actual retained recipe, without an executable getter. -/
def ArtifactRecipe (artifact : Artifact) (recipe : Recipe) : Prop :=
  Artifact.casesOn (motive := fun _ => Prop) artifact (fun _ actual => actual = recipe)

/-- The original complete native world and store of this session. -/
def SessionState {artifact : Artifact} (session : Session artifact)
    (world : StoreTyping) (store : Store) : Prop :=
  Session.casesOn (motive := fun _ => Prop) session
    (fun _ actualWorld actualStore _ _ _ _ _ _ => actualWorld = world ∧ actualStore = store)

/-- Equality with the original machine state, used only inside proofs. -/
def CheckpointInitial {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (expression : Expr) (environment : Environment) (store : Store) : Prop :=
  Checkpoint.casesOn (motive := fun _ => Prop) checkpoint
    (fun _ _ _ state _ _ _ _ _ _ => state = .initial expression environment store)

/-- The actual metadata context retained after input encoding. -/
def CheckpointValues {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (values : SourceCoreCompatibleValues.Context) : Prop :=
  Checkpoint.casesOn (motive := fun _ => Prop) checkpoint
    (fun _ _ _ _ _ _ _ _ actual _ => actual = values)

theorem CheckpointInitial.native_done_iff {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {expression : Expr} {environment : Environment} {store : Store}
    (initial : CheckpointInitial checkpoint expression environment store)
    {fuel : Nat} {value : Core.Value} {finalStore : Store} :
    checkpoint.NativeDone fuel value finalStore ↔
      runStateful fuel (.initial expression environment store) = .done value finalStore := by
  cases checkpoint
  rename_i origin request world state stored typed extension registry values owner
  change _ = Core.State.initial expression environment store at initial
  change runStateful fuel state = _ ↔ _
  rw [initial]

/-- Every index denotes an actual startup value. All fields are proofs; no
source execution, body law or authority is introduced into this receipt. -/
structure StartAt {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List SourceCorePublicValues.Value) (boundaryFuel : Nat)
    (checkpoint : Checkpoint artifact) (recipe : Recipe) (root : Root recipe.compiled)
    (world : StoreTyping) (store : Store) (native : Environment)
    (encodedValues : SourceCoreCompatibleValues.Context) : Prop where
  recipe_eq : ArtifactRecipe artifact recipe
  state : SessionState session world store
  original : checkpoint.RootStart session key arguments boundaryFuel
  selected : recipe.roots.find? (fun root => decide (root.key = key)) = some root
  initial : CheckpointInitial checkpoint root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
  values : CheckpointValues checkpoint encodedValues
  typed : RuntimeEnvironmentHasTypes world native root.types recipe.compiled.indexed.layouts.definitions
  owner : encodedValues.checked = recipe.compiled.compatible.checked

/-- Successful startup exposes its exact native prefix and metadata context.
Native typing supplies no independent source representation of the inputs. -/
theorem actual_start {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments boundaryFuel = .ok checkpoint) :
    ∃ (recipe : Recipe) (root : Root recipe.compiled) (world : StoreTyping) (store : Store)
      (native : Environment) (encodedValues : SourceCoreCompatibleValues.Context),
      StartAt session key arguments boundaryFuel checkpoint recipe root world store native encodedValues := by
  have receipt := Session.start_root_receipt session accepted
  cases artifact
  rename_i authority recipe
  cases session
  rename_i sessionAuthority world store stored environmentTyped registry values owner sourcePrefix
  have original := receipt
  obtain ⟨root, selected, _, _, encoded, _, _, _, _, initial, _, valuesEq⟩ := receipt
  rcases encoded with ⟨encodedValues, encodedOwner, native, typed⟩
  refine ⟨recipe, root, world, store, native, encodedValues, ?_⟩
  exact ⟨rfl, ⟨rfl, rfl⟩, original, selected,
    by cases checkpoint; exact initial,
    by cases checkpoint; exact valuesEq, typed, encodedOwner⟩

/-- Real preparation and the original first-find membership select the full
Header. Neither a key nor native type tags replace this provenance. -/
theorem StartAt.selection {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments boundaryFuel checkpoint recipe root world store native encodedValues)
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : SourceSemantics.Program}
    {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    (complete : Complete headers) :
    ∃ header, RecursiveNamedPublicRootMeaning.RootSelection headers root header :=
  RecursiveNamedPublicRootMeaning.selection_of_recipe prepared
    (List.mem_of_find?_eq_some started.selected) complete

section Common
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogInvocationBounds
variable (runtime : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
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
      RecursiveNamedCatalogMutualMeaning.MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
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
theorem has_sufficient_fuel_with
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
  obtain ⟨value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    RecursiveNamedPublicRootMeaning.has_sufficient_fuel_with runtime functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles caller selected represented heaps executed
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel enough => started.initial.native_done_iff.mpr (completes fuel enough), result⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_with
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
  exact RecursiveNamedPublicRootMeaning.completed_reflects_program_with runtime functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected represented heaps
    admitted heapTyped argumentsTyped (started.initial.native_done_iff.mp completed)

end Common

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
theorem has_sufficient_fuel
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
  exact has_sufficient_fuel_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected started represented heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started represented heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program
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
  exact completed_reflects_program_with false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) caller selected started represented heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
