import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeProfileFactory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization

/-! Static body extraction connects to actual public execution through an
existential receipt whose own diagnostics are interpreted. A receipt is selected
only after this interpretation is supplied. All source input typing, staging,
heap and Entry conditions remain independent. Capture prefixes are zero; general
lambda/indirect/builtin closure assembly and Header inventory construction are
separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedCatalogInvocationBounds
open CallableAncestryPairedLookup

section Static
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {authenticated : Bool}

/-- Static compiler inputs and an extraction receipt with its own interpreted
diagnostics. This proposition neither quantifies over all receipts nor chooses
an arbitrary receipt before asking whether its diagnostics hold. The shared
indices fix the Header, compiler, read fuel, administrative context and emitted
body. The equalities below expose the same accepted lowering, projection and
source signatures; the result itself keeps the generated flow and its Tree. -/
def InputsWith (authenticated tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∃ (actual : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative),
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative,
      result.accepted = actual.accepted ∧ result.projection = actual.projection ∧
      result.signatures = actual.sourceSignatures ∧ result.extracted.diagnostics registry faults

/-- Package exactly this static extraction and this interpretation. Its accepted
body, generated flow, Tree and complete ledger remain in the receipt. -/
theorem InputsWith.of_receipt
    (actual : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
    (result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative)
    (interpreted : result.extracted.diagnostics registry faults) :
    InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  ⟨actual, result, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, interpreted⟩

/-- A good receipt is eliminated only inside a proposition. No data getter or
runtime law is added to the input package. -/
theorem InputsWith.profile
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults) :
    Nonempty (RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      administrative registry faults) := by
  obtain ⟨_, result, _, _, _, interpreted⟩ := inputs
  exact ⟨result.profile catalog interpreted⟩

abbrev Inputs (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  InputsWith false tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults

/-- Package exactly this static extraction and this interpretation. Its accepted
body, generated flow, Tree and complete ledger remain in the receipt. -/
theorem Inputs.of_receipt
    (actual : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
    (result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
    (interpreted : result.extracted.diagnostics registry faults) :
    Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  InputsWith.of_receipt actual result interpreted

/-- A good receipt is eliminated only inside a proposition. No data getter or
runtime law is added to the input package. -/
theorem Inputs.profile
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults) :
    Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      administrative registry faults) := by
  exact InputsWith.profile catalog inputs
end Static

section ActualCache
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
  (accepted : Recipe.prepare compiled = .ok recipe)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {header rootHeader : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : Root compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root rootHeader)
  (definitions : ambient.definitions = compiled.indexed.layouts.definitions)
  (sameCache : header.compiled.closures = compiled.indexed.secondPass.closures)

include accepted selected definitions sameCache in
/-- The real selected root supplies an indexed native entry. Its accepted
assembly types the same cached lambda; actual preparation supplies its support.
Neither fact supplies source typing or catalog authority. -/
theorem cached_facts :
    ∃ suffix : Core.Context,
      HasType (compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: suffix)
        (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
        header.named.signature.functionType ambient.definitions ∧
      NativeExpressionContextSupport.supported
        (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
        (compiled.indexed.base.globals.length + 1) = true := by
  obtain ⟨_, nativeEntry, member, _, _⟩ := selected
  have cached := header.cached
  rw [sameCache] at cached
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member cached
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
  exact ⟨_, by simpa only [← definitions] using typed,
    RecursiveNamedCatalogPreparedInitialization.supported_cached accepted cached⟩

section EvidenceExtraction
variable (authenticated : Bool)
variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem extract_source_with_evidence :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  obtain ⟨suffix, typed, support⟩ := cached_facts accepted selected definitions sameCache
  obtain ⟨result⟩ := RecursiveNamedCatalogRuntimeProfileFactory.extract_source_with actualInputs typed support complete globals entry
  exact ⟨result, fun _ interpreted => InputsWith.of_receipt actualInputs result interpreted⟩
end EvidenceExtraction

variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem extract_source :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  exact extract_source_with_evidence (authenticated := false) accepted selected definitions sameCache actualInputs complete globals entry
end ActualCache

section EvidenceMeaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable (authenticated : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
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
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      InputsWith authenticated (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
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


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel_evidence
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  classical
  let profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults := by
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
    have good := Classical.choose_spec (inputs header member entry)
    let result := Classical.choose good
    exact result.profile catalog (Classical.choose_spec good).2.2.2
  exact RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel_evidence authenticated functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_evidence
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
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  classical
  let profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults := by
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
    have good := Classical.choose_spec (inputs header member entry)
    let result := Classical.choose good
    exact result.profile catalog (Classical.choose_spec good).2.2.2
  exact RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end EvidenceMeaning

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
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
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
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      Inputs (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
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


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
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
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact has_sufficient_fuel_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
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
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact completed_reflects_program_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
