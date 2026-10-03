import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
import Solcore.Test.SourceCoreRecursiveNamedPublicRuntimeMeaning

/-! The public consumers take only pointwise static inputs with an interpreted
existential receipt. They keep independent source typing/staging/heap/Entry and
reuse existing public execution regressions. The negative receipt below shows
why an arbitrary Nonempty receipt cannot determine a diagnostic obligation. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicRuntimeFactoryMeaning
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicRuntimeFactoryMeaning
open CallableAncestryPairedLookup GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalogNativeContexts RecursiveNamedCatalogInvocationBounds
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
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.has_sufficient_fuel functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
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
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact RecursiveNamedPublicRuntimeFactoryMeaning.completed_reflects_program functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

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

variable
  (actual : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
  (result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
  (interpreted : result.extracted.diagnostics registry faults)
  (catalog : SignatureCatalogWellFormed values.checked.signatures)

include actual result interpreted in
theorem actual_package : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  Inputs.of_receipt actual result interpreted

include result interpreted catalog in
theorem same_receipt :
    ∃ profile : RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax administrative registry faults,
      profile.flow = result.flow ∧ HEq profile.tree result.extracted.tree :=
  ⟨result.profile catalog interpreted, rfl, HEq.rfl⟩

include result in
/-- The same Tree and compiler equalities permit a stronger, unsatisfied
obligation. Nonempty by itself cannot select an interpretable receipt. -/
theorem blocked_receipt :
    ∃ blocked : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative,
      blocked.flow = result.flow ∧ HEq blocked.extracted.tree result.extracted.tree ∧
      ∀ registry faults, ¬ blocked.extracted.diagnostics registry faults := by
  let blocked : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative := { result with extracted := { result.extracted with
    diagnostics := fun _ _ => False
    materialize := fun _ _ impossible => False.elim impossible } }
  exact ⟨blocked, rfl, HEq.rfl, fun _ _ impossible => impossible⟩

include actual result interpreted in
/-- This receipt is interpreted while a second receipt for the same emitted
code is not; callers need not establish diagnostics for every receipt. -/
theorem good_does_not_require_all :
    Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults ∧
    ¬ (∀ other : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative,
      other.extracted.diagnostics registry faults) := by
  refine ⟨Inputs.of_receipt actual result interpreted, ?_⟩
  obtain ⟨blocked, _, _, fails⟩ := blocked_receipt result
  intro all
  exact fails registry faults (all blocked)
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
theorem actual_extraction :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults :=
  RecursiveNamedPublicRuntimeFactoryMeaning.extract_source accepted selected definitions sameCache actualInputs complete globals entry
end ActualCache

/-- Codec representation preserves the complete independent source list. -/
abbrev exact_arguments := @RecursiveNamedPublicRuntimeMeaning.meanings_functional
/-- Duplicate mapping order and raw proxy metadata remain distinct. -/
abbrev duplicate_order := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.duplicate_order
abbrev raw_proxy := Tests.SourceCoreRecursiveNamedPublicRuntimeMeaning.raw_proxy

end Tests.SourceCoreRecursiveNamedPublicRuntimeFactoryMeaning
