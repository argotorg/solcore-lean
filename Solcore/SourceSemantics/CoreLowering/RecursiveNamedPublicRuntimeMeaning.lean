import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs

/-! The actual public startup and full data codec receipt supply source arguments
for the runtime catalog family. Every raw constructor/proxy type and ordered
mapping row is retained. Source input typing, staging, heap correspondence and
catalog authority remain independent conditions. Opaque handles and automatic
whole-body profile extraction are separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
open Core Frontend SourceInference
open SourceCoreIndexedSession

/- The public carrier retains all raw metadata and the original list order. -/
mutual
  private theorem public_value_injective (left right : SourceCoreDataValues.Value)
      (same : DataInput.publicValue left = DataInput.publicValue right) : left = right := by
    cases hleft : left <;> cases right <;> simp only [hleft, DataInput.publicValue] at same <;> try (solve | cases same)
    case unit.unit => rfl
    case bool.bool a b => cases same; rfl
    case word.word a b => cases same; rfl
    case integer.integer a b => cases same; rfl
    case proxy.proxy a b => cases same; rfl
    case product.product a b c d =>
      obtain ⟨first, second⟩ := SourceCorePublicValues.Value.product.inj same
      rw [public_value_injective a c first, public_value_injective b d second]
    case constructed.constructed a xs b ys =>
      obtain ⟨metadata, payloads⟩ := SourceCorePublicValues.Value.constructed.inj same
      rw [metadata, public_values_injective xs ys payloads]
    case mapping.mapping k v xs k' v' ys =>
      obtain ⟨key, value, entries⟩ := SourceCorePublicValues.Value.mapping.inj same
      rw [key, value, public_entries_injective xs ys entries]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega

  private theorem public_values_injective (left right : List SourceCoreDataValues.Value)
      (same : DataInput.publicValues left = DataInput.publicValues right) : left = right := by
    cases hleft : left with
    | nil => cases right <;> simp_all [DataInput.publicValues]
    | cons head tail =>
      cases right with
      | nil => simp [hleft, DataInput.publicValues] at same
      | cons other rest =>
        simp only [hleft, DataInput.publicValues] at same
        obtain ⟨first, next⟩ := List.cons.inj same
        rw [public_value_injective head other first, public_values_injective tail rest next]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega

  private theorem public_entries_injective (left right : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value))
      (same : DataInput.publicEntries left = DataInput.publicEntries right) : left = right := by
    cases hleft : left with
    | nil =>
      cases right with
      | nil => rfl
      | cons pair rest => cases pair; simp [hleft, DataInput.publicEntries] at same
    | cons head tail =>
      cases head with
      | mk key value =>
        cases right with
        | nil => simp [hleft, DataInput.publicEntries] at same
        | cons other rest =>
          cases other with
          | mk otherKey otherValue =>
            simp only [hleft, DataInput.publicEntries] at same
            obtain ⟨first, next⟩ := List.cons.inj same
            obtain ⟨keys, values⟩ := Prod.mk.inj first
            rw [public_value_injective key otherKey keys,
              public_value_injective value otherValue values, public_entries_injective tail rest next]
  termination_by sizeOf left
  decreasing_by all_goals simp_all; omega
end

theorem means_functional {value : SourceCorePublicValues.Value} {left right : Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Means value left)
    (second : RecursiveNamedPublicDataInputs.Means value right) : left = right := by
  obtain ⟨firstCarrier, firstImage, firstMeaning⟩ := first
  obtain ⟨secondCarrier, secondImage, secondMeaning⟩ := second
  have same := public_value_injective firstCarrier secondCarrier (firstImage.symm.trans secondImage)
  cases same
  exact DataPayloadEncoding.Means.functional firstMeaning secondMeaning

theorem meanings_functional {values : List SourceCorePublicValues.Value} {left right : List Dynamic.Value}
    (first : RecursiveNamedPublicDataInputs.Meanings values left)
    (second : RecursiveNamedPublicDataInputs.Meanings values right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => rw [means_functional head other, ih rest]


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


include selected started data sameChecked programTyped record meanings in
/-- Actual encoding supplies the same independently interpreted source arguments.
Native carrier equality is not used to infer a source type or authority. -/
theorem source_arguments :
    CallableIndexedParameterMeaning.Arguments (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
      mapping world header.bindings arguments payloads := by
  obtain ⟨actual, related, represented⟩ := RecursiveNamedPublicDataInputs.StartAt.data_arguments functions mapping started selected data sameChecked programTyped record
  have same := meanings_functional related meanings
  exact same ▸ represented


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
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
  exact RecursiveNamedPublicStartMeaning.has_sufficient_fuel_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started
    (source_arguments functions selected started data sameChecked programTyped record meanings) heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps in
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
  exact RecursiveNamedPublicStartMeaning.completed_reflects_program_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started
    (source_arguments functions selected started data sameChecked programTyped record meanings) heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
