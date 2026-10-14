import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataInputs
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedCatalog
open CallableIndexedParameterCertificates (Binding)
open RecursiveNamedPublicDataArgumentReceipts
private theorem arguments_metadata {checked : SourceCoreCompatibleCatalog.Checked}
    {encoded receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked encoded functions) mapping world bindings sources native)
    (metadata : SourceCoreRawMetadata.Extends encoded receiving) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked receiving functions) mapping world bindings sources native := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (CompatiblePayload.ValueRep.extend head metadata (.refl _) (.refl _)) ih

/-- The original encoder supplies both source meaning and payload representation.
Raw input correctness and exact registry extension construct the two argument
premises at the receiving metadata used by the initialized public bounds. -/
theorem data_arguments_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types) :
    ∃ arguments, RecursiveNamedPublicDataInputs.Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  obtain ⟨arguments, meanings, represented⟩ :=
    SelectedCompilationPublicDataInputs.StartAt.data_arguments functions mapping started selected
      typed.data sameChecked certified record
  exact ⟨arguments, meanings, arguments_metadata represented metadata, typed.source_haveTypes meanings⟩

/-- Match caller-supplied independent Source arguments to the actual encoder's
arguments before the initialized public Word preservation theorem is applied. -/
theorem data_arguments_at_receiving
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program}
    {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
    (functions : FunctionModel values.checked.catalog ambient)
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (before : Dynamic.Heap)
    (started : StartAt session key publicArguments fuel checkpoint recipe root world store native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, actualTyped⟩ :=
    data_arguments_receiving functions receiving mapping before started selected sameChecked certified metadata typed
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional interpreted meanings
  cases same
  exact ⟨represented, actualTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDataArgumentReceipts
