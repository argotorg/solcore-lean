import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! Metadata-bearing input arguments come from the original successful public
encoder. Their exact metadata words are transported by a genuine extension of
the encoded registry to the receiving registry. This extension remains an
explicit static condition; two extensions of a common registry do not imply it.

The independent structural input certificate retains raw proxy inner types,
constructor instantiations, mapping types and ordered duplicate entries. It
does not contain a Source value typing judgment or a body execution law.
Accepted encoding alone permits more inputs because runtimeType erases nested
comptime annotations. The certificate rules out those raw mismatches.

The two final endpoints are consumed by initialized public success/failure and
Word bounds. Handles remain outside this recursively data-only input family.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open CallableIndexedParameterCertificates (Binding)

mutual
  /-- Raw structural typing of a public data carrier, independent of heaps,
  native tags, payload representations and Source execution. -/
  inductive DataTyped (context : SourceSemantics.Context) :
      SourceCoreDataValues.Value → TypeSystem.Ty → Prop where
    | unit : DataTyped context .unit .unit
    | bool (value : Bool) : DataTyped context (.bool value) .bool
    | word (value : Word) : DataTyped context (.word value) .word
    | integer (value : Int) : DataTyped context (.integer value) .integer
    | product {left right : SourceCoreDataValues.Value} {leftType rightType : TypeSystem.Ty}
        (first : DataTyped context left leftType) (second : DataTyped context right rightType) :
        DataTyped context (.product left right) (.product leftType rightType)
    | proxy (inner : TypeSystem.Ty) : DataTyped context (.proxy inner) (.proxy inner)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List SourceCoreDataValues.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (typed : DataTypes context payloads metadata.payloadTypes) :
        DataTyped context (.constructed metadata payloads) metadata.resultType
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)}
        (typed : DataEntriesTyped context key value entries) :
        DataTyped context (.mapping key value entries) (.mapping key value)
    | comptime {value : SourceCoreDataValues.Value} {type : TypeSystem.Ty}
        (typed : DataTyped context value type) : DataTyped context value (.comptime type)

  inductive DataTypes (context : SourceSemantics.Context) :
      List SourceCoreDataValues.Value → List TypeSystem.Ty → Prop where
    | nil : DataTypes context [] []
    | cons {value : SourceCoreDataValues.Value} {values : List SourceCoreDataValues.Value}
        {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        (head : DataTyped context value type) (tail : DataTypes context values types) :
        DataTypes context (value :: values) (type :: types)

  inductive DataEntriesTyped (context : SourceSemantics.Context) :
      TypeSystem.Ty → TypeSystem.Ty → List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : DataEntriesTyped context key value []
    | entry {key value : TypeSystem.Ty} {first second : SourceCoreDataValues.Value}
        {rest : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)}
        (firstTyped : DataTyped context first key) (secondTyped : DataTyped context second value)
        (restTyped : DataEntriesTyped context key value rest) :
        DataEntriesTyped context key value ((first, second) :: rest)
end

/-- The structural certificate constructs an independent Source interpretation
and its raw typing at any heap. No compiler or encoder result is used here. -/
theorem DataTyped.meaning_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {carrier : SourceCoreDataValues.Value} {type : TypeSystem.Ty}
    (typed : DataTyped context carrier type) :
    ∃ source, DataPayloadEncoding.Means carrier source ∧
      Dynamic.ValueHasType context heap source type := by
  induction typed using DataTyped.rec
    (motive_2 := fun carriers types _ => ∃ sources,
      DataPayloadEncoding.Meanings carriers sources ∧ Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value carriers _ => ∃ sources,
      DataPayloadEncoding.EntryMeanings carriers sources ∧
        Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | bool value => exact ⟨.bool value, .bool value, .bool value⟩
  | word value => exact ⟨.word value, .word value, .word value⟩
  | integer value => exact ⟨.integer value, .integer value, .integer value⟩
  | product _ _ first second =>
      obtain ⟨left, leftMeaning, leftTyped⟩ := first
      obtain ⟨right, rightMeaning, rightTyped⟩ := second
      exact ⟨.product left right, .product leftMeaning rightMeaning, .product leftTyped rightTyped⟩
  | proxy inner => exact ⟨.proxy inner, .proxy inner, .proxy inner⟩
  | constructed valid _ ih =>
      obtain ⟨sources, meanings, typed⟩ := ih
      exact ⟨.constructed _ sources, .constructed meanings, .constructed valid typed⟩
  | mapping _ ih =>
      obtain ⟨sources, meanings, typed⟩ := ih
      exact ⟨.mapping _ _ sources, .mapping meanings, .mapping typed⟩
  | comptime _ ih =>
      obtain ⟨source, meaning, typed⟩ := ih
      exact ⟨source, meaning, .comptime typed⟩
  | nil => exact ⟨[], .nil, .nil⟩
  | cons _ _ head tail =>
      obtain ⟨source, meaning, typed⟩ := head
      obtain ⟨sources, meanings, typings⟩ := tail
      exact ⟨source :: sources, .cons meaning meanings, .cons typed typings⟩
  | empty key value => exact ⟨[], .empty, .nil key value⟩
  | entry _ _ _ first second rest =>
      obtain ⟨left, leftMeaning, leftTyped⟩ := first
      obtain ⟨right, rightMeaning, rightTyped⟩ := second
      obtain ⟨sources, meanings, typings⟩ := rest
      exact ⟨(left, right) :: sources, .prepend leftMeaning rightMeaning meanings,
        .cons leftTyped rightTyped typings⟩

/-- Exact raw data typing of one public value. This records its literal public
carrier, rather than wrapping a desired Dynamic.ValueHasType judgment. -/
def PublicDataTyped (context : SourceSemantics.Context) (value : SourceCorePublicValues.Value)
    (type : TypeSystem.Ty) : Prop :=
  ∃ carrier, value = DataInput.publicValue carrier ∧ DataTyped context carrier type

inductive PublicDataTypes (context : SourceSemantics.Context) :
    List SourceCorePublicValues.Value → List TypeSystem.Ty → Prop where
  | nil : PublicDataTypes context [] []
  | cons {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
      {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      (head : PublicDataTyped context value type) (tail : PublicDataTypes context values types) :
      PublicDataTypes context (value :: values) (type :: types)

theorem PublicDataTypes.data {context : SourceSemantics.Context}
    {values : List SourceCorePublicValues.Value} {types : List TypeSystem.Ty}
    (typed : PublicDataTypes context values types) : ∀ value ∈ values, DataPublic value := by
  induction typed with
  | nil => intro value member; cases member
  | cons head _ ih =>
      intro value member
      rcases List.mem_cons.mp member with same | member
      · subst value
        obtain ⟨carrier, image, _⟩ := head
        exact ⟨carrier, image⟩
      · exact ih value member

theorem PublicDataTyped.source_hasType {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : SourceCorePublicValues.Value} {type : TypeSystem.Ty} {source : Dynamic.Value}
    (typed : PublicDataTyped context value type)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    Dynamic.ValueHasType context heap source type := by
  obtain ⟨carrier, image, typed⟩ := typed
  obtain ⟨actual, interpreted, actualTyped⟩ := typed.meaning_typed (heap := heap)
  have same := RecursiveNamedPublicRuntimeMeaning.means_functional
    (show RecursiveNamedPublicDataInputs.Means value actual from ⟨carrier, image, interpreted⟩) meaning
  cases same
  exact actualTyped

theorem PublicDataTypes.source_haveTypes {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {values : List SourceCorePublicValues.Value} {types : List TypeSystem.Ty}
    {sources : List Dynamic.Value} (typed : PublicDataTypes context values types)
    (meanings : RecursiveNamedPublicDataInputs.Meanings values sources) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction typed generalizing sources with
  | nil => cases meanings; exact .nil
  | cons head _ ih =>
      cases meanings with
      | cons meaning rest => exact .cons (head.source_hasType meaning) (ih rest)

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
    (programTyped : ProgramWellFormed program)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types) :
    ∃ arguments, RecursiveNamedPublicDataInputs.Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  obtain ⟨arguments, meanings, represented⟩ :=
    RecursiveNamedPublicDataInputs.StartAt.data_arguments functions mapping started selected
      typed.data sameChecked programTyped record
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
    (programTyped : ProgramWellFormed program)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (typed : PublicDataTypes header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, actualTyped⟩ :=
    data_arguments_receiving functions receiving mapping before started selected sameChecked programTyped metadata typed
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional interpreted meanings
  cases same
  exact ⟨represented, actualTyped⟩

/-- The encoder's erased comparison cannot justify raw proxy typing. -/
example : SourceCoreRawMetadata.runtimeType (.proxy (.comptime .word)) =
    SourceCoreRawMetadata.runtimeType (.proxy .word) := rfl

example (context : SourceSemantics.Context) :
    ¬ PublicDataTyped context (.proxy (.comptime .word)) (.proxy .word) := by
  intro typed
  have meaning : RecursiveNamedPublicDataInputs.Means (.proxy (.comptime .word))
      (.proxy (.comptime .word)) :=
    ⟨.proxy (.comptime .word), by simp only [DataInput.publicValue], .proxy _⟩
  have impossible := typed.source_hasType (heap := ⟨[]⟩) meaning
  cases impossible

/-- Matching raw proxy annotations have a genuine structural certificate. -/
example (context : SourceSemantics.Context) :
    PublicDataTyped context (.proxy (.comptime .word)) (.proxy (.comptime .word)) :=
  ⟨.proxy (.comptime .word), by simp only [DataInput.publicValue], .proxy _⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
