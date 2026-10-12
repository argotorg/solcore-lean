import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! The original successful public encoder supplies scalar/product arguments
at the selected Header's raw types. Deep Source typing follows structurally
from the same SimpleInput receipt, including nested comptime wrappers.
The representation uses the receiving body's registry directly: these values
carry no metadata tags, so no equality or extension of encoder and receiving
registries is needed. Handles and metadata-bearing data are outside this unit.
The final endpoint matches supplied independent data meanings, allowing the
initialized public consumer to supply neither argument typing nor representation.
-/
set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicSimpleInputs (Means Meanings)
open CallableIndexedParameterCertificates (Binding)

/-- Removing comptime from a scalar/product type preserves its shape; restoring
the original raw type uses genuine Source constructors rather than Core typing. -/
private theorem restore_simple_type
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {type : TypeSystem.Ty} {encoded : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (meaning : Means encoded source)
    (typed : Dynamic.ValueHasType context heap source (SourceCoreRawMetadata.runtimeType type)) :
    Dynamic.ValueHasType context heap source type := by
  induction type generalizing encoded source with
  | «variable» id => exact typed
  | parameter id => exact typed
  | constructor id => exact typed
  | error => exact typed
  | application function argument _functionIH _argumentIH =>
      cases meaning <;> cases typed
  | function parameter result _parameterIH _resultIH =>
      cases meaning <;> cases typed
  | mapping key value _keyIH _valueIH =>
      cases meaning <;> cases typed
  | proxy inner _ih =>
      cases meaning <;> cases typed
  | product left right leftIH rightIH =>
      cases meaning with
      | unit => cases typed
      | bool => cases typed
      | word => cases typed
      | integer => cases typed
      | product first second =>
          cases typed with
          | product leftTyped rightTyped =>
              exact .product (leftIH first leftTyped) (rightIH second rightTyped)
  | comptime inner ih => exact .comptime (ih meaning typed)

/-- The raw Source type comes from the original accepted SimpleInput, at any
Source heap and context. No heap lookup or native-value typing is assumed. -/
theorem simple_input_hasType
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {expected : TypeSystem.Ty} {encoded : SourceCorePublicValues.Value}
    {native : Core.Value} {source : Dynamic.Value}
    (input : SimpleInput expected encoded native) (meaning : Means encoded source) :
    Dynamic.ValueHasType context heap source expected := by
  induction input generalizing source with
  | unit view =>
      cases meaning
      exact restore_simple_type .unit (view.symm ▸ .unit)
  | bool value view =>
      cases meaning
      exact restore_simple_type (.bool value) (view.symm ▸ .bool value)
  | word value view =>
      cases meaning
      exact restore_simple_type (.word value) (view.symm ▸ .word value)
  | integer value view =>
      cases meaning
      exact restore_simple_type (.integer value) (view.symm ▸ .integer value)
  | product view _left _right leftIH rightIH =>
      cases meaning with
      | product first second =>
          exact restore_simple_type (.product first second)
            (view.symm ▸ .product (leftIH first) (rightIH second))

theorem simple_inputs_haveTypes
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {types : List TypeSystem.Ty} {encoded : List SourceCorePublicValues.Value}
    {native : Core.Environment} {sources : List Dynamic.Value}
    (inputs : SimpleInputs types encoded native) (meanings : Meanings encoded sources) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction inputs generalizing sources with
  | nil => cases meanings; exact .nil
  | cons head _tail ih =>
      cases meanings with
      | cons first rest => exact .cons (simple_input_hasType head first) (ih rest)

private theorem simple_means_data
    {encoded : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (meaning : Means encoded source) : RecursiveNamedPublicDataInputs.Means encoded source := by
  induction meaning with
  | unit => exact ⟨.unit, by simp only [DataInput.publicValue], .unit⟩
  | bool value => exact ⟨.bool value, by simp only [DataInput.publicValue], .bool value⟩
  | word value => exact ⟨.word value, by simp only [DataInput.publicValue], .word value⟩
  | integer value => exact ⟨.integer value, by simp only [DataInput.publicValue], .integer value⟩
  | product _first _second firstIH secondIH =>
      obtain ⟨left, leftEq, leftMeaning⟩ := firstIH
      obtain ⟨right, rightEq, rightMeaning⟩ := secondIH
      refine ⟨.product left right, ?_, .product leftMeaning rightMeaning⟩
      rw [leftEq, rightEq]
      simp only [DataInput.publicValue]

private theorem simple_meanings_data
    {encoded : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (meanings : Meanings encoded sources) : RecursiveNamedPublicDataInputs.Meanings encoded sources := by
  induction meanings with
  | nil => exact .nil
  | cons head _tail ih => exact .cons (simple_means_data head) ih

/-- The original StartAt and selected raw signature construct both argument
premises for the receiving model. Its registry is independent of encodedValues. -/
theorem simple_arguments_receiving
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
    (simple : ∀ argument ∈ publicArguments, SimplePublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program) :
    ∃ arguments, Meanings publicArguments arguments ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
        mapping world header.bindings arguments native ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have inputs := RecursiveNamedPublicSimpleInputs.StartAt.simple_inputs started simple
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1] at inputs
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header sameChecked programTyped record
  obtain ⟨arguments, meanings, represented⟩ :=
    RecursiveNamedPublicSimpleInputs.SimpleInputs.arguments (registry := receiving)
      functions mapping world inputs projected
  have typed := simple_inputs_haveTypes (context := header.function.context) (heap := before) inputs meanings
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨arguments, meanings, represented, typesEq ▸ typed⟩

/-- Match independently supplied data arguments to those issued by the original
simple encoder, so the actual public Word trace needs no opaque argument premise. -/
theorem simple_arguments_at_receiving
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
    (simple : ∀ argument ∈ publicArguments, SimplePublic argument)
    (sameChecked : values.checked = recipe.compiled.compatible.checked)
    (programTyped : ProgramWellFormed program)
    {arguments : List Dynamic.Value}
    (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  obtain ⟨actual, interpreted, represented, typed⟩ :=
    simple_arguments_receiving functions receiving mapping before started selected simple sameChecked programTyped
  have same := RecursiveNamedPublicRuntimeMeaning.meanings_functional
    (simple_meanings_data interpreted) meanings
  cases same
  exact ⟨represented, typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleArgumentReceipts
