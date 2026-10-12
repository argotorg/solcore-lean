import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient

/-! A selected data argument is interpreted through its original codec inside
an arbitrary mixed input list. Adjacent handles do not change its Source
meaning. Native position, raw parameter type and final metadata all come from
the same actual startup. Ordered duplicate entries and raw annotations remain
those of the public data carrier. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Identify one exact encoded position without requiring other arguments to
be recursively data-only. Both native types and raw types retain that index. -/
theorem StartAt.data_input
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    (rawType : root.inputs[index]? = some expected)
    (found : arguments[index]? = some value) (data : DataPublic value) :
    ∃ payload type, native[index]? = some payload ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      EncodedDataInput recipe.compiled.compatible.checked encodedValues.registry expected value payload := by
  have receipt := started.original.data_input found data
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, atIndex, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  obtain ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩ := atIndex expected rawType
  have original := started.initial
  have actualValues := started.values
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values owner
  change values = encodedValues at actualValues
  change EncodedDataInput actualRecipe.compiled.compatible.checked values.registry expected value payload at encodedAt
  rw [actualValues] at encodedAt
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩

/-- Actual mixed startup supplies the selected data payload's representation.
Independent raw input typing supplies Source typing; the actual metadata
extension retains every encoded tag word at the receiving registry. -/
theorem StartAt.data_argument_represents
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    (functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
    (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap)
    (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (rawType : root.inputs[index]? = some expected) (found : arguments[index]? = some value)
    (inputTyped : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value expected)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    ∃ payload type, native[index]? = some payload ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world expected source payload type ∧
      Dynamic.ValueHasType context heap source expected := by
  have sourceTyped := RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType inputTyped meaning (heap := heap)
  obtain ⟨carrier, image, _typed⟩ := inputTyped
  obtain ⟨payload, type, payloadAt, typeAt, projected, encodedAt⟩ :=
    StartAt.data_input started rawType found ⟨carrier, image⟩
  obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
  have same : actual = payload := Option.some.inj (actualAt.symm.trans payloadAt)
  subst actual
  obtain ⟨interpreted, interpretedAt, represented⟩ :=
    RecursiveNamedPublicDataInputs.EncodedDataInput.represents functions mapping world encodedAt projected
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).basePrefix typed
  have sameSource := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
  subst interpreted
  exact ⟨payload, type, payloadAt, typeAt, projected,
    represented.extend metadata (.refl _) (.refl _), sourceTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedDataArgumentReceipts
