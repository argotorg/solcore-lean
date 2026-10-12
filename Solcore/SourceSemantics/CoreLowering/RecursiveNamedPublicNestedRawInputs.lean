import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! Exact raw input receipts from the original public startup. The selected
payload, native projection and metadata extension retain the same argument
position and the actual checkpoint; this module adds no semantic premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- The actual selected input keeps its own starting registry and the genuine
extension through all later inputs into the startup's final registry. -/
theorem StartAt.raw_input
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    (rawType : root.inputs[index]? = some expected)
    (found : arguments[index]? = some value) :
    ∃ (before : SourceCoreRawMetadata.Registry)
      (encoded : SourceCoreCompatibleValues.Extended before Core.Value) (type : Core.Ty),
      native[index]? = some encoded.value ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      before.signatures = recipe.compiled.compatible.checked.signatures ∧
      session.RawEncodedAt fuel before expected value encoded ∧
      SourceCoreRawMetadata.Extends encoded.registry encodedValues.registry := by
  have receipt := started.original.raw_input found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, atIndex, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  obtain ⟨before, encoded, type, payloadAt, typeAt, projected, owner, encodedAt, extended⟩ :=
    atIndex expected rawType
  have original := started.initial
  have actualValues := started.values
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values valueOwner
  change values = encodedValues at actualValues
  change SourceCoreRawMetadata.Extends encoded.registry values.registry at extended
  rw [actualValues] at extended
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact ⟨before, encoded, type, payloadAt, typeAt, projected, owner, encodedAt, extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
