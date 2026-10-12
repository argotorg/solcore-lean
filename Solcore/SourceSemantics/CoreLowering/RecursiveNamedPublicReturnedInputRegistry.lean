import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! A successful public return retains the metadata registry from the actual
input encoding. Later calls can therefore derive their metadata conditions
from a prior startup and completion, without assuming a receiving registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
open Core Frontend SourceInference SourceCoreIndexedSession

theorem StartAt.returned_registry
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments inputFuel checkpoint recipe root world store native encodedValues)
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {value : Core.Value} {finalStore : Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore completion) :
    completion.session.RegistryAt encodedValues.registry := by
  obtain ⟨_done, _payload, _extension, _slots, _encoded, _decoded, _decode, _encode, _recovered,
    _sourceType, _boundary, _stored, _world, _authority, _prefix, returnedValues, _owner,
    _registry, _origin, _authenticated⟩ := succeeded
  have values := started.values
  cases checkpoint
  unfold Session.RegistryAt
  exact congrArg SourceCoreCompatibleValues.Context.registry (returnedValues.trans values)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning
