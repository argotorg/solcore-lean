import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! Exact Bool output follows from the actual public encoder and the independent
Source/native result. No decoder success or Source value law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload
open SourceCoreIndexedSession

private theorem encoded_bool_value {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    {value : Bool}
    (accepted : session.RawEncodedAt fuel registry .bool publicValue encoded)
    (payload : encoded.value = .bool value) : publicValue = .bool value := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case bool.refl =>
        exact congrArg SourceCorePublicValues.Value.bool (Core.Value.bool.inj payload)
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        rw [same] at payload
        cases payload

theorem succeeded_bool_value {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word (.bool value)) store completion)
    (requested : checkpoint.ResultTypeAt .bool) : completion.value = .bool value := by
  obtain ⟨_sourceType, encoded, accepted, payload⟩ := succeeded.reimports_payload requested rfl
  exact encoded_bool_value accepted payload

theorem represented_bool
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt .bool)
    (exported : completion.value = .bool value)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType .bool
      faults outcome native) : outcome = .value (.bool value) := by
  obtain ⟨payload, decoded, _⟩ := succeeded.reimports
  cases represented with
  | value related =>
    obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.bool_fields related
    have actualOutput := succeeded_bool_value succeeded requested
    have same := SourceCorePublicValues.Value.bool.inj (actualOutput.symm.trans exported)
    rw [same]
  | fault related =>
    simp only [LanguageResult.decode?, Option.some.injEq] at decoded
    cases decoded

/-- The fixture has exactly the two scalar public result profiles it executes. -/
inductive ScalarOutput where
  | word (value : Core.Word)
  | bool (value : Bool)

def ScalarOutput.sourceType : ScalarOutput → TypeSystem.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.nativeType : ScalarOutput → Core.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.source : ScalarOutput → Dynamic.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.native : ScalarOutput → Core.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.publicValue : ScalarOutput → SourceCorePublicValues.Value
  | .word value => .word value
  | .bool value => .bool value

theorem ScalarOutput.succeeded_value (scalar : ScalarOutput)
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word scalar.native) store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType) :
    completion.value = scalar.publicValue := by
  cases scalar with
  | word value => exact succeeded.word_value requested
  | bool value => exact succeeded_bool_value succeeded requested

theorem ScalarOutput.source_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType)
    (exported : completion.value = scalar.publicValue)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType scalar.nativeType
      faults outcome native) : outcome = .value scalar.source := by
  cases scalar with
  | word value => exact RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested exported represented
  | bool value => exact represented_bool succeeded requested exported represented

theorem ScalarOutput.native_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {payload : Core.Value}
    (represented : ValueRep checked registry functions mapping world rawType scalar.source payload scalar.nativeType) :
    payload = scalar.native := by
  cases scalar with
  | word value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.word_fields represented
    exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  | bool value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.bool_fields represented
    exact native.trans (congrArg Core.Value.bool (Dynamic.Value.bool.inj same).symm)

end Tests.SourceCoreEvidenceDirect
