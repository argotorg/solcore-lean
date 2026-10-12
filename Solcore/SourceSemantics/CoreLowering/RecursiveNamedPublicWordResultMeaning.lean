import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.Frontend.SourceCoreIndexedSession

/-! An actual public Word completion fixes the value of the independent Source
outcome. The existing full result relation forces a common native/Source Word;
the genuine public decoder identifies that Word with the observed output. No
new execution, source typing or payload representation premise is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
open Core Frontend SourceInference GeneralHeap CompatiblePayload

/-- Scalar payload inversion and the actual successful export identify the
Source result. The public success receipt also rules out semantic faults. -/
theorem represented_word
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : SourceCoreIndexedSession.Artifact} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Value} {store : Store} {completion : SourceCoreIndexedSession.Completion artifact}
    {word : Word}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt .word)
    (exported : completion.value = .word word)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType .word
      faults outcome native) : outcome = .value (.word word) := by
  obtain ⟨payload, decoded, _⟩ := succeeded.reimports
  cases represented with
  | value related =>
    obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.word_fields related
    have actualOutput := succeeded.word_value requested
    have same := SourceCorePublicValues.Value.word.inj (actualOutput.symm.trans exported)
    rw [same]
  | fault related =>
    simp only [LanguageResult.decode?, Option.some.injEq] at decoded
    cases decoded

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
  {caller : CallableIndexedOwnedFunctionState.State headers keys ⟨scope, mapping, world, before, store, canonical⟩}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world}
  {payloads : List Value} {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome}
  {after : Dynamic.Heap} {native : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Consume the complete named invocation result returned by public history
execution. Heap, caller and metadata postconditions remain in that same result. -/
theorem result_word
    {artifact : SourceCoreIndexedSession.Artifact} {checkpoint : SourceCoreIndexedSession.Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {completion : SourceCoreIndexedSession.Completion artifact} {word : Word}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion)
    (requested : checkpoint.ResultTypeAt .word)
    (exported : completion.value = .word word)
    (outputWord : header.output = .word)
    (result : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := payloads) functions owner caller header capture context outcome
      after native finalStore finalMap finalWorld faults) : outcome = .value (.word word) := by
  have represented := result.2.1
  rw [outputWord] at represented
  exact represented_word succeeded requested exported represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
