import Solcore.Test.SourceCoreMixedBuiltinHandleCollected
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleMeaning

/-! The original returned builtin and current typed history supply an
independent Source call before resuming the accepted public handle request. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : ProfiledFixture} {row : Row fixture.original}
  {selected : SelectedInventory fixture row} {shape : Shape row.original.function.typedBody}
  {flag : Bool} {started : Started fixture.original row.original.key [.bool flag]}
  {callableProfile : fixture.original.recipe.compiled.compatible.checked.catalog.callableContracts = true}
  (first : InitialForward selected shape flag started callableProfile)
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} (retained : first.Retained session entries)
  (entry : Entry) (word : Core.Word)
  (call : CellAwarePublicHandleStart.StartedCall session entry.handle (.word word) runOptions.inputValidationFuel)

structure BuiltinHandlePlan where
  member : entry ∈ entries
  entryType : entry.sourceType = .function .word .integer
  sourceEq : entry.source = .builtin ⟨.wordToInteger⟩
  start : CellAwarePublicHandleStart.Started retained.state entry call .word .integer
  ready : CellAwarePublicHandleStart.Ready retained.state entry call start (.word word)
  input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context
    .word (.word word) (.word word)
  trace : Dynamic.CallableApplies (Program.ofChecked fixture.original.recipe.compiled.sourceProgram)
    selected.packet.header.function.context [] [] retained.state.heap
    entry.source [.word word] (.integer (Int.ofNat word.val)) retained.state.heap

/-- Genuine primitive semantics, with no native execution premise. -/
theorem builtin_plan (member : entry ∈ entries) (entryType : entry.sourceType = .function .word .integer)
    (sourceEq : entry.source = .builtin ⟨.wordToInteger⟩) :
    Nonempty (BuiltinHandlePlan first retained entry word call) := by
  obtain ⟨start⟩ := CellAwarePublicHandleStart.from_call retained.state entry call member entryType
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input entries selected.packet.header.function.context
      .word (.word word) (.word word) :=
    .data ⟨.word word,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word word⟩
      ⟨.word word,by simp [SourceCoreIndexedSession.DataInput.publicValue],.word word⟩
  obtain ⟨ready⟩ := CellAwarePublicHandleStart.of_started retained.state entry call
    (CellAwarePublicCells.generalized_extends_registry _ _) member entryType input start
  exact ⟨⟨member,entryType,sourceEq,start,ready,input,sourceEq.symm ▸ .builtin (.wordToInteger word)⟩⟩

end Tests.SourceCoreMixedBuiltinValue
