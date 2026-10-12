import Solcore.Test.SourceCoreRecursiveIndexCommon
import Solcore.Test.SourceCoreRecursiveIndexSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def sourceTable (first second : Entry) : Dynamic.Value :=
  .mapping .word closureType [(.word firstKey, first.source), (.word secondKey, second.source)]

theorem word_input {entries : List Entry} {context : SourceSemantics.Context} (word : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context .word (.word word) (.word word) :=
  .data ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩

theorem table_input {entries : List Entry} {context : SourceSemantics.Context}
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context containerType
      (table firstHandle secondHandle) (sourceTable first second) := by
  have firstInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) first firstMember
  have secondInput := RecursiveNamedPublicFunctionHistoryInputs.Input.retained (context := context) second secondMember
  rw [firstType, firstHandleEq] at firstInput
  rw [secondType, secondHandleEq] at secondInput
  exact .mapping (.entry (word_input firstKey) firstInput
    (.entry (word_input secondKey) secondInput (.empty _ _)))

theorem select_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [containerType, .word]
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] :=
  .cons (table_input first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq)
    (.cons (word_input key) .nil)

end Tests.SourceCoreRecursiveIndex
