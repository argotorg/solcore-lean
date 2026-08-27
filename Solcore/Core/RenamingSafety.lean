import Solcore.Core.RenamingRuntime
import Solcore.Core.Safety

set_option autoImplicit false

namespace Solcore.Core

theorem ValuesRelated.eq_of_cellPayload
    {type : Ty} {source target : Value} {definitions : DataEnvironment}
    (payload : CellPayload type)
    (typing : ValueHasType source type definitions)
    (related : ValuesRelated source target) :
    source = target := by
  induction payload generalizing source target with
  | unit =>
      cases typing
      exact (ValuesRelated.unit_iff.mp related).symm
  | bool =>
      cases typing
      exact (ValuesRelated.bool_iff.mp related).symm
  | word =>
      cases typing
      exact (ValuesRelated.word_iff.mp related).symm
  | product leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          cases related with
          | pair leftRelated rightRelated =>
              rw [leftIH leftTyping leftRelated, rightIH rightTyping rightRelated]
  | sum leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | inLeft payloadTyping =>
          cases related with
          | inLeft payloadRelated =>
              rw [leftIH payloadTyping payloadRelated]
      | inRight payloadTyping =>
          cases related with
          | inRight payloadRelated =>
              rw [rightIH payloadTyping payloadRelated]

namespace StoreHasTypes

private theorem tail
    {elementType : Ty} {world : StoreTyping}
    {head : Value} {store : Store}
    (typing : StoreHasTypes (elementType :: world) (head :: store)) :
    StoreHasTypes world store where
  length_eq := by
    simpa using typing.length_eq
  lookup := by
    intro location storedType found
    obtain ⟨value, read, payload, valueTyping⟩ :=
      typing.lookup (location := location + 1) (by simpa using found)
    exact ⟨value, by simpa [Store.read?] using read, payload, valueTyping⟩

end StoreHasTypes

theorem StoresRelated.eq_of_hasTypes
    {world : StoreTyping} {source target : Store}
    (typing : StoreHasTypes world source)
    (related : StoresRelated source target) :
    source = target := by
  induction related generalizing world with
  | nil => rfl
  | cons headRelated tailRelated inductionHypothesis =>
      cases world with
      | nil =>
          have lengthEquality := typing.length_eq
          simp at lengthEquality
      | cons elementType world =>
          obtain ⟨headValue, headRead, payload, headTyping⟩ :=
            typing.lookup (location := 0) (elementType := elementType) (by simp)
          simp [Store.read?] at headRead
          subst headValue
          have headEquality :=
            headRelated.eq_of_cellPayload payload headTyping
          have tailEquality := inductionHypothesis typing.tail
          simp [headEquality, tailEquality]

theorem EnvironmentsRelated.headInsertion
    (inserted : Value) (environment : Environment) :
    EnvironmentsRelated (Renaming.insertion 0)
      environment (inserted :: environment) := by
  constructor
  · intro index sourceBound
    change ValuesRelated environment[index] environment[index]
    exact ValuesRelated.refl _
  · intro index sourceBound
    simpa [Renaming.insertion] using sourceBound

end Solcore.Core
