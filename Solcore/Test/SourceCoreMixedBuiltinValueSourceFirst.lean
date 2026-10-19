import Solcore.Test.SourceCoreMixedBuiltinValueSource

/-! Construct the original declaration, generalized call, and builtin return
before any target execution. The builtin leaf preserves the actual call heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedBuiltinValue
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem Shape.call_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {result : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id result) :
    ∃ type, ExpressionHasType source context shape.call.node.id type := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children => cases children with | cons first _ => exact ⟨_,first⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource}
    (shape : Shape source) {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap} {control : ControlContext} {facts : BodyFacts}
    (state : SourceState program source context evidence environment before)
    (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.initialized.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ next after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.initialized.node.id,shape.returned.node.id] next
      (.returned (.product (.bool flag) (.builtin ⟨.wordToInteger⟩))) after ∧ HeapAppends before after := by
  obtain ⟨middle, _, _, firstTyped, tailTyped⟩ := head_tail typed
  obtain ⟨declaration, stateNext, stored, _extended⟩ := generalized_step shape.f shape.initialized state wellFormed firstTyped
  obtain ⟨next, _, _, returnedTyped, _⟩ := head_tail tailTyped
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnedTyped
  rw [shape.returned.formEq] at original
  cases original with
  | returnValue tupleTyped =>
    obtain ⟨type,callTyped⟩ := shape.call_typed state.runtime.graph.nodeOccurrencesUnique tupleTyped
    have allocatedPrefix : HeapAppends before (identityHeap shape.f context environment before) := ⟨_,rfl⟩
    have flagNext := (flagStored.mono allocatedPrefix).under ⟨before.cells.length⟩ shape.fFlag
    obtain ⟨after, callTrace, append⟩ := stored.invoke stateNext wellFormed shape.call (.inr rfl)
      callTyped (read_value shape.flagRead flagNext)
    have builtinTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,⟨before.cells.length⟩) :: environment) after shape.builtin.id
        (.builtin ⟨.wordToInteger⟩) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.builtinFound)
      · rw [shape.builtinForm,shape.builtinRequirements,shape.builtinCoercions]
        exact .builtinFunction rfl
      · rw [shape.builtinCoercions]; exact .nil
    have tupleTrace : Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,⟨before.cells.length⟩) :: environment)
        (identityHeap shape.f context environment before) shape.tuple.id
        (.product (.bool flag) (.builtin ⟨.wordToInteger⟩)) after := by
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
      · rw [shape.tupleForm,shape.tupleRequirements,shape.tupleCoercions]
        exact .tuple rfl (.cons callTrace (.cons builtinTrace .nil)) (.cons (.singleton _))
      · rw [shape.tupleCoercions]; exact .nil
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans append⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreMixedBuiltinValue
