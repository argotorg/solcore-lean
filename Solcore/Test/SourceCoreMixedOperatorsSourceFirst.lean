import Solcore.Test.SourceCoreMixedOperatorsSource

/-! Construct the original declaration and operators before target execution.
The first identity call always runs; the second runs only after true. The
following builtin leaf retains the exact heap reached by those calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedOperators
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem Shape.calls_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {result : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context shape.tuple.id result) :
    ∃ leftType rightType, ExpressionHasType source context shape.firstCall.node.id leftType ∧
      ExpressionHasType source context shape.secondCall.node.id rightType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple children =>
      cases children with
      | cons first _ =>
        cases first with
        | intro binaryContains binaryRaw _ _ _ _ =>
          cases Option.some.inj ((lookupExpression?_complete unique binaryContains).symm.trans shape.binaryFound)
          rw [shape.binaryForm] at binaryRaw
          cases binaryRaw with
          | binary left right _ =>
            cases right with
            | intro negatedContains negatedRaw _ _ _ _ =>
              cases Option.some.inj ((lookupExpression?_complete unique negatedContains).symm.trans shape.negatedFound)
              rw [shape.negatedForm] at negatedRaw
              cases negatedRaw with
              | unary operand _ => exact ⟨_,_,left,operand⟩

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
    obtain ⟨leftType,rightType,leftTyped,rightTyped⟩ := shape.calls_typed state.runtime.graph.nodeOccurrencesUnique tupleTyped
    have allocatedPrefix : HeapAppends before (identityHeap shape.f context environment before) := ⟨_,rfl⟩
    have flagNext := (flagStored.mono allocatedPrefix).under ⟨before.cells.length⟩ shape.fFlag
    obtain ⟨leftHeap,leftTrace,leftAppend⟩ := stored.invoke stateNext wellFormed shape.firstCall (.inr rfl)
      leftTyped (read_value shape.flagRead flagNext)
    have leftState := stateNext.after_expression wellFormed leftTyped leftTrace
    have chosen : ∃ after, Dynamic.ExpressionEvaluates program middle evidence source
        ((shape.f.binder.id,⟨before.cells.length⟩) :: environment)
        (identityHeap shape.f context environment before) shape.binary.id (.bool flag) after ∧
        HeapAppends (identityHeap shape.f context environment before) after := by
      cases flag with
      | false =>
        refine ⟨leftHeap,?_,leftAppend⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.binaryFound)
        · rw [shape.binaryForm,shape.binaryRequirements,shape.binaryCoercions]
          exact .binaryShortCircuit (owned := []) rfl leftTrace .andFalse rfl
        · rw [shape.binaryCoercions]; exact .nil
      | true =>
        obtain ⟨after,rightTrace,rightAppend⟩ := (stored.mono leftAppend).invoke leftState wellFormed
          shape.secondCall (.inr rfl) rightTyped (boolean_value shape.falseNode)
        have negatedTrace : Dynamic.ExpressionEvaluates program middle evidence source
            ((shape.f.binder.id,⟨before.cells.length⟩) :: environment)
            leftHeap shape.negated.id (.bool true) after := by
          apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.negatedFound)
          · rw [shape.negatedForm,shape.negatedRequirements,shape.negatedCoercions]
            exact .unary (owned := []) rfl rightTrace (.primitive (.logicalNot false))
          · rw [shape.negatedCoercions]; exact .nil
        refine ⟨after,?_,leftAppend.trans rightAppend⟩
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.binaryFound)
        · rw [shape.binaryForm,shape.binaryRequirements,shape.binaryCoercions]
          exact .binaryEvaluateRight (owned := []) rfl leftTrace .andTrue negatedTrace (.primitive (.logicalAnd true true))
        · rw [shape.binaryCoercions]; exact .nil
    obtain ⟨after, binaryTrace, append⟩ := chosen
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
        exact .tuple rfl (.cons binaryTrace (.cons builtinTrace .nil)) (.cons (.singleton _))
      · rw [shape.tupleCoercions]; exact .nil
    refine ⟨middle,after,.cons declaration ?_,allocatedPrefix.trans append⟩
    apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
    · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
    · exact .returnValue (lookupStatement?_sound shape.returned.found) shape.returned.formEq tupleTrace

end Tests.SourceCoreMixedOperators
