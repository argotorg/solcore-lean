import Solcore.Test.SourceCoreMixedImperativeSourceBranch

/-! The complete original body is evaluated independently of native execution.
Both lexical exits restore the outer binding; the final two calls use the same
principal descriptor after the chosen branch has finished. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.finalWordCall.node.id left ∧
      ExpressionHasType source context shape.finalBoolCall.node.id right := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans shape.tupleFound)
    rw [shape.tupleForm] at raw
    cases raw with
    | tuple elements =>
      cases elements with
      | cons first rest =>
        cases rest with
        | cons second _ => exact ⟨_,_,first,second⟩

theorem Shape.body_from_source {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : BodyFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementsHaveType source control context
      [shape.fLet.node.id,shape.block.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.block.node.id,shape.returned.node.id] finalContext
      (.returned (.product (.word (Word.ofNatModulo 17)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,rest⟩ := head_tail typed
  obtain ⟨blockContext,_,_,blockTyped,last⟩ := head_tail rest
  obtain ⟨returnContext,_,_,returnTyped,_⟩ := head_tail last
  obtain ⟨fTrace,fState,fStored,fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let firstHeap := identityHeap shape.f context environment before
  have firstAppend : HeapAppends before firstHeap := ⟨_,rfl⟩
  have flagAtF := (flagStored.mono firstAppend).under ⟨before.cells.length⟩ shape.fFlag
  obtain ⟨blockHeap,blockTrace,blockAppend⟩ := shape.block_trace fState wellFormed blockTyped fStored flag flagAtF
  have blockForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.block.found blockTyped
  rw [shape.block.formEq] at blockForm
  cases blockForm with
  | block _ =>
    have blockState := fState.after_statement wellFormed blockTyped blockTrace
    have fAtBlock := fStored.mono blockAppend
    have flagAtBlock := flagAtF.mono blockAppend
    have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
    rw [shape.returned.formEq] at returnForm
    cases returnForm with
    | returnValue tupleTyped =>
      obtain ⟨_,_,wordTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
      obtain ⟨_,_,_,literalTyped⟩ := call_typed shape.finalWordCall state.runtime.graph.nodeOccurrencesUnique wordTyped
      have literal := shape.seventeen.evaluates (program := program) evidence ((shape.f.binder.id,⟨before.cells.length⟩) :: environment) blockHeap
        state.runtime.graph.nodeOccurrencesUnique literalTyped
      rw [shape.seventeenValue] at literal
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtBlock.invoke blockState wellFormed shape.finalWordCall
        (.inl rfl) wordTyped literal
      have wordState := blockState.after_expression wellFormed wordTyped wordTrace
      have fAtWord := fAtBlock.mono wordAppend
      have flagAtWord := flagAtBlock.mono wordAppend
      obtain ⟨after,boolTrace,boolAppend⟩ := fAtWord.invoke wordState wellFormed shape.finalBoolCall
        (.inr rfl) boolTyped (read_value shape.flagRead flagAtWord)
      have tupleTrace : Dynamic.ExpressionEvaluates program fContext evidence source
          ((shape.f.binder.id,⟨before.cells.length⟩) :: environment) blockHeap shape.tuple.id
          (.product (.word (Word.ofNatModulo 17)) (.bool flag)) after := by
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
        · rw [shape.tupleForm]
          exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
            (.cons wordTrace (.cons boolTrace .nil)) (.cons (.singleton _))
        · rw [shape.tupleCoercions]; exact .nil
      have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
        shape.returned.formEq tupleTrace
      refine ⟨fContext,after,.cons fTrace (.cons blockTrace ?_),firstAppend.trans (blockAppend.trans (wordAppend.trans boolAppend))⟩
      apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
      · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
      · exact returned

end Tests.SourceCoreMixedImperative
