import Solcore.Test.SourceCoreMixedProjectedSourceLoop

/-! Construct the original ordinary Source body independently: capture the
polymorphic identity, allocate the absent mapping, commit the right-hand call,
execute the for headers, and return the updated mapping and Bool instance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMixedProjected
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

def absentHeap (before : Dynamic.Heap) (binder : TypedBinder) : Dynamic.Heap :=
  ⟨before.cells ++ [⟨binder.scheme.body,none,none⟩]⟩

private theorem absent_step {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} (site : StatementAt source (.letDecl binder none))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((binder.id,⟨before.cells.length⟩) :: environment)) (absentHeap before binder) ∧
    SourceState program source final evidence ((binder.id,⟨before.cells.length⟩) :: environment) (absentHeap before binder) ∧
    BinderExtends source.owner context binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letUninitialized mono extended =>
    have allocation : Dynamic.Heap.Allocates before binder.scheme.body none
        ⟨before.cells.length⟩ (absentHeap before binder) := .append
    have trace := Dynamic.StatementExecutes.letUninitialized (program := program) (environment := environment)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq mono extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,extended⟩

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.tableRead.node.id left ∧
      ExpressionHasType source context shape.boolCall.node.id right := by
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
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.tableLet.node.id,shape.activeLet.node.id,
       shape.tableWrite.node.id,shape.loop.node.id,shape.returned.node.id] finalContext
      (.returned (.product (mappingValue (loopValue flag)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,tail1⟩ := head_tail typed
  obtain ⟨tableContext,_,_,tableTyped,tail2⟩ := head_tail tail1
  obtain ⟨activeContext,_,_,activeTyped,tail3⟩ := head_tail tail2
  obtain ⟨writeContext,_,_,writeTyped,tail4⟩ := head_tail tail3
  obtain ⟨loopContext,_,_,loopTyped,tail5⟩ := head_tail tail4
  obtain ⟨_,_,_,returnTyped,_⟩ := head_tail tail5
  obtain ⟨fTrace,fState,fStored,_fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let base := identityHeap shape.f context environment before
  let outer : Dynamic.Environment := (shape.f.binder.id,⟨before.cells.length⟩) :: environment
  have baseAppend : HeapAppends before base := ⟨_,rfl⟩
  have flagAtF := (flagStored.mono baseAppend).under ⟨before.cells.length⟩ shape.fFlag
  obtain ⟨tableTrace,tableState,tableExtended⟩ := absent_step shape.tableLet fState wellFormed tableTyped
  let tableHeap := absentHeap base shape.table
  have flagAtTable := (flagAtF.mono (show HeapAppends base tableHeap from ⟨_,rfl⟩)).under
    ⟨base.cells.length⟩ shape.tableFlag
  obtain ⟨activeTrace,activeState,_,activeExtended⟩ := ordinary_step shape.activeLet tableState wellFormed
    (by rw [shape.activeScheme]; rfl) activeTyped (read_value shape.inputRead flagAtTable)
  have sameHeap : valueHeap tableHeap shape.active (.bool flag) = phaseHeap base none flag [] := by
    simp only [tableHeap,absentHeap,valueHeap,phaseHeap,shape.tableScheme,shape.activeScheme,
      TypeSystem.Scheme.mono,List.append_nil,Option.map_none,List.append_assoc,List.cons_append,List.nil_append]
  have sameEnvironment :
      (shape.active.id,⟨tableHeap.cells.length⟩) :: (shape.table.id,⟨base.cells.length⟩) :: outer =
      phaseEnvironment shape base outer := by
    simp only [tableHeap,absentHeap,phaseEnvironment,List.length_append,List.length_cons,List.length_nil]
  rw [sameHeap,sameEnvironment] at activeState activeTrace
  have fAtActive : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
      (phaseHeap base none flag []) := by
    rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
    exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
      (phaseHeap.prefix base none flag []).read read,descriptor,
      (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
  have writeForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.tableWrite.found writeTyped
  rw [shape.tableWrite.formEq] at writeForm
  cases writeForm with
  | assignValue assigned =>
    cases assigned with
    | equal place wordTyped _ =>
      obtain ⟨_,keyTyped⟩ := projected_key_typed place
      obtain ⟨_,_,_,tenTyped⟩ := call_typed shape.wordCall state.runtime.graph.nodeOccurrencesUnique wordTyped
      have tenTrace := shape.ten.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique tenTyped
      rw [shape.tenValue] at tenTrace
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtActive.invoke activeState wellFormed shape.wordCall
        (.inl rfl) wordTyped tenTrace
      obtain ⟨suffix,appendEq⟩ := wordAppend
      have wordHeapEq : wordHeap = phaseHeap base none flag suffix := by
        cases wordHeap
        simp only [phaseHeap,List.append_nil] at appendEq ⊢
        exact congrArg Dynamic.Heap.mk appendEq
      rw [wordHeapEq] at wordTrace
      have keyTrace := shape.key.evaluates (program := program) evidence (phaseEnvironment shape base outer)
        (phaseHeap base none flag []) state.runtime.graph.nodeOccurrencesUnique keyTyped
      rw [shape.keyValue] at keyTrace
      have writeTrace := Dynamic.StatementExecutes.assignValue (program := program) (context := activeContext)
        (evidence := evidence) (environment := phaseEnvironment shape base outer)
        (lookupStatement?_sound shape.tableWrite.found) shape.tableWrite.formEq
        (projected_first (.tail shape.activeTable .head) keyTrace wordTrace)
      have writtenState := activeState.after_statement wellFormed writeTyped writeTrace
      have loopTrace := shape.loop_trace (program := program) evidence base outer
        state.runtime.graph.nodeOccurrencesUnique loopTyped flag suffix
      have loopForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.loop.found loopTyped
      rw [shape.loop.formEq] at loopForm
      cases loopForm with
      | forLoop _ _ _ _ =>
        have afterState := writtenState.after_statement wellFormed loopTyped loopTrace
        have fAtLoop : StoredIdentity shape.f activeContext (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) := by
          rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
          exact ⟨definitionContext,captured,location,cell,.tail shape.activeF (.tail shape.tableF lookup),
            (phaseHeap.prefix base (some (loopValue flag)) false suffix).read read,descriptor,
            (fields.trans (.ofBinderExtends tableExtended)).trans (.ofBinderExtends activeExtended)⟩
        have flagAtLoop : StoredValue shape.flag (phaseEnvironment shape base outer)
            (phaseHeap base (some (loopValue flag)) false suffix) (.bool flag) :=
          ((flagAtF.mono (phaseHeap.prefix base (some (loopValue flag)) false suffix)).under
            ⟨base.cells.length⟩ shape.tableFlag).under ⟨base.cells.length+1⟩ shape.activeFlag
        have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
        rw [shape.returned.formEq] at returnForm
        cases returnForm with
        | returnValue tupleTyped =>
          obtain ⟨_,_,_tableTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
          obtain ⟨after,boolTrace,boolAppend⟩ := fAtLoop.invoke afterState wellFormed shape.boolCall
            (.inr rfl) boolTyped (read_value shape.flagRead flagAtLoop)
          have tupleTrace : Dynamic.ExpressionEvaluates program activeContext evidence source
              (phaseEnvironment shape base outer) (phaseHeap base (some (loopValue flag)) false suffix) shape.tuple.id
              (.product (mappingValue (loopValue flag)) (.bool flag)) after := by
            apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
            · rw [shape.tupleForm]
              exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
                (.cons (read_value shape.tableRead (shape.table_stored base outer (loopValue flag) false suffix))
                  (.cons boolTrace .nil)) (.cons (.singleton _))
            · rw [shape.tupleCoercions]; exact .nil
          have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
            shape.returned.formEq tupleTrace
          refine ⟨activeContext,after,.cons fTrace (.cons tableTrace (.cons activeTrace (.cons writeTrace (.cons loopTrace ?_)))),
            baseAppend.trans ((phaseHeap.prefix base (some (loopValue flag)) false suffix).trans boolAppend)⟩
          apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
          · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
          · exact returned
    | wordCompound impossible _ _ _ => cases impossible

end Tests.SourceCoreMixedProjected
