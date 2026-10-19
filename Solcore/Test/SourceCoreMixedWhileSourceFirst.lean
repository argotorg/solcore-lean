import Solcore.Test.SourceCoreMixedWhileSourceLoop

/-! The complete ordinary Source body constructs its descriptor, runs the real
zero/two-iteration loop, then invokes the same descriptor at Word and Bool. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMixedWhile
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreMixedImperative

private theorem initializer_typed {source : TypedSource} {binder : TypedBinder} {initializer : ExpressionId}
    (site : StatementAt source (.letDecl binder (some initializer)))
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source) (mono : binder.scheme.quantified = [])
    (typed : StatementHasType source control context site.node.id final facts) :
    ExpressionHasType source context initializer binder.scheme.body := by
  have form := form_at unique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized value _ _ => exact value
  | letInitializedGeneralized impossible _ _ _ _ => exact (impossible mono).elim

private theorem tuple_typed {source : TypedSource} (shape : Shape source)
    {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context shape.tuple.id type) :
    ∃ left right, ExpressionHasType source context shape.wordCall.node.id left ∧
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
      [shape.fLet.node.id,shape.activeLet.node.id,shape.firstLet.node.id,shape.counterLet.node.id,
       shape.loop.node.id,shape.returned.node.id] final facts)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ finalContext after, Dynamic.FunctionStatementsExecute program context evidence source environment before
      [shape.fLet.node.id,shape.activeLet.node.id,shape.firstLet.node.id,shape.counterLet.node.id,
       shape.loop.node.id,shape.returned.node.id] finalContext
      (.returned (.product (.word (loopCounter flag)) (.bool flag))) after ∧ HeapAppends before after := by
  obtain ⟨fContext,_,_,fTyped,tail1⟩ := head_tail typed
  obtain ⟨activeContext,_,_,activeTyped,tail2⟩ := head_tail tail1
  obtain ⟨firstContext,_,_,firstTyped,tail3⟩ := head_tail tail2
  obtain ⟨counterContext,_,_,counterTyped,tail4⟩ := head_tail tail3
  obtain ⟨loopContext,_,_,loopTyped,tail5⟩ := head_tail tail4
  obtain ⟨_,_,_,returnTyped,_⟩ := head_tail tail5
  obtain ⟨fTrace,fState,fStored,fExtended⟩ := generalized_step shape.f shape.fLet state wellFormed fTyped
  let base := identityHeap shape.f context environment before
  let outer : Dynamic.Environment := (shape.f.binder.id,⟨before.cells.length⟩) :: environment
  have baseAppend : HeapAppends before base := ⟨_,rfl⟩
  have flagAtF := (flagStored.mono baseAppend).under ⟨before.cells.length⟩ shape.fFlag
  obtain ⟨activeTrace,activeState,_,activeExtended⟩ := ordinary_step shape.activeLet fState wellFormed
    (by rw [shape.activeScheme]; rfl) activeTyped (read_value shape.inputRead flagAtF)
  let activeHeap := valueHeap base shape.active (.bool flag)
  obtain ⟨firstTrace,firstState,_,firstExtended⟩ := ordinary_step shape.firstLet activeState wellFormed
    (by rw [shape.firstScheme]; rfl) firstTyped (boolean_value shape.trueNode)
  let firstHeap := valueHeap activeHeap shape.first (.bool true)
  have zeroTyped := initializer_typed shape.counterLet state.runtime.graph.nodeOccurrencesUnique
    (by rw [shape.counterScheme]; rfl) counterTyped
  have zeroTrace := shape.zero.evaluates (program := program) evidence
    ((shape.first.id,⟨activeHeap.cells.length⟩) :: (shape.active.id,⟨base.cells.length⟩) :: outer)
    firstHeap state.runtime.graph.nodeOccurrencesUnique zeroTyped
  rw [shape.zeroValue] at zeroTrace
  obtain ⟨counterTrace,counterState,_,counterExtended⟩ := ordinary_step shape.counterLet firstState wellFormed
    (by rw [shape.counterScheme]; rfl) counterTyped zeroTrace
  have sameHeap : valueHeap firstHeap shape.counter (.word (Word.ofNatModulo 0)) =
      phaseHeap base flag true (Word.ofNatModulo 0) := by
    simp only [firstHeap,activeHeap,valueHeap,phaseHeap,shape.activeScheme,shape.firstScheme,shape.counterScheme,
      TypeSystem.Scheme.mono,List.append_assoc,List.cons_append,List.nil_append]
  have sameEnvironment :
      (shape.counter.id,⟨firstHeap.cells.length⟩) ::
        (shape.first.id,⟨activeHeap.cells.length⟩) :: (shape.active.id,⟨base.cells.length⟩) :: outer =
      phaseEnvironment shape base outer := by
    simp only [firstHeap,activeHeap,valueHeap,phaseEnvironment,List.length_append,List.length_cons,List.length_nil]
  rw [sameHeap,sameEnvironment] at counterState counterTrace
  have loopTrace := shape.loop_trace (program := program) evidence base outer state.runtime.graph.nodeOccurrencesUnique loopTyped flag
  have loopForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.loop.found loopTyped
  rw [shape.loop.formEq] at loopForm
  cases loopForm with
  | whileLoop _ _ =>
    have afterState := counterState.after_statement wellFormed loopTyped loopTrace
    have fAtLoop : StoredIdentity shape.f counterContext (phaseEnvironment shape base outer)
        (phaseHeap base false (!flag) (loopCounter flag)) := by
      rcases fStored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
      exact ⟨definitionContext,captured,location,cell,
        .tail shape.counterF (.tail shape.firstF (.tail shape.activeF lookup)),
        (phaseHeap.prefix base false (!flag) (loopCounter flag)).read read,descriptor,
        ((fields.trans (.ofBinderExtends activeExtended)).trans (.ofBinderExtends firstExtended)).trans
          (.ofBinderExtends counterExtended)⟩
    have flagAtLoop : StoredValue shape.flag (phaseEnvironment shape base outer)
        (phaseHeap base false (!flag) (loopCounter flag)) (.bool flag) :=
      (((flagAtF.mono (phaseHeap.prefix base false (!flag) (loopCounter flag))).under
        ⟨base.cells.length⟩ shape.activeFlag).under ⟨base.cells.length+1⟩ shape.firstFlag).under
        ⟨base.cells.length+2⟩ shape.counterFlag
    have returnForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.returned.found returnTyped
    rw [shape.returned.formEq] at returnForm
    cases returnForm with
    | returnValue tupleTyped =>
      obtain ⟨_,_,wordTyped,boolTyped⟩ := tuple_typed shape state.runtime.graph.nodeOccurrencesUnique tupleTyped
      obtain ⟨wordHeap,wordTrace,wordAppend⟩ := fAtLoop.invoke afterState wellFormed shape.wordCall
        (.inl rfl) wordTyped (read_value shape.counterRead (shape.counter_stored base outer false (!flag) (loopCounter flag)))
      have wordState := afterState.after_expression wellFormed wordTyped wordTrace
      obtain ⟨after,boolTrace,boolAppend⟩ := (fAtLoop.mono wordAppend).invoke wordState wellFormed shape.boolCall
        (.inr rfl) boolTyped (read_value shape.flagRead (flagAtLoop.mono wordAppend))
      have tupleTrace : Dynamic.ExpressionEvaluates program counterContext evidence source
          (phaseEnvironment shape base outer) (phaseHeap base false (!flag) (loopCounter flag)) shape.tuple.id
          (.product (.word (loopCounter flag)) (.bool flag)) after := by
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound shape.tupleFound)
        · rw [shape.tupleForm]
          exact .tuple (by rw [shape.tupleRequirements,shape.tupleCoercions]; rfl)
            (.cons wordTrace (.cons boolTrace .nil)) (.cons (.singleton _))
        · rw [shape.tupleCoercions]; exact .nil
      have returned := Dynamic.StatementExecutes.returnValue (lookupStatement?_sound shape.returned.found)
        shape.returned.formEq tupleTrace
      refine ⟨counterContext,after,.cons fTrace (.cons activeTrace (.cons firstTrace (.cons counterTrace (.cons loopTrace ?_)))) ,
        baseAppend.trans ((phaseHeap.prefix base false (!flag) (loopCounter flag)).trans (wordAppend.trans boolAppend))⟩
      apply Dynamic.FunctionStatementsExecute.singleton (lookupStatement?_sound shape.returned.found)
      · intro expression impossible; rw [shape.returned.formEq] at impossible; cases impossible
      · exact returned

end Tests.SourceCoreMixedWhile
