import Solcore.Test.SourceCoreMixedImperativeSourceSteps

/-! Both branches execute from independent Source states. The true branch
allocates its own generalized identity and ordinary result; the false branch
calls the outer identity. Each restores the incoming lexical environment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics

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

/-- Actual Source execution is available for either original branch. -/
theorem Shape.branch_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementHasType source control context shape.branch.node.id final facts)
    (fStored : StoredIdentity shape.f context environment before)
    (firstStored : StoredValue shape.first environment before (.word (Word.ofNatModulo 11)))
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ after, Dynamic.StatementExecutes program context evidence source environment before shape.branch.node.id
      final (.fallthrough environment) after ∧ HeapAppends before after := by
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.branch.found typed
  rw [shape.branch.formEq] at original
  cases original with
  | ifWithElse conditionTyped thenTyped elseTyped =>
    have conditionTrace := read_value (program := program) (context := context) (evidence := evidence) shape.condition flagStored
    cases flag with
    | false =>
      obtain ⟨elseContext,_,_,discardTyped,_⟩ := head_tail elseTyped
      have discardForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.elseDiscard.found discardTyped
      rw [shape.elseDiscard.formEq] at discardForm
      cases discardForm with
      | expressionDiscard callTyped =>
        obtain ⟨after,callTrace,appended⟩ := fStored.invoke state wellFormed shape.elseCall (.inr rfl)
          callTyped (boolean_value shape.falseNode)
        have discarded := Dynamic.StatementExecutes.expression (lookupStatement?_sound shape.elseDiscard.found)
          shape.elseDiscard.formEq callTrace
        exact ⟨after,.ifFalseWithElse (lookupStatement?_sound shape.branch.found) shape.branch.formEq
          conditionTrace (.cons discarded .nil),appended⟩
    | true =>
      obtain ⟨gContext,_,_,gTyped,tailTyped⟩ := head_tail thenTyped
      obtain ⟨chosenContext,_,_,chosenTyped,discardTypedList⟩ := head_tail tailTyped
      obtain ⟨discardContext,_,_,discardTyped,_⟩ := head_tail discardTypedList
      obtain ⟨gTrace,gState,gStored,gExtended⟩ := generalized_step shape.g shape.gLet state wellFormed gTyped
      let gHeap := identityHeap shape.g context environment before
      have gAppended : HeapAppends before gHeap := ⟨_,rfl⟩
      have fAtG := (fStored.mono gAppended).under shape.g.binder ⟨before.cells.length⟩ shape.gF gExtended
      have firstAtG := (firstStored.mono gAppended).under ⟨before.cells.length⟩ shape.gFirst
      have chosenInitializer := initializer_typed shape.chosenLet state.runtime.graph.nodeOccurrencesUnique
        (by rw [shape.chosenScheme]; rfl) chosenTyped
      obtain ⟨middle,chosenCallTrace,chosenCallAppend⟩ := gStored.invoke gState wellFormed shape.chosenCall (.inl rfl)
        chosenInitializer (read_value shape.firstRead firstAtG)
      obtain ⟨chosenTrace,chosenState,chosenStored,chosenExtended⟩ := ordinary_step shape.chosenLet gState wellFormed
        (by rw [shape.chosenScheme]; rfl) chosenTyped chosenCallTrace
      let chosenHeap := valueHeap middle shape.chosen (.word (Word.ofNatModulo 11))
      have chosenAppend : HeapAppends middle chosenHeap := ⟨_,rfl⟩
      have fAtChosen := ((fAtG.mono chosenCallAppend).mono chosenAppend).under shape.chosen
        ⟨middle.cells.length⟩ shape.chosenF chosenExtended
      have discardForm := form_at state.runtime.graph.nodeOccurrencesUnique shape.thenDiscard.found discardTyped
      rw [shape.thenDiscard.formEq] at discardForm
      cases discardForm with
      | expressionDiscard callTyped =>
        obtain ⟨after,callTrace,lastAppend⟩ := fAtChosen.invoke chosenState wellFormed shape.thenCall (.inl rfl)
          callTyped (read_value shape.chosenRead chosenStored)
        have discarded := Dynamic.StatementExecutes.expression (lookupStatement?_sound shape.thenDiscard.found)
          shape.thenDiscard.formEq callTrace
        have inner := Dynamic.StatementsExecute.cons gTrace (.cons chosenTrace (.cons discarded .nil))
        exact ⟨after,.ifTrue (lookupStatement?_sound shape.branch.found) shape.branch.formEq conditionTrace inner,
          gAppended.trans (chosenCallAppend.trans (chosenAppend.trans lastAppend))⟩

/-- The ordinary first declaration is evaluated before the original condition. -/
theorem Shape.block_trace {program : SourceSemantics.Program} {source : TypedSource} (shape : Shape source)
    {context final : SourceSemantics.Context} {control : ControlContext} {facts : StatementFacts}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (typed : StatementHasType source control context shape.block.node.id final facts)
    (fStored : StoredIdentity shape.f context environment before)
    (flag : Bool) (flagStored : StoredValue shape.flag environment before (.bool flag)) :
    ∃ after, Dynamic.StatementExecutes program context evidence source environment before shape.block.node.id
      final (.fallthrough environment) after ∧ HeapAppends before after := by
  have original := form_at state.runtime.graph.nodeOccurrencesUnique shape.block.found typed
  rw [shape.block.formEq] at original
  cases original with
  | block bodyTyped =>
    obtain ⟨firstContext,_,_,firstTyped,branchTypedList⟩ := head_tail bodyTyped
    obtain ⟨branchContext,_,_,branchTyped,_⟩ := head_tail branchTypedList
    have initializer := initializer_typed shape.firstLet state.runtime.graph.nodeOccurrencesUnique
      (by rw [shape.firstScheme]; rfl) firstTyped
    obtain ⟨_,_,_,literalTyped⟩ := call_typed shape.firstCall state.runtime.graph.nodeOccurrencesUnique initializer
    have literal := shape.eleven.evaluates (program := program) evidence environment before state.runtime.graph.nodeOccurrencesUnique literalTyped
    rw [shape.elevenValue] at literal
    obtain ⟨middle,firstCallTrace,firstCallAppend⟩ := fStored.invoke state wellFormed shape.firstCall (.inl rfl) initializer literal
    obtain ⟨firstTrace,firstState,firstStored,firstExtended⟩ := ordinary_step shape.firstLet state wellFormed
      (by rw [shape.firstScheme]; rfl) firstTyped firstCallTrace
    let firstHeap := valueHeap middle shape.first (.word (Word.ofNatModulo 11))
    have firstAppend : HeapAppends middle firstHeap := ⟨_,rfl⟩
    have fAtFirst := ((fStored.mono firstCallAppend).mono firstAppend).under shape.first
      ⟨middle.cells.length⟩ shape.firstF firstExtended
    have flagAtFirst := ((flagStored.mono firstCallAppend).mono firstAppend).under
      ⟨middle.cells.length⟩ shape.firstFlag
    obtain ⟨after,branchTrace,branchAppend⟩ := shape.branch_trace firstState wellFormed branchTyped fAtFirst
      firstStored flag flagAtFirst
    exact ⟨after,.block (lookupStatement?_sound shape.block.found) shape.block.formEq
      (.cons firstTrace (.cons branchTrace .nil)),firstCallAppend.trans (firstAppend.trans branchAppend)⟩

end Tests.SourceCoreMixedImperative
