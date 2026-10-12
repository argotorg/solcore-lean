import Solcore.Test.SourceCoreNamedBranchFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots

/-! The actual checked conditional supplies both lexical arms and the stopping
receipts for their dead suffix. All child certificates describe local reads. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreNamedBranch
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem form_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {node : StatementNode} {facts : StatementFacts}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context node.id final facts)
    (found : source.lookupStatement? node.id = some node) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, form⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact form

private theorem returning {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {binder : TypedBinder}
    {statement : StatementNode} {facts : StatementFacts} {mode : Bool}
    (read : WordRead source binder) (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context statement.id final facts)
    (found : source.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some read.node.id))
    (type : statement.type = .word) (returns : control.returnType = .word) :
    GenericLexicalStatements.Syntax source (fun id => ∃ node name binderId,
      source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      context mode [statement.id] .word := by
  have formTyped := form_typed unique typed found
  rw [form] at formTyped
  cases formTyped with
  | returnValue valueTyped =>
    exact .returnValue [] found form type read.found read.type
      (by simpa only [returns, read.type] using valueTyped) ⟨_, _, _, read.found, read.form⟩

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.statements]
  exact .conditional observed.shape.branchFound observed.shape.branchForm
    (.initialized observed.shape.initializedFound observed.shape.initializedForm
      (.returnValue [] observed.shape.thenReturnFound observed.shape.thenReturnForm))
    (.returnValue [] observed.shape.elseReturnFound observed.shape.elseReturnForm) .nil

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericLexicalStatements.Syntax actual.header.function.source (fun id => ∃ node name binderId,
      actual.header.function.source.lookupExpression? id = some node ∧ node.form = .reference name (.local binderId))
      actual.header.context true actual.header.function.body actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.statements, actual.result_type]
  have unique : NodeOccurrencesUnique observed.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | singleton head =>
    have formTyped := form_typed unique head observed.shape.branchFound
    rw [observed.shape.branchForm] at formTyped
    cases formTyped with
    | ifWithElse conditionTyped yes no =>
      cases yes with
      | cons initialized tail =>
        have initialTyped := form_typed unique initialized observed.shape.initializedFound
        rw [observed.shape.initializedForm] at initialTyped
        have thenStopped : GenericLexicalStatements.Stopped observed.row.function.typedBody
            [observed.shape.initialized.id, observed.shape.thenReturn.id] := GenericLexicalStatements.Stopped.of_source
          (ReachableStatementContinuations.StoppingStatements.prefix observed.shape.initializedFound initialized
            (.stop (.returnValue observed.shape.thenReturnFound observed.shape.thenReturnForm)))
        have elseStopped : GenericLexicalStatements.Stopped observed.row.function.typedBody
            [observed.shape.elseReturn.id] := GenericLexicalStatements.Stopped.of_source
          (ReachableStatementContinuations.StoppingStatements.stop
            (.returnValue observed.shape.elseReturnFound observed.shape.elseReturnForm))
        apply GenericLexicalStatements.Syntax.terminalIf unique observed.shape.branchFound observed.shape.branchForm
          observed.shape.branchType observed.shape.conditionRead.found observed.shape.conditionRead.type
          (by simpa only [observed.shape.conditionRead.type] using conditionTyped)
          ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
        · cases initialTyped with
          | letInitialized initializer mono extended =>
            apply GenericLexicalStatements.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
              observed.local_declaration mono extended
              (by simp [observed.shape.inputs, Ne.symm observed.shape.localFlag, Ne.symm observed.shape.localArgument])
              observed.shape.initialRead.found
              (by simp [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono])
              (by simpa only [observed.shape.initialRead.type, observed.shape.localScheme, TypeSystem.Scheme.mono] using initializer)
              ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
            cases tail with
            | singleton last =>
              exact returning observed.shape.localRead unique last observed.shape.thenReturnFound
                observed.shape.thenReturnForm observed.shape.thenReturnType rfl
          | letInitializedGeneralized polymorphic _ _ _ _ =>
            exact False.elim (polymorphic (by simp [observed.shape.localScheme, TypeSystem.Scheme.mono]))
        · cases no with
          | singleton last =>
              exact returning observed.shape.elseRead unique last observed.shape.elseReturnFound
                observed.shape.elseReturnForm observed.shape.elseReturnType rfl
        · exact thenStopped
        · exact elseStopped

end Tests.SourceCoreNamedBranch
