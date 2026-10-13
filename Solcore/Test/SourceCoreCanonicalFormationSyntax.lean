import Solcore.Test.SourceCoreCanonicalFormationMetadata
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreCanonicalFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original


theorem ObservedProgram.make_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.localBinder.id = .ok observed.makeShape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, observed.makeShape.initialRead.form,
    observed.makeShape.initial.calleeForm, observed.makeShape.initial.form,
    observed.makeShape.read.form, observed.makeShape.call.calleeForm, observed.makeShape.call.form,
    observed.makeShape.initializedForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda,
    observed.makeShape.returnStatement, observed.makeShape.localOwner, Ne.symm observed.makeShape.localDistinct,
    observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.localRequirements]

theorem ObservedProgram.make_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.makeRow.row.function.typedBody true
      [observed.makeShape.initialized.id, observed.makeShape.statement.id] :=
  .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
    (.returnValue [] observed.makeShape.statementFound observed.makeShape.returnStatement)

theorem ObservedProgram.make_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (unique : NodeOccurrencesUnique observed.makeRow.row.function.typedBody)
    {approved : ExpressionId → Prop} (initial : approved observed.makeShape.initial.value.node.id)
    (formation : approved observed.makeShape.expression.id)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType observed.makeRow.row.function.typedBody {returnType := closureType} context
      [observed.makeShape.initialized.id, observed.makeShape.statement.id] final facts) :
    GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved context
      (.statements true [observed.makeShape.initialized.id, observed.makeShape.statement.id]) closureType := by
  obtain ⟨middle, firstFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.makeShape.initializedFound first
  rw [observed.makeShape.initializedForm] at firstForm
  have remaining : GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved middle
      (.statements true [observed.makeShape.statement.id]) closureType := by
    obtain ⟨_, _, _, returned, _⟩ := head_tail tail
    have actual := form_at unique observed.makeShape.statementFound returned
    rw [observed.makeShape.returnStatement] at actual
    cases actual with
    | returnValue expression =>
      exact .body (.returnValue [] observed.makeShape.statementFound observed.makeShape.returnStatement
        observed.makeShape.statementType observed.makeShape.expressionFound observed.makeShape.expressionType
        (by simpa only [observed.makeShape.expressionType] using expression) formation)
  cases firstForm with
  | letInitialized value mono extended =>
    exact .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
      observed.make_local_declaration mono extended
      (by simp [observed.makeShape.inputs, Ne.symm observed.makeShape.localDistinct])
      observed.makeShape.initial.value.found
      (by rw [observed.makeShape.initial.value.type, observed.makeShape.localScheme]; rfl)
      (by simpa only [observed.makeShape.localScheme, TypeSystem.Scheme.mono, observed.makeShape.initial.value.type] using value)
      initial remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [observed.makeShape.localScheme]; rfl))

end Tests.SourceCoreCanonicalFormation
