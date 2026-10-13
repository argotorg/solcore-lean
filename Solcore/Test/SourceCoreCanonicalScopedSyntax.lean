import Solcore.Test.SourceCoreCanonicalScopedFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

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

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (expression : ExpressionNode) (expressionFound : source.lookupExpression? expression.id = some expression) (expressionType : expression.type = .word)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression.id))
    (annotation : node.type = .word) (leaf : approved expression.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation expressionFound expressionType
        (by simpa only [expressionType] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (expression : ExpressionNode) (expressionFound : source.lookupExpression? expression.id = some expression) (expressionType : expression.type = payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal expression.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved expression.id)
    (typed : SourceAssignmentHasType source context assignment .equal expression.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericImperativeMatch.Syntax.assign found form
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [scheme, bare, targetType]
            exact .nil _
          · intro actual actualFound
            have same := Except.ok.inj (declaration.symm.trans actualFound)
            subst actual
            rw [bare] at projections
            cases projections
            have word := target.symm.trans targetType
            simpa only [word, scheme, TypeSystem.Scheme.mono] using writable
          · simpa only [target] using rhs
          · exact .inl rfl
          · intro child member
            simp only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_cons, List.not_mem_nil, or_false] at member
            subst child
            exact ⟨leaf, expression, expressionFound, by simpa only [← target, targetType, expressionType] using rhs⟩
          · exact remaining

private theorem initialized_syntax {source : TypedSource} {context middle : SourceSemantics.Context}
    {binder : TypedBinder} {node : StatementNode} {expression : ExpressionNode}
    {approved : ExpressionId → Prop} {rest : List StatementId}
    (found : source.lookupStatement? node.id = some node)
    (form : node.form = .letDecl binder (some expression.id))
    (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
    (scheme : binder.scheme = .mono .word)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = .word) (leaf : approved expression.id)
    (typed : Dynamic.StatementHasType.FormTyping source {returnType := .word} context node.form middle)
    (remaining : GenericImperativeMatch.Syntax source approved middle (.statements true rest) .word) :
    GenericImperativeMatch.Syntax source approved context (.statements true (node.id :: rest)) .word := by
  rw [form] at typed
  cases typed with
  | letInitialized value mono extended =>
    exact .initialized found form declaration mono extended ordinary expressionFound
      (by rw [expressionType, scheme]; rfl)
      (by simpa only [scheme, TypeSystem.Scheme.mono, expressionType] using value) leaf remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [scheme]; rfl))

theorem ObservedProgram.make_seed_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (seedScheme : observed.makeShape.binder.scheme = .mono .word) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.binder.id = .ok observed.makeShape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.binderOwner, observed.makeShape.argumentDistinct, observed.makeShape.flagDistinct, observed.makeShape.stopDistinct, observed.makeShape.previousDistinct, seedScheme, observed.makeShape.binderRequirements]

theorem ObservedProgram.make_flag_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.flag.id = .ok observed.makeShape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.flagOwner, Ne.symm observed.makeShape.flagDistinct, Ne.symm observed.makeShape.flagArgument, observed.makeShape.stopFlag, observed.makeShape.previousFlag, observed.makeShape.flagScheme, observed.makeShape.flagRequirements]

theorem ObservedProgram.make_previous_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.makeRow.row.function.typedBody observed.makeShape.previous.id = .ok observed.makeShape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.makeShape.inputs,
    observed.makeNodes, FactoryShape.nodeList, TypeSystem.Scheme.mono,
    observed.makeShape.initialRead.form, observed.makeShape.initial.calleeForm, observed.makeShape.initial.form, observed.makeShape.conditionRead.form, observed.makeShape.argumentRead.form, observed.makeShape.updated.calleeForm, observed.makeShape.updated.form, observed.makeShape.stopRead.form, observed.makeShape.previousRead.form, observed.makeShape.final.calleeForm, observed.makeShape.final.form, observed.makeShape.initializedForm, observed.makeShape.assignmentForm, observed.makeShape.flagAssignmentForm, observed.makeShape.loopForm, observed.makeShape.innerReturnForm, observed.makeShape.lambda, observed.makeShape.returnStatement, observed.makeShape.previousOwner, Ne.symm observed.makeShape.previousDistinct, Ne.symm observed.makeShape.previousArgument, Ne.symm observed.makeShape.previousFlag, Ne.symm observed.makeShape.previousStop, observed.makeShape.previousScheme, observed.makeShape.previousRequirements]

theorem ObservedProgram.relay_local_declaration {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    SourceCoreDataPlaces.rootBinder observed.relayRow.row.function.typedBody observed.relayShape.localBinder.id = .ok observed.relayShape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.relayShape.inputs,
    observed.relayNodes, RelayShape.nodeList, observed.relayShape.initialRead.form,
    observed.relayShape.initial.calleeForm, observed.relayShape.initial.form,
    observed.relayShape.finalRead.form, observed.relayShape.initializedForm, observed.relayShape.statementForm,
    observed.relayShape.localOwner, Ne.symm observed.relayShape.localDistinct,
    observed.relayShape.localScheme, TypeSystem.Scheme.mono, observed.relayShape.localRequirements]

theorem ObservedProgram.make_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.makeRow.row.function.typedBody true observed.makeShape.body :=
  .initialized observed.makeShape.initializedFound observed.makeShape.initializedForm
    (.whileLoop observed.makeShape.loopFound observed.makeShape.loopForm
      (.assign observed.makeShape.assignmentFound observed.makeShape.assignmentForm observed.makeShape.targetBare
        (.assign observed.makeShape.flagAssignmentFound observed.makeShape.flagAssignmentForm observed.makeShape.flagTargetBare .nil))
      (.returnValue [] observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm))

def ObservedProgram.childIds {fixture : CompiledFixture} (observed : ObservedProgram fixture) : List ExpressionId :=
  [observed.makeShape.initial.value.node.id, observed.makeShape.conditionRead.node.id,
    observed.makeShape.updated.value.node.id, observed.makeShape.stopRead.node.id, observed.makeShape.final.value.node.id]

theorem ObservedProgram.make_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (seedScheme : observed.makeShape.binder.scheme = .mono .word)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.makeRow.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.childIds, approved id)
    (typed : StatementsHaveType observed.makeRow.row.function.typedBody {returnType := .word}
      context observed.makeShape.body final facts) :
    GenericImperativeMatch.Syntax observed.makeRow.row.function.typedBody approved context
      (.statements true observed.makeShape.body) .word := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax observed.makeShape.initializedFound observed.makeShape.initializedForm
    observed.make_previous_declaration observed.makeShape.previousScheme
    (by simp [observed.makeShape.inputs, Ne.symm observed.makeShape.previousDistinct])
    observed.makeShape.initial.value.found observed.makeShape.initial.value.type
    (leaves _ (by simp [childIds])) (form_at unique observed.makeShape.initializedFound initialized)
  obtain ⟨middle, _, _, first, suffix⟩ := head_tail tail
  have firstForm := form_at unique observed.makeShape.loopFound first
  rw [observed.makeShape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop observed.makeShape.loopFound observed.makeShape.loopForm
      observed.makeShape.conditionRead.found observed.makeShape.conditionRead.type
      (by simpa only [observed.makeShape.conditionRead.type] using conditionTyped) (leaves _ (by simp [childIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.makeShape.assignmentFound assignedHead
      rw [observed.makeShape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned observed.makeShape.updated.value.node observed.makeShape.updated.value.found observed.makeShape.updated.value.type
          observed.makeShape.assignmentFound observed.makeShape.assignmentForm
          (by rw [observed.makeShape.targetRoot]; exact observed.make_seed_declaration seedScheme)
          seedScheme observed.makeShape.targetBare observed.makeShape.targetType
          (leaves _ (by simp [childIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique observed.makeShape.flagAssignmentFound flagHead
        rw [observed.makeShape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned observed.makeShape.stopRead.node observed.makeShape.stopRead.found observed.makeShape.stopRead.type
            observed.makeShape.flagAssignmentFound observed.makeShape.flagAssignmentForm
            (by rw [observed.makeShape.flagTargetRoot]; exact observed.make_flag_declaration)
            observed.makeShape.flagScheme observed.makeShape.flagTargetBare observed.makeShape.flagTargetType
            (leaves _ (by simp [childIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail suffix
      exact returning unique observed.makeShape.final.value.node observed.makeShape.final.value.found
        observed.makeShape.final.value.type observed.makeShape.innerReturnFound observed.makeShape.innerReturnForm
        observed.makeShape.innerReturnType (leaves _ (by simp [childIds])) returningHead

theorem ObservedProgram.relay_body_shape {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.relayRow.row.function.typedBody true
      [observed.relayShape.initialized.id, observed.relayShape.statement.id] :=
  .initialized observed.relayShape.initializedFound observed.relayShape.initializedForm
    (.returnValue [] observed.relayShape.statementFound observed.relayShape.statementForm)

theorem ObservedProgram.relay_body_syntax {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.relayRow.row.function.typedBody) {approved : ExpressionId → Prop}
    (initialApproved : approved observed.relayShape.initial.value.node.id)
    (finalApproved : approved observed.relayShape.finalRead.node.id)
    (typed : StatementsHaveType observed.relayRow.row.function.typedBody {returnType := .word}
      context [observed.relayShape.initialized.id, observed.relayShape.statement.id] final facts) :
    GenericImperativeMatch.Syntax observed.relayRow.row.function.typedBody approved context
      (.statements true [observed.relayShape.initialized.id, observed.relayShape.statement.id]) .word := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax observed.relayShape.initializedFound observed.relayShape.initializedForm
    observed.relay_local_declaration observed.relayShape.localScheme
    (by simp [observed.relayShape.inputs, Ne.symm observed.relayShape.localDistinct])
    observed.relayShape.initial.value.found observed.relayShape.initial.value.type initialApproved
    (form_at unique observed.relayShape.initializedFound initialized)
  obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
  exact returning unique observed.relayShape.finalRead.node observed.relayShape.finalRead.found
    observed.relayShape.finalRead.type observed.relayShape.statementFound observed.relayShape.statementForm
    observed.relayShape.statementType finalApproved returningHead

end Tests.SourceCoreCanonicalScoped
