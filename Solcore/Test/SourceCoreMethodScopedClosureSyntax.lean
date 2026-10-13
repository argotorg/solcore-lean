import Solcore.Test.SourceCoreMethodScopedFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodRootStaticSupport
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreMethodScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodRootStaticSupport (NoIndirectSource)
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
    {resultType : TypeSystem.Ty} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (expression : ExpressionNode)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = resultType)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression.id))
    (annotation : node.type = resultType) (leaf : approved expression.id)
    (typed : StatementHasType source {returnType := resultType} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) resultType := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation expressionFound expressionType
        (by simpa only [expressionType] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder : TypedBinder} {payload resultType : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (expression : ExpressionNode)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal expression.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved expression.id)
    (typed : SourceAssignmentHasType source context assignment .equal expression.id)
    (remaining : GenericImperativeMatch.Syntax source approved context (.statements mode rest) resultType) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) resultType := by
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
    {binder : TypedBinder} {payload resultType : TypeSystem.Ty} {node : StatementNode} {expression : ExpressionNode}
    {approved : ExpressionId → Prop} {rest : List StatementId}
    (found : source.lookupStatement? node.id = some node)
    (form : node.form = .letDecl binder (some expression.id))
    (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
    (scheme : binder.scheme = .mono payload)
    (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : source.lookupExpression? expression.id = some expression)
    (expressionType : expression.type = payload) (leaf : approved expression.id)
    (typed : Dynamic.StatementHasType.FormTyping source {returnType := resultType} context node.form middle)
    (remaining : GenericImperativeMatch.Syntax source approved middle (.statements true rest) resultType) :
    GenericImperativeMatch.Syntax source approved context (.statements true (node.id :: rest)) resultType := by
  rw [form] at typed
  cases typed with
  | letInitialized value mono extended =>
    exact .initialized found form declaration mono extended ordinary expressionFound
      (by rw [expressionType, scheme]; rfl)
      (by simpa only [scheme, TypeSystem.Scheme.mono, expressionType] using value) leaf remaining
  | letInitializedGeneralized poly _ _ _ _ =>
    exact False.elim (poly (by rw [scheme]; rfl))


section Metadata
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedFactoryShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)
include nodes in
theorem SelectedFactoryShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.call.value.node ∨ node = shape.conditionRead.node ∨ node = shape.loopSecondRead.node ∨ node = shape.loopCall.value.node ∨ node = shape.stop.node ∨ node = shape.finalRead.node ∨ node = shape.finalCall.value.node ∨ node = shape.expression.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedFactoryShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present
include nodes in
theorem SelectedFactoryShape.no_indirect : NoIndirectSource function.typedBody := by
  intro id node callee ids metadata found form
  rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
  all_goals subst node
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.call.form] at form; cases form
  · rw [shape.conditionRead.form] at form; cases form
  · rw [shape.loopSecondRead.form] at form; cases form
  · rw [shape.loopCall.form] at form; cases form
  · rw [shape.stopForm] at form; cases form
  · rw [shape.finalRead.form] at form; cases form
  · rw [shape.finalCall.form] at form; cases form
  · rw [shape.lambda] at form; cases form

include nodes in
theorem SelectedFactoryShape.metadata {fixture : CompiledFixture} {directSites : DeclarationInstantiation → Prop}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []) :
    MetadataFor fixture.recipe.compiled.indexed named function.typedBody directSites := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact .inl shape.firstRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.call.form]; trivial)))
    · exact .inl shape.conditionRead.requirements
    · exact .inl shape.loopSecondRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.loopCall.form]; trivial)))
    · exact .inl shape.stop.requirements
    · exact .inl shape.finalRead.requirements
    · exact .inr (.inr (.inr (by rw [shape.finalCall.form]; trivial)))
    · exact .inl shape.expression.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same | same | same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.call.value.coercions
    · exact shape.conditionRead.coercions
    · exact shape.loopSecondRead.coercions
    · exact shape.loopCall.value.coercions
    · exact shape.stop.coercions
    · exact shape.finalRead.coercions
    · exact shape.finalCall.value.coercions
    · exact shape.expression.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    exact False.elim (shape.no_indirect nodes id node callee ids metadata found form)
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]
end Metadata
section Factory
variable {function : CheckedFunction} {type : TypeSystem.Ty}
  (shape : SelectedFactoryShape function type)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem SelectedFactoryShape.local_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.localBinder.id = .ok shape.localBinder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.localOwner, shape.localScheme, TypeSystem.Scheme.mono, shape.localRequirements, Ne.symm shape.localFirst, Ne.symm shape.localSecond, Ne.symm shape.localFlag]

include nodes in
theorem SelectedFactoryShape.flag_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.flag.id = .ok shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.flagOwner, shape.flagScheme, TypeSystem.Scheme.mono, shape.flagRequirements, Ne.symm shape.flagFirst, Ne.symm shape.flagSecond, shape.localFlag]

include nodes in
theorem SelectedFactoryShape.first_declaration :
    SourceCoreDataPlaces.rootBinder function.typedBody shape.first.id = .ok shape.first := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, shape.inputs, nodes, SelectedFactoryShape.nodeList,
    shape.firstRead.form, shape.call.form, shape.conditionRead.form, shape.loopSecondRead.form, shape.loopCall.form, shape.stopForm, shape.finalRead.form, shape.finalCall.form, shape.initializedForm, shape.assignmentForm, shape.flagAssignmentForm, shape.loopForm, shape.statementForm, shape.lambda, shape.outerReturnForm,
    shape.firstOwner, shape.firstScheme, TypeSystem.Scheme.mono, shape.firstRequirements, shape.different, shape.flagFirst, shape.localFirst]

theorem SelectedFactoryShape.body_shape :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.typedBody true shape.body :=
  .initialized shape.initializedFound shape.initializedForm
    (.whileLoop shape.loopFound shape.loopForm
      (.assign shape.assignmentFound shape.assignmentForm shape.targetBare
        (.assign shape.flagAssignmentFound shape.flagAssignmentForm shape.flagTargetBare .nil))
      (.returnValue [] shape.statementFound shape.statementForm))

def SelectedFactoryShape.childIds : List ExpressionId :=
  [shape.call.value.node.id, shape.conditionRead.node.id, shape.loopCall.value.node.id,
    shape.stop.node.id, shape.finalCall.value.node.id]

include nodes in
theorem SelectedFactoryShape.body_syntax
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ shape.childIds, approved id)
    (typed : StatementsHaveType function.typedBody {returnType := type}
      context shape.body final facts) :
    GenericImperativeMatch.Syntax function.typedBody approved context
      (.statements true shape.body) type := by
  obtain ⟨locals, _, _, initialized, tail⟩ := head_tail typed
  apply initialized_syntax shape.initializedFound shape.initializedForm
    (shape.local_declaration nodes) shape.localScheme
    (by simp [shape.inputs, Ne.symm shape.localFirst, Ne.symm shape.localSecond, Ne.symm shape.localFlag])
    shape.call.value.found shape.call.value.type (leaves _ (by simp [childIds]))
    (form_at unique shape.initializedFound initialized)
  obtain ⟨middle, _, _, first, suffix⟩ := head_tail tail
  have firstForm := form_at unique shape.loopFound first
  rw [shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop shape.loopFound shape.loopForm
      shape.conditionRead.found shape.conditionRead.type
      (by simpa only [shape.conditionRead.type] using conditionTyped) (leaves _ (by simp [childIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique shape.assignmentFound assignedHead
      rw [shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned shape.loopCall.value.node shape.loopCall.value.found shape.loopCall.value.type
          shape.assignmentFound shape.assignmentForm
          (by rw [shape.targetRoot]; exact shape.first_declaration nodes)
          shape.firstScheme shape.targetBare shape.targetType
          (leaves _ (by simp [childIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique shape.flagAssignmentFound flagHead
        rw [shape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned shape.stop.node shape.stop.found shape.stop.type
            shape.flagAssignmentFound shape.flagAssignmentForm
            (by rw [shape.flagTargetRoot]; exact shape.flag_declaration nodes)
            shape.flagScheme shape.flagTargetBare shape.flagTargetType
            (leaves _ (by simp [childIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail suffix
      exact returning unique shape.finalCall.value.node shape.finalCall.value.found shape.finalCall.value.type
        shape.statementFound shape.statementForm shape.statementType (leaves _ (by simp [childIds])) returningHead
end Factory
theorem SelectedFactoryShape.children {function : CheckedFunction} {type : TypeSystem.Ty}
    (shape : SelectedFactoryShape function type) :
    ∀ id ∈ shape.childIds, GeneralSyntax function.typedBody id (fun _ => False) := by
  intro id member
  simp only [SelectedFactoryShape.childIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .unary shape.call.value.found shape.call.form (.leaf (.read shape.firstRead.found shape.firstRead.form))
  · exact .leaf (.read shape.conditionRead.found shape.conditionRead.form)
  · exact .unary shape.loopCall.value.found shape.loopCall.form (.leaf (.read shape.loopSecondRead.found shape.loopSecondRead.form))
  · exact .leaf (.literal shape.stop.found (shape.stopForm ▸ .bool _ _))
  · exact .unary shape.finalCall.value.found shape.finalCall.form (.leaf (.read shape.finalRead.found shape.finalRead.form))

end Tests.SourceCoreMethodScoped
