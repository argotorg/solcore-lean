import Solcore.Test.SourceCoreCapturedWhileFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots

/-! The original typed loop body supplies its condition, two writes and restored
suffix. Every expression is an actual local read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedWhile
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

private theorem returning {source : TypedSource} {context final : SourceSemantics.Context}
    {binder : TypedBinder} {id : StatementId} {node : StatementNode} {facts : StatementFacts}
    {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (unique : NodeOccurrencesUnique source) (read : WordRead source binder)
    (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some read.node.id))
    (annotation : node.type = .word) (leaf : approved read.node.id)
    (typed : StatementHasType source {returnType := .word} context id final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements mode (id :: rest)) .word := by
  have original := form_at unique found typed
  rw [form] at original
  cases original with
  | returnValue value =>
      exact .body (.returnValue rest found form annotation read.found read.type
        (by simpa only [read.type] using value) leaf)

private theorem assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : Read source rhsBinder payload) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
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
            exact ⟨leaf, read.node, read.found, by simpa only [← target, targetType, read.type] using rhs⟩
          · exact remaining

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form,
    observed.shape.argumentRead.form, observed.shape.stopRead.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.flagAssignmentForm, observed.shape.loopForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement, observed.shape.binderOwner, observed.shape.flagDistinct, observed.shape.argumentDistinct,
    observed.shape.stopDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements]

theorem ObservedFactory.flag_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.flag.id = .ok observed.shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form,
    observed.shape.argumentRead.form, observed.shape.stopRead.form, observed.shape.finalRead.form,
    observed.shape.assignmentForm, observed.shape.flagAssignmentForm, observed.shape.loopForm,
    observed.innerReturnForm, observed.lambda, observed.returnStatement, observed.shape.flagOwner, observed.shape.flagScheme, TypeSystem.Scheme.mono,
    Ne.symm observed.shape.flagDistinct, observed.shape.argumentFlag, observed.shape.stopFlag, observed.shape.flagRequirements]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .whileLoop observed.shape.loopFound observed.shape.loopForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare
      (.assign observed.shape.flagAssignmentFound observed.shape.flagAssignmentForm observed.shape.flagTargetBare .nil))
    (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.conditionRead.node.id, observed.shape.argumentRead.node.id,
    observed.shape.stopRead.node.id, observed.shape.finalRead.node.id]

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true observed.shape.body) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.loopFound first
  rw [observed.shape.loopForm] at firstForm
  cases firstForm with
  | whileLoop conditionTyped bodyTyped =>
    apply GenericImperativeMatch.Syntax.whileLoop observed.shape.loopFound observed.shape.loopForm
      observed.shape.conditionRead.found observed.shape.conditionRead.type
      (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, rest⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        apply assigned observed.shape.argumentRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
          observed.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped
        obtain ⟨_, _, _, flagHead, _⟩ := head_tail rest
        have flagAssignment := form_at unique observed.shape.flagAssignmentFound flagHead
        rw [observed.shape.flagAssignmentForm] at flagAssignment
        cases flagAssignment with
        | assignValue flagTyped =>
          exact assigned observed.shape.stopRead observed.shape.flagAssignmentFound observed.shape.flagAssignmentForm
            (by rw [observed.shape.flagTargetRoot]; exact observed.flag_declaration)
            observed.flagScheme observed.shape.flagTargetBare observed.shape.flagTargetType
            (leaf _ (by simp [readIds])) flagTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.innerReturnFound observed.shape.innerReturnForm
        observed.shape.innerReturnType (leaf _ (by simp [readIds])) returningHead

theorem ObservedFactory.body_reads {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context observed.shape.body final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody)
      context (.statements true observed.shape.body) .word := by
  apply observed.body_syntax unique _ typed
  intro id member
  simp only [readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.stopRead.found, observed.shape.stopRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

end Tests.SourceCoreCapturedWhile
