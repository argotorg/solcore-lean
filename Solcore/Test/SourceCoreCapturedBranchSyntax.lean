import Solcore.Test.SourceCoreCapturedBranchFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots

/-! The original typed branch body supplies scoped arms and its restored
suffix. Only the actual read occurrences and plain captured writes are used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedBranch
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
    {binder rhsBinder : TypedBinder} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    (read : WordRead source rhsBinder) (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal read.node.id)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono .word) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = .word) (leaf : approved read.node.id)
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

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.earlyConditionRead.form,
    observed.shape.initialRead.form, observed.shape.argumentRead.form, observed.shape.previousRead.form,
    observed.shape.earlyRead.form, observed.shape.finalRead.form, observed.shape.initializedForm,
    observed.shape.assignmentForm, observed.shape.elseAssignmentForm, observed.shape.branchForm,
    observed.shape.earlyBranchForm, observed.shape.earlyReturnForm, observed.innerReturnForm,
    observed.lambda, observed.returnStatement, observed.shape.previousOwner,
    Ne.symm observed.shape.previousDistinct, Ne.symm observed.shape.previousArgument,
    Ne.symm observed.shape.previousFlag, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.conditionRead.form, observed.shape.earlyConditionRead.form,
    observed.shape.initialRead.form, observed.shape.argumentRead.form, observed.shape.previousRead.form,
    observed.shape.earlyRead.form, observed.shape.finalRead.form, observed.shape.initializedForm,
    observed.shape.assignmentForm, observed.shape.elseAssignmentForm, observed.shape.branchForm,
    observed.shape.earlyBranchForm, observed.shape.earlyReturnForm, observed.innerReturnForm,
    observed.lambda, observed.returnStatement, observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.shape.flagDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .conditional observed.shape.branchFound observed.shape.branchForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare .nil)
    (.initialized observed.shape.initializedFound observed.shape.initializedForm
      (.assign observed.shape.elseAssignmentFound observed.shape.elseAssignmentForm observed.shape.elseTargetBare .nil))
    (.conditional observed.shape.earlyBranchFound observed.shape.earlyBranchForm
      (.returnValue [] observed.shape.earlyReturnFound observed.shape.earlyReturnForm) .nil
      (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm))

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.conditionRead.node.id, observed.shape.argumentRead.node.id, observed.shape.initialRead.node.id,
    observed.shape.previousRead.node.id, observed.shape.earlyConditionRead.node.id,
    observed.shape.earlyRead.node.id, observed.shape.finalRead.node.id]

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
  have firstForm := form_at unique observed.shape.branchFound first
  rw [observed.shape.branchForm] at firstForm
  cases firstForm with
  | ifWithElse conditionTyped thenTyped elseTyped =>
    apply GenericImperativeMatch.Syntax.ifThen observed.shape.branchFound observed.shape.branchForm
      observed.shape.branchType observed.shape.conditionRead.found observed.shape.conditionRead.type
      (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail thenTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.argumentRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
          observed.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨boundContext, _, _, initializedHead, rest⟩ := head_tail elseTyped
      have initialized := form_at unique observed.shape.initializedFound initializedHead
      rw [observed.shape.initializedForm] at initialized
      have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
      cases initialized with
      | letInitializedGeneralized polymorphic _ _ _ _ => exact False.elim (polymorphic mono)
      | letInitialized initialTyped _ extended =>
        apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
          observed.previous_declaration mono extended
          (by simp [observed.inputs, Ne.symm observed.shape.previousDistinct])
          observed.shape.initialRead.found (by rw [observed.shape.initialRead.type, observed.shape.previousScheme]; rfl)
          (by simpa only [observed.shape.initialRead.type, observed.shape.previousScheme, TypeSystem.Scheme.mono] using initialTyped)
          (leaf _ (by simp [readIds]))
        obtain ⟨_, _, _, assignedHead, _⟩ := head_tail rest
        have assignment := form_at unique observed.shape.elseAssignmentFound assignedHead
        rw [observed.shape.elseAssignmentForm] at assignment
        cases assignment with
        | assignValue assignmentTyped =>
          exact assigned observed.shape.previousRead observed.shape.elseAssignmentFound observed.shape.elseAssignmentForm
            (by rw [observed.shape.elseTargetRoot]; exact observed.seed_declaration)
            observed.binderScheme observed.shape.elseTargetBare observed.shape.elseTargetType
            (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, early, last⟩ := head_tail tail
      have earlyForm := form_at unique observed.shape.earlyBranchFound early
      rw [observed.shape.earlyBranchForm] at earlyForm
      cases earlyForm with
      | ifWithoutElse conditionTyped thenTyped =>
        apply GenericImperativeMatch.Syntax.ifThen observed.shape.earlyBranchFound observed.shape.earlyBranchForm
          observed.shape.earlyBranchType observed.shape.earlyConditionRead.found observed.shape.earlyConditionRead.type
          (by simpa only [observed.shape.earlyConditionRead.type] using conditionTyped) (leaf _ (by simp [readIds]))
        · obtain ⟨_, _, _, returningHead, _⟩ := head_tail thenTyped
          exact returning unique observed.shape.earlyRead observed.shape.earlyReturnFound observed.shape.earlyReturnForm
            observed.shape.earlyReturnType (leaf _ (by simp [readIds])) returningHead
        · exact .body (.nil (.inl rfl))
        · obtain ⟨_, _, _, returningHead, _⟩ := head_tail last
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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩
  · exact ⟨_, _, _, observed.shape.earlyConditionRead.found, observed.shape.earlyConditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.earlyRead.found, observed.shape.earlyRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

end Tests.SourceCoreCapturedBranch
