import Solcore.Test.SourceCoreNamedOperatorsFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBranchingReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots

/-! The original typed loop supplies comparison, subtraction, assignment and return.
Recursive expression syntax retains both actual validated integer-literal children. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedOperators
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
    (unique : NodeOccurrencesUnique source) (read : Read source binder .word)
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
    {binder : TypedBinder} {payload : TypeSystem.Ty} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {mode : Bool} {rest : List StatementId}
    {rhs : ExpressionId} {rhsNode : ExpressionNode}
    (rhsFound : source.lookupExpression? rhs = some rhsNode) (rhsType : rhsNode.type = payload)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal rhs)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved rhs)
    (typed : SourceAssignmentHasType source context assignment .equal rhs)
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
            exact ⟨leaf, rhsNode, rhsFound, by simpa only [← target, targetType, rhsType] using rhs⟩
          · exact remaining

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .whileLoop observed.shape.loopFound observed.shape.loopForm
    (.assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare .nil)
    (.returnValue [] observed.shape.statementFound observed.shape.statementForm)

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.comparison.node.id, observed.shape.difference.node.id, observed.shape.finalRead.node.id]

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
      observed.shape.comparison.found observed.shape.comparison.type
      (by simpa only [observed.shape.comparison.type] using conditionTyped) (leaf _ (by simp [readIds]))
    · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.difference.found observed.shape.difference.type observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.binder_declaration)
          observed.shape.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.statementFound observed.shape.statementForm
        observed.shape.statementType (leaf _ (by simp [readIds])) returningHead

theorem ActualHeader.syntax {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    GenericImperativeMatch.Syntax actual.header.function.source
      (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax actual.header.function.source)
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.shape.roots, actual.result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.body, actual.result_type]
  apply observed.body_syntax (actual.source ▸ actual.header.unique) _ typed
  intro id member
  simp only [ObservedFactory.readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .binary observed.shape.comparison.found observed.shape.comparison.form
      (.leaf (.read observed.shape.conditionRead.found observed.shape.conditionRead.form))
      (.leaf (.literal observed.shape.zero.found (observed.shape.zero.form ▸ .integer _ _)))
  · exact .binary observed.shape.difference.found observed.shape.difference.form
      (.leaf (.read observed.shape.argumentRead.found observed.shape.argumentRead.form))
      (.leaf (.literal observed.shape.one.found (observed.shape.one.form ▸ .integer _ _)))
  · exact .leaf (.read observed.shape.finalRead.found observed.shape.finalRead.form)

theorem ActualHeader.branching_receipt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.body]
  exact observed.body_shape

def ActualHeader.branching_body {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := row, prepared := actual.prepared, instantiation := CallableNamedMetadata.instantiation row
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .branching receipt }

end Tests.SourceCoreNamedOperators
