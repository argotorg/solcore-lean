import Solcore.Test.SourceCoreCapturedForFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLegacyBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
/-! Original typed initialization, loop header, post, and restored return supply
all compiler children for the captured For body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedFor
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

private theorem header_assigned {source : TypedSource} {context : SourceSemantics.Context}
    {binder rhsBinder : TypedBinder} {payload : TypeSystem.Ty}
    {assignment : AssignmentResolution} {approved : ExpressionId → Prop} {rest : List ForItemForm}
    (read : Read source rhsBinder payload)
    (declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder)
    (scheme : binder.scheme = .mono payload) (bare : assignment.target.projections = [])
    (targetType : assignment.target.type = payload) (leaf : approved read.node.id)
    (typed : SourceAssignmentHasType source context assignment .equal read.node.id)
    (remaining : GenericForHeader.Syntax source approved context rest) :
    GenericForHeader.Syntax source approved context (.assignValue assignment .equal read.node.id :: rest) := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal target rhs _requirements =>
      cases target with
      | intro writable projections target =>
          apply GenericForHeader.Syntax.assign
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
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form, observed.shape.headerRead.form,
    observed.shape.conditionRead.form, observed.shape.argumentRead.form, observed.shape.stopRead.form,
    observed.shape.finalRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.loopForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.binderOwner, observed.binderScheme, TypeSystem.Scheme.mono, observed.shape.binderRequirements,
    observed.shape.runningDistinct, observed.shape.argumentDistinct, observed.shape.stopDistinct, observed.shape.previousDistinct, observed.shape.flagDistinct]

theorem ObservedFactory.previous_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.previous.id = .ok observed.shape.previous := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form, observed.shape.headerRead.form,
    observed.shape.conditionRead.form, observed.shape.argumentRead.form, observed.shape.stopRead.form,
    observed.shape.finalRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.loopForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.previousOwner, observed.shape.previousScheme, TypeSystem.Scheme.mono, observed.shape.previousRequirements,
    Ne.symm observed.shape.previousDistinct, Ne.symm observed.shape.previousRunning, Ne.symm observed.shape.previousArgument, Ne.symm observed.shape.previousStop, observed.shape.flagPrevious]

theorem ObservedFactory.flag_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.flag.id = .ok observed.shape.flag := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, FactoryShape.nodeList, observed.shape.initialRead.form, observed.shape.headerRead.form,
    observed.shape.conditionRead.form, observed.shape.argumentRead.form, observed.shape.stopRead.form,
    observed.shape.finalRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.loopForm, observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.flagOwner, observed.shape.flagScheme, TypeSystem.Scheme.mono, observed.shape.flagRequirements,
    Ne.symm observed.shape.flagDistinct, Ne.symm observed.shape.flagRunning, Ne.symm observed.shape.flagArgument, Ne.symm observed.shape.flagStop, Ne.symm observed.shape.flagPrevious]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape observed.row.function.typedBody true observed.shape.body :=
  .initialized observed.shape.initializedFound observed.shape.initializedForm
    (.forLoop observed.shape.loopFound observed.shape.loopForm (.initialized .nil)
      (.assign (.inl rfl) observed.shape.postBare .nil)
      (.assign observed.shape.assignmentFound observed.shape.assignmentForm (.inl rfl) observed.shape.targetBare .nil)
      (.returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm))

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.headerRead.node.id, observed.shape.conditionRead.node.id,
    observed.shape.argumentRead.node.id, observed.shape.stopRead.node.id, observed.shape.finalRead.node.id]
private theorem tail_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.loop.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.loop.id, observed.shape.innerReturn.id]) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.loopFound first
  rw [observed.shape.loopForm] at firstForm
  cases firstForm with
  | forLoop initializerTyped conditionTyped bodyTyped postTyped =>
    apply GenericImperativeMatch.Syntax.forLoop observed.shape.loopFound observed.shape.loopForm observed.shape.loopType
    · cases initializerTyped with
      | cons initial rest =>
        cases rest
        cases initial with
        | letInitialized initializer mono generalized extended =>
          apply GenericImperativeMatch.Syntax.initializerInitialized observed.flag_declaration mono extended
            (by simp [observed.inputs, Ne.symm observed.shape.flagDistinct])
            observed.shape.headerRead.found
            (by rw [observed.shape.headerRead.type, observed.shape.flagScheme]; rfl)
            (by simpa only [observed.shape.headerRead.type, observed.shape.flagScheme, TypeSystem.Scheme.mono] using initializer)
            (leaf _ (by simp [ObservedFactory.readIds]))
          apply GenericImperativeMatch.Syntax.initializersDone observed.shape.conditionRead.found observed.shape.conditionRead.type
            (by simpa only [observed.shape.conditionRead.type] using conditionTyped) (leaf _ (by simp [ObservedFactory.readIds]))
          · obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
            have assignment := form_at unique observed.shape.assignmentFound assignedHead
            rw [observed.shape.assignmentForm] at assignment
            cases assignment with
            | assignValue assignmentTyped =>
              exact assigned observed.shape.argumentRead observed.shape.assignmentFound observed.shape.assignmentForm
                (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
                observed.binderScheme observed.shape.targetBare observed.shape.targetType
                (leaf _ (by simp [ObservedFactory.readIds])) assignmentTyped (.body (.nil (.inl rfl)))
          · cases postTyped with
            | cons post tail =>
              cases post with
              | assignValue assignmentTyped =>
                exact header_assigned observed.shape.stopRead
                  (by rw [observed.shape.postRoot]; exact observed.flag_declaration)
                  observed.shape.flagScheme observed.shape.postBare observed.shape.postType
                  (leaf _ (by simp [ObservedFactory.readIds])) assignmentTyped .nil
        | letInitializedGeneralized polymorphic _ _ _ _ =>
          exact False.elim (polymorphic (by rw [observed.shape.flagScheme]; rfl))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.finalRead observed.shape.innerReturnFound observed.shape.innerReturnForm
        observed.shape.innerReturnType (leaf _ (by simp [ObservedFactory.readIds])) returningHead

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word} context
      [observed.shape.initialized.id, observed.shape.loop.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.initialized.id, observed.shape.loop.id, observed.shape.innerReturn.id]) .word := by
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have declaration := observed.previous_declaration
  have mono : observed.shape.previous.scheme.quantified = [] := by rw [observed.shape.previousScheme]; rfl
  have ordinary : observed.row.function.typedBody.inputs.any
      (fun input => decide (input.id = observed.shape.previous.id)) = false := by
    simp [observed.inputs, Ne.symm observed.shape.previousDistinct]
  cases first with
  | letInitialized contains form initializer _mono _generalized extended _type =>
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
    cases same
    rw [observed.shape.initializedForm] at form
    obtain ⟨sameBinder, sameInitializer⟩ := StatementForm.letDecl.inj form
    cases sameBinder
    cases Option.some.inj sameInitializer
    apply GenericImperativeMatch.Syntax.initialized observed.shape.initializedFound observed.shape.initializedForm
      declaration mono extended ordinary observed.shape.initialRead.found
      (by rw [observed.shape.initialRead.type, observed.shape.previousScheme]; rfl)
      (by simpa only [observed.shape.initialRead.type, observed.shape.previousScheme, TypeSystem.Scheme.mono] using initializer)
      (leaves _ (by simp [ObservedFactory.readIds]))
    exact tail_syntax observed unique leaves tail
  | letInitializedGeneralized contains form polymorphic _requirements _generalizes _initializer _extended _type =>
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.shape.initializedFound)
    cases same
    rw [observed.shape.initializedForm] at form
    obtain ⟨sameBinder, _⟩ := StatementForm.letDecl.inj form
    cases sameBinder
    exact False.elim (polymorphic mono)
  | _ =>
    have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.shape.initializedFound)
    cases same
    simp_all [observed.shape.initializedForm, observed.shape.previousScheme, TypeSystem.Scheme.mono]

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
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.headerRead.found, observed.shape.headerRead.form⟩
  · exact ⟨_, _, _, observed.shape.conditionRead.found, observed.shape.conditionRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.stopRead.found, observed.shape.stopRead.form⟩
  · exact ⟨_, _, _, observed.shape.finalRead.found, observed.shape.finalRead.form⟩

end Tests.SourceCoreCapturedFor
