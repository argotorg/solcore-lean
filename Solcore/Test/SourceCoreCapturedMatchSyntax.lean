import Solcore.Test.SourceCoreCapturedMatchFixture
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.CompatiblePatternSourceBinders
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedMatch
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
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.localRead.form, observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, List.filter_nil,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.previousOwner, Ne.symm observed.shape.previousDistinct,
    Ne.symm observed.shape.previousArgument, observed.shape.previousScheme, TypeSystem.Scheme.mono,
    observed.shape.previousRequirements, observed.shape.localPrevious]

theorem ObservedFactory.seed_declaration {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    SourceCoreDataPlaces.rootBinder observed.row.function.typedBody observed.shape.binder.id = .ok observed.shape.binder := by
  simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, observed.inputs,
    observed.nodes, observed.shape.initialRead.form, observed.shape.argumentRead.form,
    observed.shape.localRead.form, observed.shape.previousRead.form, observed.shape.initializedForm, observed.shape.assignmentForm,
    observed.shape.matchForm, observed.shape.arms, observed.shape.patternResolution, SourceCoreDataPlaces.patternBinders, List.filter_nil,
    observed.innerReturnForm, observed.lambda, observed.returnStatement,
    observed.shape.binderOwner, observed.shape.previousDistinct,
    observed.shape.argumentDistinct, observed.binderScheme, TypeSystem.Scheme.mono,
    observed.shape.binderRequirements, observed.shape.localSeed]

theorem ObservedFactory.body_shape {fixture : CompiledFixture} (observed : ObservedFactory fixture) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape observed.row.function.typedBody true
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] := by
  apply CallableIndexedOwnedPreparedStagedBranchingTree.Shape.initialized
    observed.shape.initializedFound observed.shape.initializedForm
  apply CallableIndexedOwnedPreparedStagedBranchingTree.Shape.matchWith observed.shape.matchFound observed.shape.matchForm
  · intro arm member
    have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
    subst arm
    rw [observed.shape.armBody]
    exact .assign observed.shape.assignmentFound observed.shape.assignmentForm observed.shape.targetBare .nil
  · intro statements present
    simp [observed.shape.noDefault] at present
  · exact .returnValue [] observed.shape.innerReturnFound observed.shape.innerReturnForm

private theorem binders_functional {owner : Resolved.DeclarationId}
    {context left right : SourceSemantics.Context} {binders : List TypedBinder}
    (first : BindersExtend owner context binders left) (second : BindersExtend owner context binders right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other rest => cases head; cases other; exact ih rest

private theorem requested_body {source : TypedSource} {control : ControlContext}
    {parent child : SourceSemantics.Context} {type : TypeSystem.Ty} {cases : List TypedMatchCase}
    {caseFacts : List BodyFacts} {fallback : Option (List StatementId)} {request : GenericMatchChildren.Request}
    (typed : MatchCasesHaveType source control parent type cases caseFacts)
    (defaultTyped : ∀ statements, fallback = some statements →
      ∃ final facts, StatementsHaveType source control parent statements final facts)
    (selected : GenericMatchChildren.ContextFor source parent type cases fallback request child) :
    ∃ final facts, StatementsHaveType source control child request.statements final facts := by
  cases selected with
  | @arm arm binders arity child member statements patternTyped extended =>
    have caseTyped : ∃ facts, MatchCaseHasType source control parent type arm facts := by
      induction cases generalizing caseFacts with
      | nil => cases member
      | cons head rest ih =>
        cases typed with
        | cons headTyped tail =>
          rcases List.mem_cons.mp member with same | later
          · subst arm; exact ⟨_, headTyped⟩
          · exact ih tail later
    obtain ⟨facts, caseTyped⟩ := caseTyped
    cases caseTyped with
    | intro originalPattern originalExtension body =>
      have bindersEq := (CompatiblePatternSourceBinders.pattern_binders originalPattern).symm.trans
        (CompatiblePatternSourceBinders.pattern_binders patternTyped)
      cases bindersEq
      have same := binders_functional originalExtension extended
      rw [← same, statements]
      exact ⟨_, _, body⟩
  | default present => exact defaultTyped _ present

def ObservedFactory.readIds {fixture : CompiledFixture} (observed : ObservedFactory fixture) : List ExpressionId :=
  [observed.shape.initialRead.node.id, observed.shape.argumentRead.node.id,
    observed.shape.localRead.node.id, observed.shape.previousRead.node.id]

private theorem tail_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word}
      context [observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
  have leaf : ∀ id, id ∈ observed.readIds → approved id := leaves
  obtain ⟨middle, headFacts, tailFacts, first, tail⟩ := head_tail typed
  have firstForm := form_at unique observed.shape.matchFound first
  rw [observed.shape.matchForm] at firstForm
  cases firstForm with
  | matchWithDefault present _ _ _ => simp [observed.shape.noDefault] at present
  | matchWithoutDefault absent scrutineeTyped casesTyped =>
    have scrutineeFound : observed.row.function.typedBody.lookupExpression? observed.shape.matching.scrutinee =
        some observed.shape.argumentRead.node := by rw [observed.shape.scrutinee]; exact observed.shape.argumentRead.found
    obtain ⟨stored, contained, storedType⟩ := scrutineeTyped.stored_type
    have same := Option.some.inj ((lookupExpression?_complete unique contained).symm.trans scrutineeFound)
    subst stored
    have defaults : ∀ statements, observed.shape.matching.defaultBody = some statements →
        ∃ final facts, StatementsHaveType observed.row.function.typedBody {returnType := .word} context statements final facts := by
      intro statements present; simp [observed.shape.noDefault] at present
    apply GenericImperativeMatch.Syntax.matchWith observed.shape.matchFound observed.shape.matchForm
      (.inl observed.shape.matchType) scrutineeFound (storedType ▸ scrutineeTyped)
      (by rw [observed.shape.scrutinee]; exact leaf _ (by simp [ObservedFactory.readIds]))
      (storedType ▸ casesTyped) defaults
    · simp [observed.shape.inputs, Ne.symm observed.shape.hiddenSeed]
    · intro arm member binder binderMember
      have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
      subst arm
      have sameBinder : binder = observed.shape.copyBinder.id := by
        simpa [TypedMatchPattern.binderIds, observed.shape.patternResolution] using binderMember
      subst binder
      simp [observed.shape.inputs, Ne.symm observed.shape.localSeed]
    · intro request child selected
      have original := requested_body (storedType ▸ casesTyped) defaults selected
      have statements : request.statements = [observed.shape.assignment.id] := by
        cases selected with
        | @arm arm _ _ _ member sameBody _ _ =>
          have same : arm = observed.shape.arm := by simpa only [observed.shape.arms, List.mem_singleton] using member
          subst arm
          exact sameBody.trans observed.shape.armBody
        | default present => simp [observed.shape.noDefault] at present
      rw [statements]
      obtain ⟨final, bodyFacts, bodyTyped⟩ := original
      rw [statements] at bodyTyped
      obtain ⟨_, _, _, assignedHead, _⟩ := head_tail bodyTyped
      have assignment := form_at unique observed.shape.assignmentFound assignedHead
      rw [observed.shape.assignmentForm] at assignment
      cases assignment with
      | assignValue assignmentTyped =>
        exact assigned observed.shape.localRead observed.shape.assignmentFound observed.shape.assignmentForm
          (by rw [observed.shape.targetRoot]; exact observed.seed_declaration)
          observed.binderScheme observed.shape.targetBare observed.shape.targetType
          (leaf _ (by simp [ObservedFactory.readIds])) assignmentTyped (.body (.nil (.inl rfl)))
    · obtain ⟨_, _, _, returningHead, _⟩ := head_tail tail
      exact returning unique observed.shape.previousRead observed.shape.innerReturnFound observed.shape.innerReturnForm
        observed.shape.innerReturnType (leaf _ (by simp [ObservedFactory.readIds])) returningHead

theorem ObservedFactory.body_syntax {fixture : CompiledFixture} (observed : ObservedFactory fixture)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique observed.row.function.typedBody) {approved : ExpressionId → Prop}
    (leaves : ∀ id ∈ observed.readIds, approved id)
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word} context
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody approved context
      (.statements true [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
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
    (typed : StatementsHaveType observed.row.function.typedBody {returnType := .word} context
      [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id] final facts) :
    GenericImperativeMatch.Syntax observed.row.function.typedBody
      (CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots.Read observed.row.function.typedBody) context
      (.statements true [observed.shape.initialized.id, observed.shape.matchNode.id, observed.shape.innerReturn.id]) .word := by
  apply observed.body_syntax unique _ typed
  intro id member
  simp only [readIds, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_, _, _, observed.shape.initialRead.found, observed.shape.initialRead.form⟩
  · exact ⟨_, _, _, observed.shape.argumentRead.found, observed.shape.argumentRead.form⟩
  · exact ⟨_, _, _, observed.shape.localRead.found, observed.shape.localRead.form⟩
  · exact ⟨_, _, _, observed.shape.previousRead.found, observed.shape.previousRead.form⟩

end Tests.SourceCoreCapturedMatch
