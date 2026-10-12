import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree

/-! The actual compiler flow and its native typing produce the original scoped
branch and assignment tree. Only reached expression metadata is transported; allocations
and assignment heads keep their exact emitted Core expressions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedBranchingTree
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates

private theorem statement_identity {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view) :
    GenericLexicalStatements.StatementSourceIdentity source view := by
  refine ⟨metadata.owner, metadata.inputs, metadata.roots, ?_⟩
  intro id
  cases found : source.lookupStatement? id with
  | some node => exact (metadata.symm.statement found).symm
  | none =>
    cases viewed : view.lookupStatement? id with
    | none => rfl
    | some node => have impossible := metadata.statement viewed; rw [found] at impossible; cases impossible

private theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source view : TypedSource}
  {roots : List NodeId} {changed : List ExpressionId}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {initial : SourceSemantics.Context}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Genuine Source syntax and one native body witness suffice for every
expression callback, including the RHS under the seven-slot assignment frame. -/
theorem tree
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.Syntax source expressionSyntax context position expected)
    {mode : Bool} {statements : List StatementId} (atStatements : position = .statements mode statements)
    (shape : Shape source mode statements)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id))
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      (.statements mode statements) expected type code := by
  induction syntaxTree generalizing mode statements scope fuel code nativeType with
  | body body =>
    cases atStatements
    have viewed := CallableLambdaViewSourceTyping.lexical_syntax_with edited avoids unique
      (fun _ _ original => original) body reached
    have extracted := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual _
      readPolicy binderPolicy allocationPolicy
      (certificates := fun context scope id lowered => Dynamic.RuntimeContextFields initial context →
        Reaches source roots (.expression id) → TypedCertificate source certificates context scope id lowered)
      (fun context _ _ _ scope fuel id node lowered declarations syntaxValue found typed generated nativeType typedNative contextFields reachable => by
        have originalFound : source.lookupExpression? id = some node := (expression_lookup edited avoids reachable).trans found
        have originalTyped := CallableLambdaViewStaticTyping.expression_original edited avoids unique typed reachable
        exact ⟨node, originalFound, originalTyped, children context contextFields
          (scope_declarations edited.metadata.symm declarations) syntaxValue reachable originalFound originalTyped generated typedNative⟩)
      viewed closed residual sourceSignatures (scope_declarations edited.metadata declarations) projection accepted nativeTyped
    have discharged := CallableIndexedOwnedPreparedLexicalContextCertificates.Tree.discharge_context extracted fields
    have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
    exact .body body (CallableLambdaViewBodyTree.transport reverse (avoids.view edited.metadata)
      (fun _ _ _ _ accessible value => value (accessible.metadata edited.metadata.symm)) discharged
      (fun id member => (reached id member).metadata edited.metadata))
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.absentRequest view scope binder payload)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.absentRequest view scope binder payload) edited.metadata.symm annotation
      have tail := ih rfl (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .uninitialized found form mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      have tail := ih rfl (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initialized found form mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases atStatements
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨_continuing, restShape⟩ := shape.discard_tail found form notTail
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      obtain ⟨body, generatedBody, sameCode⟩ : ∃ body,
          SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope rest type reasonAt mode selfReason = .ok body ∧
          code = LocalSequence.discard (LocalLoop.controlType type) lowered.expression body := by
        cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
        all_goals
          obtain ⟨checked, _, accepted⟩ := bind_ok accepted
          cases checked
          obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
          exact ⟨body, generatedBody, (Except.ok.inj accepted).symm⟩
      subst code
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      exact .discard found form notTail expressionFound
        ⟨expressionNode, expressionFound, typed, children context fields declarations syntaxValue accessible expressionFound typed generated childTyped⟩
        (ih rfl restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile childSyntax remaining ih =>
    cases atStatements
    obtain ⟨sameOperator, bare, restShape⟩ := shape.assign_tail found form
    cases sameOperator
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope (.occurrence id.occurrence)
          assignment .equal (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root .equal)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        simpa only [SourceCoreLoops.assignValue, assignments.equal] using accepted
      have accessible : Reaches source roots (.expression rhs) :=
        .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
      obtain ⟨rhsSyntax, rhsNode, rhsFound, rhsTyped⟩ := childSyntax rhs (by simp)
      obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot, _layout, generated, _sameType, _profile, codeEq⟩ :=
        CompatibleBareAssignment.of_lower bare compiled
      have rhsNative := CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_present_rhs
        (prepared := prepared) (reference := .var index) (keys := SourceCoreCalls.packArguments [])
        (rhs := value.expression) (next := body) (output := LocalLoop.controlType type) (result := nativeType)
        (operator := .equal) (codeEq ▸ nativeTyped)
      have rhsType : rhsNode.type = assignment.target.type := by
        obtain ⟨actualNode, contains, actualType⟩ := rightTyped.stored_type
        have sameNode := Option.some.inj (rhsFound.symm.trans (lookupExpression?_complete unique contains))
        exact sameNode ▸ actualType
      let originalHead : GenericAssignmentStatements.Head values source context
          (TypedCertificate source certificates context) scope administrative definitions assignment .equal rhs := {
        prepared := prepared
        index := index
        codes := []
        leaf := prepared.route.rootSourceType
        lowered := value
        node := rhsNode
        invalid := invalidOperand (.occurrence id.occurrence) assignment.target.root .equal
        shape := .bare bare _layout
        slot := _slot
        writable := _rootType ▸ writable binder ((rootBinder edited.metadata _).trans _binding)
        found := rhsFound
        right := ⟨rhsNode, rhsFound, rhsTyped, children context fields declarations rhsSyntax accessible rhsFound rhsTyped generated rhsNative⟩
        rightView := by simpa only [rhsType] using _rawView
        rightType := _sameType
        profile := .inl rfl }
      have emittedOriginal : code = originalHead.emit body (LocalLoop.controlType type) := codeEq
      rw [emittedOriginal]
      exact .assign found form originalHead
        (ih rfl restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped)))
  | block found form _ _ _ _ _ | terminalBlock _ found form _ _ _ _ | scopedBlock found form _ _ _ _ =>
    cases atStatements
    exact False.elim (shape.not_block found form)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases atStatements
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have thenReached : ∀ child ∈ thenBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    have elseReached : ∀ child ∈ elseBody.getD [], Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by cases elseBody <;> simp_all [StatementForm.references])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel view scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
          (thenIH rfl leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rfl rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH rfl restShape fields closed residual sourceSignatures declarations
            (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
          (thenIH rfl leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rfl rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH rfl restShape fields closed residual sourceSignatures declarations
            (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    cases atStatements
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have thenReached : ∀ child ∈ thenBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    have elseReached : ∀ child ∈ elseBody, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      exact .terminalIf exactUnique found form conditionFound conditionType
        ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
        (thenIH rfl leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
        (elseIH rfl rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
        thenStops elseStops ((GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix).transport (statement_identity edited.metadata.symm))
  | breaking found form | continuing found form =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | whileLoop found form _ _ _ _ _ _ _ _ | forLoop found form _ _ _ _ _
  | bitNot found form _ _ _ _ _ | matchWith found form _ _ _ _ _ _ _ _ _ _ _ _
  | terminalMatch _ found form _ _ _ _ _ _ _ _ _ _ _ =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard
  | initializerAssign | initializerBitNot => cases atStatements

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
