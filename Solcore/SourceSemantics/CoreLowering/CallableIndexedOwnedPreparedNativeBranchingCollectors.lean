import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentUnaryDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalContextCertificates
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeReceipts
import Solcore.SourceSemantics.CoreLowering.GenericMatchScopedContexts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors

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
open CallableIndexedOwnedPreparedBranchingCatalogSites (Collected)

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

private theorem while_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.whileLoop type condition body reason) result definitions) :
    ∃ conditionType, HasType context condition conditionType definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨_, shifted⟩ := computation_child loop
              exact ⟨_, TypedLexicalWhile.Native.remove_front
                (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem binders_fields {owner : Resolved.DeclarationId}
    {parent child : SourceSemantics.Context} {binders : List TypedBinder}
    (extended : BindersExtend owner parent binders child) :
    Dynamic.RuntimeContextFields parent child := by
  induction extended with
  | nil => exact .refl _
  | cons head _ ih => exact (Dynamic.RuntimeContextFields.ofBinderExtends head).trans ih

/-- Native typing of the actual hidden allocation retains the exact evaluated
scrutinee callback, before any matcher or arm body executes. -/
private theorem match_expression
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {compilation : SourceCoreCompatibleDataMatches.Context}
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} {administrative : Core.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {before after : CompatibleMatchCertificates.ExpressionCertificate}
    {bodyCertificate : CompatibleMatchCertificates.BodyCertificate} {code : Expr}
    (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason before bodyCertificate code)
    {type : Ty} (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions)
    (convert : ∀ lowered, before scope resolution.scrutinee lowered →
      (∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions) → after scope resolution.scrutinee lowered) :
    CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason after bodyCertificate code := by
  cases receipt with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    apply CompatibleMatchCertificates.Certificate.matchWith read allowed form requirements hiddenOwned hiddenFresh
      scrutineeOwned found projection _ sameType arms fallback branches hiddenCompiled
    have native := hiddenCompiled
    rw [allocator] at native
    unfold SourceCoreSourceCells.letInitialized at native
    obtain ⟨allocation, allocated, exactCode⟩ := bind_ok native
    cases exactCode
    cases typed with
    | caseE initial failure next => exact convert _ expression ⟨_, initial⟩

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
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Every callback is reached from the original body. Header references include
all remaining initializers, the actual test, the post items and the loop body. -/
def PositionReaches (source : TypedSource) (roots : List NodeId) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => ∀ id ∈ statements, Reaches source roots (.statement id)
  | .initializers items condition post statements =>
      ∀ id ∈ items.flatMap ForItemForm.references ++ [.expression condition] ++
        post.flatMap ForItemForm.references ++ statements.map NodeId.statement,
        Reaches source roots id

/-- The for-header continuation is recovered from the actual outer compiler
call. Its condition, post and body equations are retained together. -/
def CompilerAccepted (policy : SourceCoreLoops.Policy) (fuel : Nat) (original source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (position : GenericImperativeMatch.Position)
    (type : Ty) (reasonAt : ExpressionId → Word) (selfReason : Word) (code : Expr) : Prop :=
  match position with
  | .statements mode statements =>
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code
  | .initializers items condition post statements =>
      ∃ headerFuel parentSite next,
        AssignmentDiagnosticOrigins.ForOrigin original parentSite items condition post statements ∧
        SourceCoreLoops.lowerForItems policy parentSite headerFuel source scope items type reasonAt next = .ok code ∧
        ∀ loopScope nextCode, next loopScope = .ok nextCode →
          ∃ conditionCode loopCode postCode,
            policy.lowerExpression fuel source loopScope condition reasonAt = .ok conditionCode ∧
            conditionCode.type = .bool ∧
            SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source loopScope statements type reasonAt false selfReason = .ok loopCode ∧
            SourceCoreLoops.lowerForItems policy parentSite fuel source loopScope post type reasonAt
              (fun _ => pure (LocalLoop.fallthrough type)) = .ok postCode ∧
            nextCode = LocalLoop.iterate type conditionCode.expression loopCode postCode selfReason

private theorem iterate_condition {definitions : DataEnvironment} {context : Core.Context}
    {type result : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason) result definitions) :
    ∃ conditionType, HasType context condition conditionType definitions := by
  cases typed with
  | letE allocation installed =>
    cases allocation with
    | newCell empty =>
      cases installed with
      | letE written invoked =>
        cases written with
        | storeCell reference closure =>
          cases closure with
          | inRight unitWF raw =>
            cases raw with
            | lambda parameterWF resultWF loop =>
              obtain ⟨_, shifted⟩ := computation_child loop
              exact ⟨_, TypedLexicalWhile.Native.remove_front
                (TypedLexicalWhile.Native.remove_front shifted)⟩

private theorem header_operand {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {items : List ForItemForm} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.HeaderOrigin source site items)
    (member : .assignValue assignment operator rhs ∈ items) :
    AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs := by
  rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩ |
    ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩
  · exact .header found form (List.mem_append_left _ (List.mem_append_right _ member))
  · exact .header found form (List.mem_append_right _ (List.mem_append_right _ member))

private theorem header_unary {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {items : List ForItemForm} {assignment : AssignmentResolution}
    (origin : AssignmentDiagnosticOrigins.HeaderOrigin source site items)
    (member : .assignBitNot assignment ∈ items) :
    GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment := by
  rcases origin with ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩ |
    ⟨id, node, initializer, condition, post, body, found, form, rfl, beforeItems, rfl⟩
  · exact .header found form (List.mem_append_left _ (List.mem_append_right _ member))
  · exact .header found form (List.mem_append_right _ (List.mem_append_right _ member))

theorem collected_at
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root))
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (ledger : initial.solvedRequirements = matchCompilation.solvedRequirements)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax source expressionSyntax context position expected)
    (shape : PositionShape source position)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : PositionReaches source roots position)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : CompilerAccepted policy fuel source view scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      position expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | body body =>
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
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
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
      have tail := ih (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .uninitialized found form mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
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
      have tail := ih (shape.tail_of_let found form) (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended) (fun child member => reached child (List.mem_cons_of_mem id member))
        projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initialized found form mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
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
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sourceProfile, restShape⟩ := shape.assignment_tail found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        have edge : .expression child ∈ assignment.references ++ [.expression rhs] := by
          rcases List.mem_cons.mp member with equal | member
          · subst child; simp
          · exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member)
        exact .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using edge)
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child (List.mem_cons_of_mem _ member)))).trans compiled
      obtain ⟨originalHead, emittedOriginal, sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emittedOriginal]
      exact .assignPrepared found form originalHead
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))) (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site (.statement found form) sourceSignatures preparedAt
            (sameToken.symm ▸ operands (.statement found form) sourceProfile) registry)
  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH
  | @scopedBlock context mode id node statements rest expected found form inner remaining innerIH restIH =>
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    have innerReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form
        (innerIH innerShape fields closed residual sourceSignatures declarations innerReached projection generatedInner innerTyped)
        (restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    have innerReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .terminalBlock exactUnique found form
        (innerIH innerShape fields closed residual sourceSignatures declarations innerReached projection generatedInner innerTyped)
        stops ((GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix).transport (statement_identity edited.metadata.symm))
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
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
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
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
          (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH restShape fields closed residual sourceSignatures declarations
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
          (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
          (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
          (restIH restShape fields closed residual sourceSignatures declarations
            (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
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
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
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
        (thenIH leftShape fields closed residual sourceSignatures declarations thenReached projection generatedThen thenTyped)
        (elseIH rightShape fields closed residual sourceSignatures declarations elseReached projection generatedElse elseTyped)
        thenStops elseStops ((GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix).transport (statement_identity edited.metadata.symm))
  | breaking found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .breaking found form
  | continuing found form =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .continuing found form
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    obtain ⟨loopShape, restShape⟩ := shape.loop found form
    have conditionReached : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    have loopReached : ∀ child ∈ statements, Reaches source roots (.statement child) := by
      intro child member
      exact .statement (reached id (by simp)) found (by simp [form, StatementForm.references, member])
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, conditionTyped⟩ := while_condition loopTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      exact .whileLoop found form conditionFound conditionType
        ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax conditionReached conditionFound typed generatedCondition conditionTyped⟩
        (loopIH loopShape fields closed residual sourceSignatures declarations loopReached projection generatedLoop loopBodyTyped)
        loopTyped
        (restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped)
  | @matchWith context mode id node resolution scrutineeNode rest expected control caseFacts
      found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary childrenSyntax remaining childIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, rawReceipt, _, generatedChildren⟩ := CompatibleMatchNativeReceipts.finite_typed_of_lower
        onError matchAllocator matchDefinitions
        (expressionCertificate := fun scope id lowered => ∃ childFuel,
          policy.lowerExpression childFuel view scope id reasonAt = .ok lowered)
        (fun childFuel lowered generated => ⟨childFuel, generated⟩) generatedMatch matchedTyped
      have refs : ∀ child ∈ resolution.references, Reaches source roots child :=
        fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
      have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
      have certified := match_expression onError matchAllocator rawReceipt matchedTyped
        (after := TypedCertificate source certificates context)
        (fun lowered generated native => by
          obtain ⟨childFuel, generated⟩ := generated
          obtain ⟨nativeType, native⟩ := native
          exact ⟨scrutineeNode, scrutineeFound, scrutineeTyped, children context fields declarations
            scrutineeSyntax scrutineeReached scrutineeFound scrutineeTyped generated native⟩)
      have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
      have receipt := CallableLambdaViewMatchRuntimeCertificates.match_certificate reverse
        (avoids.view edited.metadata) matchAllocator (fun _ _ _ _ value => value) certified
        (scrutineeReached.metadata edited.metadata)
      apply Collected.matchWith found form scrutineeFound scrutineeTyped casesTyped defaultTyped
        matchCompilation matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary)
      · intro request member childContext related
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations := related.source_declarations found form (hidden found form) declarations
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := related.closed_fields
        have childFields : Dynamic.RuntimeContextFields context childContext := by
          cases related with
          | arm _ _ _ extended _ => exact binders_fields extended
          | default _ _ => exact .refl _
        apply childIH request childContext related.forget (shape.match_request found form related.forget)
          (fields.trans childFields) (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations
        · intro statement present
          apply refs
          cases related with
          | arm armMember sameBody _ _ _ =>
            simp only [MatchResolution.references, List.mem_cons, reduceCtorEq, List.mem_append]
            exact .inl (.inr (List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩))
          | default sameBody _ =>
            simp [MatchResolution.references, sameBody, present]
        · exact projection
        · exact generated
        · exact childTyped
      · exact restIH (shape.match_children found form).2.2 fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped
      · exact catalog
      · exact ⟨by simpa only [SourceCoreCompatibleDataMatches.Context.signatures, SourceCoreCompatibleDataMatches.Context.checked, matchValues] using sourceSignatures,
          fields.solvedRequirements.trans ledger⟩
  | @terminalMatch context mode id node resolution scrutineeNode rest expected control caseFacts
      exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary childrenSyntax stops childIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      have ⟨lower, selected⟩ : ∃ lower, policy.lowerMatch = some lower := by
        cases selected : policy.lowerMatch with
        | none => simp [selected] at accepted
        | some lower => exact ⟨lower, rfl⟩
      simp only [selected] at accepted
      obtain ⟨matched, generatedMatch, accepted⟩ := bind_ok accepted
      have generatedMatch := matchPolicy selected generatedMatch
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨requests, rawReceipt, _, generatedChildren⟩ := CompatibleMatchNativeReceipts.finite_typed_of_lower
        onError matchAllocator matchDefinitions
        (expressionCertificate := fun scope id lowered => ∃ childFuel,
          policy.lowerExpression childFuel view scope id reasonAt = .ok lowered)
        (fun childFuel lowered generated => ⟨childFuel, generated⟩) generatedMatch matchedTyped
      have refs : ∀ child ∈ resolution.references, Reaches source roots child :=
        fun child member => .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
      have scrutineeReached : Reaches source roots (.expression resolution.scrutinee) := refs _ (by simp [MatchResolution.references])
      have certified := match_expression onError matchAllocator rawReceipt matchedTyped
        (after := TypedCertificate source certificates context)
        (fun lowered generated native => by
          obtain ⟨childFuel, generated⟩ := generated
          obtain ⟨nativeType, native⟩ := native
          exact ⟨scrutineeNode, scrutineeFound, scrutineeTyped, children context fields declarations
            scrutineeSyntax scrutineeReached scrutineeFound scrutineeTyped generated native⟩)
      have reverse : LocalView view source changed := ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
      have receipt := CallableLambdaViewMatchRuntimeCertificates.match_certificate reverse
        (avoids.view edited.metadata) matchAllocator (fun _ _ _ _ value => value) certified
        (scrutineeReached.metadata edited.metadata)
      apply Collected.terminalMatch exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped
        matchCompilation matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary)
      · intro request member childContext related
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations := related.source_declarations found form (hidden found form) declarations
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := related.closed_fields
        have childFields : Dynamic.RuntimeContextFields context childContext := by
          cases related with
          | arm _ _ _ extended _ => exact binders_fields extended
          | default _ _ => exact .refl _
        apply childIH request childContext related.forget (shape.match_request found form related.forget)
          (fields.trans childFields) (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations
        · intro statement present
          apply refs
          cases related with
          | arm armMember sameBody _ _ _ =>
            simp only [MatchResolution.references, List.mem_cons, reduceCtorEq, List.mem_append]
            exact .inl (.inr (List.mem_flatMap.mpr ⟨_, armMember, List.mem_map.mpr ⟨statement, sameBody ▸ present, rfl⟩⟩))
          | default sameBody _ =>
            simp [MatchResolution.references, sameBody, present]
        · exact projection
        · exact generated
        · exact childTyped
      · exact stops
      · exact (GenericLexicalStatements.IssuedSuffix.of_accepted generatedBody).transport
          (statement_identity edited.metadata.symm)
      · exact catalog
      · exact ⟨by simpa only [SourceCoreCompatibleDataMatches.Context.signatures, SourceCoreCompatibleDataMatches.Context.checked, matchValues] using sourceSignatures,
          fields.solvedRequirements.trans ledger⟩
  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.bitNot_tail found form bare
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder binding => writable binder ((rootBinder edited.metadata _).trans binding))
        bare profile accepted
      rw [emitted]
      exact .bitNot found form head
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (by simpa only [CompatibleBitNotStatements.Head.Errors, token] using unary (.statement found form) rawWord)
  | @bitNotProjected context mode id node assignment rest expected found form sourceTyped writable projected profile childSyntax remaining ih =>
    obtain ⟨_rawWord, restShape⟩ := shape.unary_tail found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, generatedBody, compiled⟩ := bind_ok accepted
      have accessible : ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        exact .statement (reached id List.mem_cons_self) found
          (by simpa only [form, StatementForm.references, AssignmentResolution.references,
            PlaceResolution.references] using CallableLambdaViewPlaceLowering.key_reference member)
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := fuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child member))).trans compiled
      obtain ⟨head, emitted, _sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable projected profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, childNode, childFound, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨childNode, childFound, childNode, childFound, typed,
              children context fields declarations approved (accessible child member) childFound typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emitted]
      exact .bitNotProjected found form head
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody
          (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (.projected (.statement found form) sourceSignatures projected preparedAt)
  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initialSyntax remaining initialIH restIH =>
    obtain ⟨initialShape, postShape, bodyShape, restShape⟩ := shape.for_children found form
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [CompilerAccepted, SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans (edited.metadata.symm.statement found))
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      apply Collected.forLoop found form
      · apply initialIH ⟨initialShape, postShape, bodyShape⟩ fields closed residual sourceSignatures declarations
        · intro child member
          exact .statement (reached id (by simp)) found (by simpa only [form, StatementForm.references] using member)
        · exact projection
        · refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start (tracked := true) found form, generatedInitial, ?_⟩
          intro loopScope nextCode generated
          obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
          obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
          cases checked
          obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
          obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
          cases generated
          exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (ensure_same conditionChecked).symm,
            loopGenerated, postGenerated, rfl⟩
        · exact initialTyped
      · exact restIH restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (List.mem_cons_of_mem id member)) projection generatedBody tailTyped
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    obtain ⟨_, conditionNative⟩ := iterate_condition loopTyped
    have accessible : Reaches source roots (.expression condition) := reached _ (by simp)
    obtain ⟨postTree, postSites⟩ := CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors.collected
      edited avoids unique binderPolicy allocationPolicy assignments unaryPolicy children postSyntax shape.2.1
      fields closed residual sourceSignatures declarations
      (fun child member => reached _ (by simp [member]))
      (fun member profile => operands (header_operand
        (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member) profile)
      (fun member rawWord => unary (header_unary
        (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member) rawWord)
      (fun member => header_operand (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member)
      (fun member => header_unary (AssignmentDiagnosticOrigins.ForOriginFor.post_origin (tracked := true) origin) member)
      postGenerated postTyped
    refine Collected.initializersDone conditionFound conditionType
      ⟨conditionNode, conditionFound, typed, children context fields declarations conditionSyntax accessible conditionFound typed conditionGenerated conditionNative⟩
      ?_ postTree postSites loopTyped
    exact loopIH shape.2.2 fields closed residual sourceSignatures declarations
      (fun child member => reached _ (by simp [member])) projection loopGenerated bodyTyped
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration mono extended ordinary remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
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
      have tail := ih ⟨shape.1.let_tail, shape.2⟩ (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended)
        (fun child member => reached child (by simpa [ForItemForm.references] using member))
        projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initializerUninitialized mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initializerInitialized context nextContext binder initializer initializerNode rest condition post statements expected declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have accessible : Reaches source roots (.expression initializer) := reached _ (by simp [ForItemForm.references])
      have value : TypedCertificate source certificates context scope initializer lowered :=
        ⟨initializerNode, initializerFound, typed, children context fields declarations initializerSyntax accessible initializerFound typed generated childTyped⟩
      let originalAllocation := CallableLambdaViewAllocations.allocation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type)
        (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata.symm) allocation
      obtain ⟨originalAnnotation, original, identical⟩ := CallableLambdaViewAllocations.annotation
        (request := TypedLexicalWhile.initializedRequest view scope binder lowered.type) edited.metadata.symm annotation
      have tail := ih ⟨shape.1.let_tail, shape.2⟩ (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended)
        (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member)))
        projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initializerInitialized mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxValue remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
      exact .initializerDiscard found
        ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩
        (ih ⟨shape.1.discard_tail, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member))) projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩ tailTyped)
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sourceProfile, restShape⟩ := shape.1.assignment_tail
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression headerFuel view scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root)
          (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : ∀ child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        have edge : .expression child ∈ assignment.references ++ [.expression rhs] := by
          rcases List.mem_cons.mp member with equal | member
          · subst child; simp
          · exact List.mem_append_left _ (CallableLambdaViewPlaceLowering.key_reference member)
        exact reached _ (by simp only [List.flatMap_cons, ForItemForm.references, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (List.mem_append.mp edge)))))
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := headerFuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child (List.mem_cons_of_mem _ member)))).trans compiled
      obtain ⟨originalHead, emittedOriginal, sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable rightTyped profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, node, found, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨node, found, node, found, typed,
              children context fields declarations approved (accessible child member) found typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emittedOriginal]
      exact .initializerAssignPrepared originalHead
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using (List.mem_append_right (ForItemForm.references _) member))) projection ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin, generatedBody, nextReceipt⟩
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))) (fun registry => CallableIndexedOwnedPreparedBranchingCatalogSites.assignment_site
            (AssignmentDiagnosticOrigins.HeaderOriginFor.operand (tracked := true) (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceSignatures preparedAt
            (sameToken.symm ▸ operands (AssignmentDiagnosticOrigins.HeaderOriginFor.operand (tracked := true) (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceProfile) registry)
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.1.bitNot_tail bare
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder binding => writable binder ((rootBinder edited.metadata _).trans binding))
        bare profile accepted
      rw [emitted]
      exact .initializerBitNot head
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using
            (List.mem_append_right (ForItemForm.references _) member))) projection
          ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin,
            generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (by simpa only [CompatibleBitNotStatements.Head.Errors, token] using (unary
          (AssignmentDiagnosticOrigins.HeaderOriginFor.unary (tracked := true)
            (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) rawWord))

  | @initializerBitNotProjected context assignment rest condition post statements expected sourceTyped writable projected profile childSyntax remaining ih =>
    obtain ⟨_rawWord, restShape⟩ := shape.1.unary_tail
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, compiled⟩ := bind_ok accepted
      have accessible : ∀ child ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
          Reaches source roots (.expression child) := by
        intro child member
        apply reached
        simp only [List.flatMap_cons, ForItemForm.references, AssignmentResolution.references,
          PlaceResolution.references, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (CallableLambdaViewPlaceLowering.key_reference member))))
      have compiledOriginal := (CallableLambdaViewPlaceLowering.lower
        (expression := policy.lowerExpression) (fuel := headerFuel) edited.metadata
        (fun child member => expression_lookup edited avoids (accessible child member))).trans compiled
      obtain ⟨head, emitted, _sameToken, preparedAt⟩ :=
        CallableIndexedOwnedPreparedNativeProjectedBitNotHeadCollectors.Head.of_lower_with_raw_occurrences
          unique sourceSignatures sourceTyped writable projected profile
          (certificate := TypedCertificate source certificates context)
          (fun child lowered member generated raw => by
            obtain ⟨approved, childNode, childFound, typed⟩ := childSyntax child member
            obtain ⟨_, native⟩ := raw
            exact ⟨childNode, childFound, childNode, childFound, typed,
              children context fields declarations approved (accessible child member) childFound typed generated native⟩)
          compiledOriginal nativeTyped
      rw [emitted]
      exact .initializerBitNotProjected head
        (ih ⟨restShape, shape.2⟩ fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simpa only [List.flatMap_cons, List.append_assoc] using
            (List.mem_append_right (ForItemForm.references _) member))) projection
          ⟨headerFuel, parentSite, next, AssignmentDiagnosticOrigins.ForOriginFor.tail (tracked := true) origin,
            generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)))
        (.projected (AssignmentDiagnosticOrigins.HeaderOriginFor.unary (tracked := true)
          (AssignmentDiagnosticOrigins.ForOriginFor.header (tracked := true) origin)) sourceSignatures projected preparedAt)


theorem collected
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    {faults : FunctionCalls.FaultRep}
    (operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand site assignment.target.root operator))
    (unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot) (invalidUnary site assignment.target.root))
    {matchCompilation : SourceCoreCompatibleDataMatches.Context}
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (hidden : GenericImperativeMatch.MatchHiddenFresh source)
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (ledger : initial.solvedRequirements = matchCompilation.solvedRequirements)
    (children : ∀ context, Dynamic.RuntimeContextFields initial context →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope context →
      expressionSyntax id → Reaches source roots (.expression id) →
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      policy.lowerExpression fuel view scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates context scope id lowered)
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (syntaxTree : GenericImperativeMatch.PreparedSyntax source expressionSyntax context position expected)
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
    Collected invalidProjection missingDefault (faults := faults) layouts owner active frame globals onError values source expressionSyntax
      (TypedCertificate source certificates) definitions administrative context scope
      (.statements mode statements) expected type code := by
  cases atStatements
  exact collected_at edited avoids unique readPolicy binderPolicy allocationPolicy assignments unaryPolicy operands unary
    matchPolicy matchValues matchDefinitions matchAllocator hidden catalog ledger children
    syntaxTree shape fields closed residual sourceSignatures declarations reached projection accepted nativeTyped

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
