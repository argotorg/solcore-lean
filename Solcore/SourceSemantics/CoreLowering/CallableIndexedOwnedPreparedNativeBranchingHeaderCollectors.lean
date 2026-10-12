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

/-! Actual lowered for-header items retain original Source children, exact
allocations and bare assignment heads at their reached lexical context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedPreparedStagedBranchingTree
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedLexicalContextCertificates


private theorem scope_declarations {source view : TypedSource}
    (metadata : LambdaMetadataViews.MetadataView source view)
    {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declared : CompatibleExpressionReads.ScopeDeclarations source scope context) :
    CompatibleExpressionReads.ScopeDeclarations view scope context := by
  intro binder original index type found root
  exact declared binder original index type found (by simpa only [rootBinder metadata] using root)

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

theorem tree
    (edited : LocalView source view changed) (_avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
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
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (syntaxTree : GenericForHeader.Syntax source expressionSyntax context items)
    (shape : ItemShape items)
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ items.flatMap ForItemForm.references, Reaches source roots id)
    {fuel : Nat} {type : Ty} {code : Expr} {nativeType : Ty} {parentSite : SourceCoreElaboration.ErrorSite}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel view scope items type reasonAt
      (fun _ => pure (LocalLoop.fallthrough type)) = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    GenericForHeader.Tree layouts owner active frame globals onError values source
      (TypedCertificate source certificates) definitions administrative type (TypedForHeader.Fallthrough type)
      context scope items code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil =>
    have same : code = LocalLoop.fallthrough type := by cases fuel <;> exact (Except.ok.inj accepted).symm
    exact .nil same
  | @uninitialized context nextContext binder rest declaration mono extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
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
      have tail := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended)
        (fun child member => reached child (by simpa [ForItemForm.references] using member))
        generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .uninitialized mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @initialized context nextContext binder initializer initializerNode rest declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
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
      have tail := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended)
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      exact .initialized mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail
  | @discard context expression expressionNode rest found typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      have accessible : Reaches source roots (.expression expression) := reached _ (by simp [ForItemForm.references])
      exact .discard found
        ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩
        (ih shape.discard_tail fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simp [ForItemForm.references, member])) generatedBody tailTyped)
  | @assign context assignment operator rhs rest sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨sameOperator, bare, restShape⟩ := shape.assign_tail
    cases sameOperator
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope parentSite
          assignment .equal (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root)
          (invalidOperand parentSite assignment.target.root .equal)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        simpa only [SourceCoreLoops.assignValue, assignments.equal] using accepted
      have accessible : Reaches source roots (.expression rhs) := reached _ (by simp [ForItemForm.references])
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
        invalid := invalidOperand parentSite assignment.target.root .equal
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
      exact .assign originalHead
        (ih restShape fields closed residual sourceSignatures declarations
          (fun child member => reached child (by simp [ForItemForm.references, member])) generatedBody
          (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped)))
  | bitNot => cases shape

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
