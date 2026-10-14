import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates
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
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

theorem collected
    (edited : LocalView source view changed) (_avoids : Avoids source roots changed)
    (unique : NodeOccurrencesUnique source)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder view scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked view scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
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
    {faults : FunctionCalls.FaultRep}
    (fields : Dynamic.RuntimeContextFields initial context)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = true)
    (sourceSignatures : context.signatures = values.checked.signatures)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (reached : ∀ id ∈ items.flatMap ForItemForm.references, Reaches source roots id)
    {fuel : Nat} {type : Ty} {code : Expr} {nativeType : Ty} {parentSite : SourceCoreElaboration.ErrorSite}
    (operands : ∀ {assignment operator rhs}, .assignValue assignment operator rhs ∈ items →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator (invalidOperand parentSite assignment.target.root operator))
    (unary : ∀ {assignment}, .assignBitNot assignment ∈ items → assignment.target.type = .word →
      faults (.invalidUnaryOperand .bitNot) (invalidUnary parentSite assignment.target.root))
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel view scope items type reasonAt
      (fun _ => pure (LocalLoop.fallthrough type)) = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source
      (TypedCertificate source certificates) definitions administrative type (TypedForHeader.Fallthrough type)
      context scope items code, ∀ registry, tree.ReachableErrors registry faults := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil =>
    have same : code = LocalLoop.fallthrough type := by cases fuel <;> exact (Except.ok.inj accepted).symm
    exact ⟨.nil same, fun _ => .nil (next := same)⟩
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
      obtain ⟨tail, tailSites⟩ := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind payload declarations declaration extended)
        (fun child member => reached child (by simpa [ForItemForm.references] using member))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      rw [← identical]
      refine ⟨.uninitialized mono extended ordinary (binder_projected (binderPolicy scope binder mono ▸ projected))
        originalAllocation originalAnnotation (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail, ?_⟩
      intro registry
      exact .uninitialized (monomorphic := mono) (extended := extended) (ordinary := ordinary)
        (projected := binder_projected (binderPolicy scope binder mono ▸ projected))
        (allocation := originalAllocation) (annotation := originalAnnotation)
        (same := by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same)
        (remaining := tail) (tailSites registry)
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
      obtain ⟨tail, tailSites⟩ := ih shape.let_tail (fields.trans (.ofBinderExtends extended))
        (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
        (scope_bind lowered.type declarations declaration extended)
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member))
        generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      rw [← identical]
      refine ⟨.initialized mono extended ordinary initializerFound sourceType value originalAllocation originalAnnotation
        (by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same) tail, ?_⟩
      intro registry
      exact .initialized (monomorphic := mono) (extended := extended) (ordinary := ordinary)
        (initializerFound := initializerFound) (sourceType := sourceType) (initial := value)
        (allocation := originalAllocation) (annotation := originalAnnotation)
        (same := by simpa only [originalAllocation, CallableLambdaViewAllocations.allocation] using original.trans same)
        (remaining := tail) (tailSites registry)
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
      obtain ⟨tail, tailSites⟩ := ih shape.discard_tail fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member)) generatedBody tailTyped
      refine ⟨.discard found
        ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩
        tail, ?_⟩
      intro registry
      exact .discard (found := found)
        (value := ⟨expressionNode, found, typed, children context fields declarations syntaxValue accessible found typed generated childTyped⟩)
        (remaining := tail) (tailSites registry)
  | @assign context assignment operator rhs rest sourceTyped writable rightTyped profile childSyntax remaining ih =>
    obtain ⟨_sourceProfile, bare, restShape⟩ := shape.assign_tail
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel view scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root)
          (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      have accessible : Reaches source roots (.expression rhs) := reached _ (by simp [ForItemForm.references])
      obtain ⟨rhsSyntax, rhsNode, rhsFound, rhsTyped⟩ := childSyntax rhs (by simp)
      obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot, _layout, generated, _sameType, _profile, codeEq⟩ :=
        CompatibleBareAssignment.of_lower bare compiled
      have rhsNative := CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_present_rhs
        (prepared := prepared) (reference := .var index) (keys := SourceCoreCalls.packArguments [])
        (rhs := value.expression) (next := body) (output := LocalLoop.controlType type) (result := nativeType)
        (operator := operator) (codeEq ▸ nativeTyped)
      have rhsType : rhsNode.type = assignment.target.type := by
        obtain ⟨actualNode, contains, actualType⟩ := rightTyped.stored_type
        have sameNode := Option.some.inj (rhsFound.symm.trans (lookupExpression?_complete unique contains))
        exact sameNode ▸ actualType
      let originalHead : GenericAssignmentStatements.Head values source context
          (TypedCertificate source certificates context) scope administrative definitions assignment operator rhs := {
        prepared := prepared
        index := index
        codes := []
        leaf := prepared.route.rootSourceType
        lowered := value
        node := rhsNode
        invalid := invalidOperand parentSite assignment.target.root operator
        shape := .bare bare _layout
        slot := _slot
        writable := _rootType ▸ writable binder ((rootBinder edited.metadata _).trans _binding)
        found := rhsFound
        right := ⟨rhsNode, rhsFound, rhsTyped, children context fields declarations rhsSyntax accessible rhsFound rhsTyped generated rhsNative⟩
        rightView := by simpa only [rhsType] using _rawView
        rightType := _sameType
        profile := by rw [_rawView]; exact profile }
      have emittedOriginal : code = originalHead.emit body (LocalLoop.controlType type) := codeEq
      rw [emittedOriginal]
      obtain ⟨tail, tailSites⟩ := ih restShape fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp [ForItemForm.references, member]))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member)) generatedBody
        (TypedImperative.Native.execute_continuation (emittedOriginal ▸ nativeTyped))
      refine ⟨.assign originalHead tail, ?_⟩
      intro registry
      refine .assign (head := originalHead) (remaining := tail) (tailSites registry) ⟨?_, ?_, operands (List.mem_cons_self) _sourceProfile⟩
      · intro root resolved reason token count fault
        have empty : originalHead.prepared.steps = [] := _layout.steps
        rw [empty] at fault
        cases fault
      · exact fun nonempty => False.elim (nonempty _layout.steps)
  | @bitNot context assignment rest writable bare profile remaining ih =>
    obtain ⟨rawWord, _, restShape⟩ := shape.bitNot_tail
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, emitted, token⟩ := CompatibleBitNotStatements.Head.of_lower_with_token
        (fun binder found => writable binder ((rootBinder edited.metadata _).trans found))
        bare profile accepted
      rw [emitted]
      obtain ⟨tail, tailSites⟩ := ih restShape fields closed residual sourceSignatures declarations
        (fun child member => reached child (by simp only [List.flatMap_cons]; exact List.mem_append_right _ member))
        (fun member => operands (List.mem_cons_of_mem _ member))
        (fun member => unary (List.mem_cons_of_mem _ member)) generatedBody
        (TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped))
      refine ⟨.bitNot head tail, fun registry => .bitNot (tailSites registry) ?_⟩
      simpa only [CompatibleBitNotStatements.Head.Errors, token] using unary List.mem_cons_self rawWord

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingHeaderCollectors
