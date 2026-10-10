import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeMatchCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors

/-! One actual imperative compiler induction retains independent actual and fixed
native typings at identical scope/Source/output indices. Original catalog and
diagnostic extraction remains indexed by the actual administrative context.
The additional witness is obtained by constructor inversion of the fixed
whole-code typing, including assignments, loops, match bodies and for-posts.
No child context rebase or semantic execution law is supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeImperativeCollectors
open Core Frontend SourceInference GenericImperativeMatch
open TypedImperativeFor (Accepted InitialAccepted)
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative fixedAdministrative : Core.Context}

variable {matchCompilation : SourceCoreCompatibleDataMatches.Context}

private theorem unary_read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
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

private theorem unary_ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
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

private theorem iterate_condition {definitions : DataEnvironment} {context : Core.Context}
    {type : Ty} {condition body post : Expr} {reason : Word}
    (typed : HasType context (LocalLoop.iterate type condition body post reason)
      (LocalLoop.resultType type) definitions) :
    HasType context condition (LanguageResult.resultType .bool) definitions := by
  have installed := TypedImperativeFor.Native.installed_body typed
  have conditionTyped := (TypedLexicalWhile.Native.conditional_inv installed).1
  exact TypedLexicalWhile.Native.remove_front (TypedLexicalWhile.Native.remove_front conditionTyped)

variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

open DataPatternValues DataPlaceCertificates CompatibleMixedRoute CompatiblePlaceCompilerCertificates

private theorem fixed_assignment_occurrence
    {values : ValuesContext} {source : TypedSource} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {next code : Expr} {output result : Ty} {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (accepted : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site assignment operator (some rhs)
      output next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (member : id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections)
    (compiled : expression fuel source scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedNativeAssignmentChildren.RawTyped
      (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression definitions := by
  by_cases bare : assignment.target.projections = []
  · obtain ⟨binder, prepared, index, value, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
    have identifier : id = rhs := by simpa only [bare, DataPlaceKeyOrder.sourceKeys, List.mem_singleton] using member
    subst id
    have same : lowered = value := Except.ok.inj (compiled.symm.trans generated)
    subst lowered
    exact ⟨_, CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_present_rhs
      (prepared := prepared) (reference := .var index) (keys := SourceCoreCalls.packArguments [])
      (rhs := value.expression) (next := next) (output := output) (operator := operator) (codeEq ▸ typed)⟩
  · cases generated_of_lower accepted with
    | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
      cases rhsGenerated with
      | @present actualId right rightGenerated rhsType =>
        obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
        obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
        rcases List.mem_cons.mp member with sameId | keyMember
        · subst id
          have same : lowered = right := Except.ok.inj (compiled.symm.trans rightGenerated)
          subst lowered
          exact ⟨_, CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_present_rhs
            (prepared := prepared) (reference := .var index) (keys := SourceCoreCalls.packArguments codes)
            (rhs := right.expression) (next := next) (output := output) (operator := operator)
            (by simpa only [routeEq, Option.isNone_some] using typed)⟩
        · obtain ⟨_, ⟨packedType, packedTyped⟩⟩ :=
            CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_children typed
          have locate : ∀ {keys codes}, ListRel (KeyGenerated expression fuel source scope reasonAt) keys codes →
              ∀ id, id ∈ keys.map Prod.fst → ∀ lowered,
              expression fuel source scope id reasonAt = .ok lowered → lowered ∈ codes := by
            intro keys codes generated
            induction generated with
            | nil => intro id member; cases member
            | @cons key keys code codes head tail ih =>
              intro id member lowered compiled
              rcases List.mem_cons.mp member with same | rest
              · subst id
                have identical : lowered = code := Except.ok.inj (compiled.symm.trans head.1)
                exact identical ▸ List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih id rest lowered compiled)
          have generatedMember := locate generated id
            (by simpa only [PreparedPath.key_ids path] using keyMember) lowered compiled
          exact CallableIndexedOwnedPreparedNativeAssignmentChildren.packed_children packedTyped lowered generatedMember

section ForHeader
open GenericForHeader
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : GenericForHeader.ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative fixedAdministrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → GenericForHeader.Scope → Expr → Prop}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Native typing is manufactured at the actual initialized/discard child.
Assignment factories remain separate until their original wrappers are inverted. -/
private theorem paired_for_header (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions →
      HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
        lowered.expression fixedNativeType definitions → certificates sourceContext scope id lowered)

    {next : GenericForHeader.Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = residualMode →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : GenericForHeader.Scope} {items : List ForItemForm}
    (syntaxTree : GenericForHeader.Syntax source expressionSyntax context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType fixedNativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) code fixedNativeType definitions)
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor tracked source parentSite items) :
    Nonempty (CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
      context scope items code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType fixedNativeType with
  | nil => exact ⟨CoupledTokenDiagnosticExtraction.nil (factory := factory) (nextCertificate _ scope code closed residual sourceSignatures declarations (by cases fuel <;> exact accepted))⟩

  | @uninitialized context nextContext binder rest declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CoupledTokenDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.absent_child allocation annotation same fixedTyped) origin.tail))⟩

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
      have sameType := unary_ensure_same checkedType
      subst payload
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      obtain ⟨fixedChildType, fixedInitializerTyped⟩ := computation_child fixedTyped
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped fixedInitializerTyped
      exact ⟨CoupledTokenDiagnosticExtraction.initialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.initialized_child allocation annotation same fixedTyped) origin.tail))⟩

  | @discard context expression expressionNode rest found typed syntaxTree remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
      obtain ⟨fixedChildType, fixedDiscardedTyped⟩ := computation_child fixedTyped
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped fixedDiscardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      obtain ⟨_, fixedBodyTyped⟩ := TypedLexicalWhile.Native.discard_child fixedTyped
      exact ⟨CoupledTokenDiagnosticExtraction.discard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations generatedBody bodyTyped fixedBodyTyped origin.tail))⟩

  | @assign context assignment operator rhs rest sourceTyped writable rightTyped profile children remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel source scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root) (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          obtain ⟨fixedChildType, fixedChildNative⟩ := fixed_assignment_occurrence compiled fixedTyped member generated
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative fixedChildNative⟩) compiled nativeTyped
      exact ⟨CoupledTokenDiagnosticExtraction.assign (factory := factory) head parentSite origin.operand sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations generatedBody (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped) origin.tail))⟩

  | @bitNot context assignment rest writable bare profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨CoupledTokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin) sameToken (Classical.choice (ih closed residual sourceSignatures declarations generatedBody
        (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped) origin.tail))⟩

end ForHeader

/-- Actual compiler acceptance and one enclosing native typing traverse the
same position. Every actual expression callback receives its literal raw
witness, including the original ordered assignment keys and present RHS. -/
theorem extraction_of_typed_position_with_catalog_coupled (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation)
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions →
      HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
        lowered.expression fixedNativeType definitions → certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)

    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType fixedNativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor tracked policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) code fixedNativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
      context scope position expected type code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType fixedNativeType with
  | body syntaxTree => exact ⟨CatalogCoupledExtractionFor.body (factory := factory) syntaxTree (CallableIndexedOwnedPreparedPairedNativeLexicalCollectors.tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped fixedTyped)⟩
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CatalogCoupledExtractionFor.uninitialized (factory := factory) found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.absent_child allocation annotation same fixedTyped)))⟩

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      obtain ⟨fixedChildType, fixedInitializerTyped⟩ := computation_child fixedTyped
      exact ⟨CatalogCoupledExtractionFor.initialized (factory := factory) found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped fixedInitializerTyped)
        allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.initialized_child allocation annotation same fixedTyped)))⟩

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        obtain ⟨_, fixedTailTyped⟩ := TypedLexicalWhile.Native.discard_child fixedTyped
        obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
        obtain ⟨fixedChildType, fixedDiscardedTyped⟩ := computation_child fixedTyped
        exact ⟨CatalogCoupledExtractionFor.discard (factory := factory) found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated discardedTyped fixedDiscardedTyped)
          (Classical.choice (ih closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped))⟩

  | @block context mode id node statements rest expected found form _ inner remaining innerIH restIH
  | @scopedBlock context mode id node statements rest expected found form inner remaining innerIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedHeadTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      exact ⟨CatalogCoupledExtractionFor.block (factory := factory) found form (Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped fixedHeadTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped))⟩
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, fixedBranchTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        obtain ⟨fixedConditionNativeType, fixedConditionNative⟩ := computation_child fixedBranchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative fixedConditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped))⟩
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, fixedBranchTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        obtain ⟨fixedConditionNativeType, fixedConditionNative⟩ := computation_child fixedBranchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative fixedConditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped))⟩

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, headTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedHeadTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      let child := Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped fixedHeadTyped)
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      exact ⟨CatalogCoupledExtractionFor.terminalBlock (factory := factory) exactUnique found form child stops issued⟩

  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedBranchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
      obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
      obtain ⟨fixedConditionNativeType, fixedConditionNative⟩ := computation_child fixedBranchTyped
      let left := Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped)
      let right := Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped)
      let conditionTree := expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative fixedConditionNative
      let issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedSuffix
      exact ⟨CatalogCoupledExtractionFor.terminalIf (factory := factory) exactUnique found form conditionFound conditionType conditionTree left right thenStops elseStops issued⟩

  | @breaking context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨CatalogCoupledExtractionFor.breaking (factory := factory) found form⟩
  | @continuing context mode id node rest expected found form =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact ⟨CatalogCoupledExtractionFor.continuing (factory := factory) found form⟩
  | @whileLoop context mode id node condition conditionNode statements rest expected found form conditionFound conditionType typed conditionSyntax loopSyntax remaining loopIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := unary_ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨loopCode, generatedLoop, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, loopTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedLoopTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      obtain ⟨⟨_, fixedLoopBodyTyped⟩, fixedLoopTyped⟩ := TypedLexicalWhile.Native.while_body fixedLoopTyped
      have conditionNative := iterate_condition loopTyped
      have fixedConditionNative := iterate_condition fixedLoopTyped
      exact ⟨CatalogCoupledExtractionFor.whileLoop (factory := factory) found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative fixedConditionNative)
        (Classical.choice (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped fixedLoopBodyTyped))
        loopTyped
        (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped))⟩

  | @assign context mode id node assignment operator rhs rest expected found form sourceTyped writable rightTyped profile children remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression fuel source scope (.occurrence id.occurrence)
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection (.occurrence id.occurrence) assignment.target.root)
          (invalidOperand (.occurrence id.occurrence) assignment.target.root operator)
          (missingDefault (.occurrence id.occurrence) assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          obtain ⟨fixedChildType, fixedChildNative⟩ := fixed_assignment_occurrence compiled fixedTyped member generated
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative fixedChildNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.assign (factory := factory) found form head (.occurrence id.occurrence) (AssignmentDiagnosticOrigins.OccursFor.statement found form) sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped)))⟩

  | @forLoop context mode id node initializer condition post statements rest expected found form sourceType initial remaining initialIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨initialCode, generatedInitial, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, initialTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedInitialTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      refine ⟨CatalogCoupledExtractionFor.forLoop (factory := factory) found form ?_ ?_⟩
      · apply Classical.choice
        apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped) (fixedTyped := fixedInitialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start found form, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (unary_ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    obtain ⟨⟨_, fixedBodyTyped⟩, ⟨_, fixedPostTyped⟩, fixedLoopTyped⟩ := TypedImperativeFor.Native.iterate_children fixedTyped
    have conditionNative := iterate_condition loopTyped
    have fixedConditionNative := iterate_condition fixedLoopTyped
    exact ⟨CatalogCoupledExtractionFor.initializersDone (factory := factory) conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated conditionNative fixedConditionNative)
      (Classical.choice (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped fixedBodyTyped))
      (Classical.choice (paired_for_header residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped fixedPostTyped origin.post_origin))
      loopTyped⟩
  | @initializerUninitialized context nextContext binder rest condition post statements expected declaration monomorphic extended ordinary remaining ih =>
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
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact ⟨CatalogCoupledExtractionFor.initializerUninitialized (factory := factory) monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.absent_child allocation annotation same fixedTyped)))⟩
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
      have sameType := unary_ensure_same checkedType
      subst payload
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨childType, initializerTyped⟩ := computation_child nativeTyped
      obtain ⟨fixedChildType, fixedInitializerTyped⟩ := computation_child fixedTyped
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped fixedInitializerTyped
      exact ⟨CatalogCoupledExtractionFor.initializerInitialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.initialized_child allocation annotation same fixedTyped)))⟩
  | @initializerDiscard context expression expressionNode rest condition post statements expected found typed syntaxTree remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
      obtain ⟨fixedChildType, fixedDiscardedTyped⟩ := computation_child fixedTyped
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped fixedDiscardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      obtain ⟨_, fixedBodyTyped⟩ := TypedLexicalWhile.Native.discard_child fixedTyped
      exact ⟨CatalogCoupledExtractionFor.initializerDiscard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ bodyTyped fixedBodyTyped))⟩
  | @initializerAssign context assignment operator rhs rest condition post statements expected sourceTyped writable rightTyped profile children remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, accepted, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases accepted
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      have compiled : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures policy.lowerExpression headerFuel source scope parentSite
          assignment operator (some rhs) (LocalLoop.controlType type) body reasonAt
          (invalidProjection parentSite assignment.target.root) (invalidOperand parentSite assignment.target.root operator)
          (missingDefault parentSite assignment.target.root) = .ok code := by
        cases operator <;> simpa only [SourceCoreLoops.assignValue, assignments.equal, assignments.value] using accepted
      obtain ⟨head, rfl, sameToken, prepared⟩ := CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors.Head.of_lower_with_raw_occurrences unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated raw => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨childType, childNative⟩ := raw
          obtain ⟨fixedChildType, fixedChildNative⟩ := fixed_assignment_occurrence compiled fixedTyped member generated
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative fixedChildNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initializerAssign (factory := factory) head parentSite origin.header.operand sameToken sourceTyped rightTyped profile headerFuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped)))⟩

  | @bitNot context mode id node assignment rest expected found form writable bare profile remaining ih =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      simp only [unaryPolicy] at accepted
      obtain ⟨body, compiledBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨CatalogCoupledExtractionFor.bitNot (factory := factory) found form head writable bare profile (.occurrence id.occurrence) (EmittedDiagnosticTokenPlan.UnaryOccursFor.statement found form) sameToken (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody
        (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped)))⟩
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases generated
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at generated
      obtain ⟨body, generatedBody, generated⟩ := bind_ok generated
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile generated
      exact ⟨CatalogCoupledExtractionFor.initializerBitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin.header) sameToken (Classical.choice (ih closed residual sourceSignatures declarations projection
        ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped) (TypedImperative.Native.execute_continuation fixedTyped)))⟩


  | @matchWith context mode id node resolution scrutineeNode rest expected control caseFacts
      found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary children remaining childIH restIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
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
      obtain ⟨⟨matchedType, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨fixedMatchedType, fixedMatchedTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedPairedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType _fixedNativeType childTyped fixedChildTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped fixedChildTyped) generatedMatch matchedTyped fixedMatchedTyped
      refine ⟨CatalogCoupledExtractionFor.matchWith (factory := factory) found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary) ?_ ?_ rfl sourceSignatures⟩
      · intro request member childContext selectedContext
        apply Classical.choice
        obtain ⟨⟨childFuel, generated⟩, childTyped, fixedChildTyped⟩ := generatedChildren request member
        have childDeclarations :=
          matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
        exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped fixedChildTyped
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)


  | @terminalMatch context mode id node resolution scrutineeNode rest expected control caseFacts
      exactUnique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped
      hiddenOrdinary armsOrdinary children stops childIH =>
    simp only [AssignmentDiagnosticOrigins.AcceptedFor] at accepted
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((unary_read_found (readPolicy ▸ read)).symm.trans found)
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
      obtain ⟨⟨matchedType, matchedTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨fixedMatchedType, fixedMatchedTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedPairedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType _fixedNativeType childTyped fixedChildTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped fixedChildTyped) generatedMatch matchedTyped fixedMatchedTyped
      let descendants : ∀ request, request ∈ requests → ∀ childContext,
          GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
          CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
            childContext request.scope (.statements false request.statements) expected type request.code :=
        fun request member childContext selectedContext => Classical.choice (by
          obtain ⟨⟨childFuel, generated⟩, childTyped, fixedChildTyped⟩ := generatedChildren request member
          have childDeclarations :=
            matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
          obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
          exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
            (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped fixedChildTyped)
      have issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedBody
      let ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary
      exact ⟨CatalogCoupledExtractionFor.terminalMatch (factory := factory) exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt ordinary descendants stops issued rfl sourceSignatures⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeImperativeCollectors
