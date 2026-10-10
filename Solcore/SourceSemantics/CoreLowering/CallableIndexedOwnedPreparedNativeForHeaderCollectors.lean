import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderCertificates

/-! Actual for-item syntax/compiler induction adds the native witness of each
initializer/discard occurrence from its literal outer bind. The continuation,
marked allocation, original Source typing and diagnostic origin stay exact.
Actual assignment RHS/keys derive their own native witnesses from this same
code. No expected child typing or body execution law is accepted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors
open Core Frontend SourceInference GenericForHeader
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)

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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : ExpressionId → Prop}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {policy : SourceCoreLoops.Policy} {parentSite : SourceCoreElaboration.ErrorSite}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Native typing is manufactured at the actual initialized/discard child.
Assignment factories remain separate until their original wrappers are inverted. -/
theorem extraction_of_lowerForItems_with_coupled (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
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
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates sourceContext scope id lowered)

    {next : Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = residualMode →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm}
    (syntaxTree : Syntax source expressionSyntax context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor tracked source parentSite items) :
    Nonempty (CoupledTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
      context scope items code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
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
          (scope_bind payload declarations declaration extended) generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) origin.tail))⟩

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
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped
      exact ⟨CoupledTokenDiagnosticExtraction.initialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) origin.tail))⟩

  | @discard context expression expressionNode rest found typed syntaxTree remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨CoupledTokenDiagnosticExtraction.discard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations generatedBody bodyTyped origin.tail))⟩

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
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CoupledTokenDiagnosticExtraction.assign (factory := factory) head parentSite origin.operand sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations generatedBody (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

  | @bitNot context assignment rest writable bare profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨CoupledTokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin) sameToken (Classical.choice (ih closed residual sourceSignatures declarations generatedBody
        (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors
