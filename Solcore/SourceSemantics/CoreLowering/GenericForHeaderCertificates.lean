import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderTokenExtraction
import Solcore.SourceSemantics.CoreLowering.EmittedForHeaderDiagnosticExtraction
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderDiagnosticExtraction
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderTree
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates

/-! Accepted for-item lowering determines a static header tree. The actual
whole-code HasType is inverted through marked allocations and assignment
slots; continuation certificates describe code, never runtime execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)

private theorem unary_ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

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

/-- The static expression receipt is shared with ordinary assignment heads.
Neither it nor the continuation extractor assumes a child evaluation. -/
theorem extraction_of_lowerForItems_with_tokens (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
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
    Nonempty (TokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary certificates definitions administrative type continuation
      context scope items code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil => exact ⟨TokenDiagnosticExtraction.nil (factory := factory) (nextCertificate _ scope code closed residual sourceSignatures declarations (by cases fuel <;> exact accepted))⟩

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
      exact ⟨TokenDiagnosticExtraction.uninitialized (factory := factory) monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
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
      obtain ⟨initial, _⟩ := expressions context scope fuel initializer lowered closed residual sourceSignatures declarations initializerSyntax initializerNode initializerFound typed generated
      exact ⟨TokenDiagnosticExtraction.initialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
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
      obtain ⟨child, _⟩ := expressions context scope fuel expression lowered closed residual sourceSignatures declarations syntaxTree expressionNode found typed generated
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨TokenDiagnosticExtraction.discard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations generatedBody bodyTyped origin.tail))⟩

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
      obtain ⟨head, rfl, sameToken⟩ := GenericAssignmentStatements.Head.of_lower_with_token unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨tree, nativeTyped⟩ := expressions context scope fuel id lowered closed residual sourceSignatures declarations syntaxTree node found typed generated
          exact ⟨node, found, tree, nativeTyped⟩) compiled nativeTyped
      exact ⟨TokenDiagnosticExtraction.assign (factory := factory) head parentSite origin.operand sameToken sourceTyped rightTyped profile (Classical.choice (ih closed residual sourceSignatures declarations generatedBody (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

  | @bitNot context assignment rest writable bare profile remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile accepted
      exact ⟨TokenDiagnosticExtraction.bitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin) sameToken (Classical.choice (ih closed residual sourceSignatures declarations generatedBody
        (TypedImperative.Native.execute_continuation nativeTyped) origin.tail))⟩

theorem extraction_of_lowerForItems_with_emitted (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
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
    Nonempty (ProducedDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory certificates definitions administrative type continuation
      context scope items code) := by
  obtain ⟨produced⟩ := extraction_of_lowerForItems_with_tokens residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped origin
  exact ⟨produced.toProduced⟩

theorem extraction_of_lowerForItems_with_residual (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
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
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code) := by
  obtain ⟨produced⟩ := extraction_of_lowerForItems_with_emitted residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped origin
  exact ⟨produced.original⟩

/-- Compatibility entry for the former closed residual scope. -/
theorem extraction_of_lowerForItems {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {next : Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = false →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm}
    (syntaxTree : Syntax source expressionSyntax context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor tracked source parentSite items) :
    Nonempty (DiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code) := by
  exact extraction_of_lowerForItems_with_residual false (tracked := tracked) (diagnosticPolicy := diagnosticPolicy)
    (factory := factory) (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (expressions := expressions)
    (next := next) (nextCertificate := nextCertificate) (context := context) (scope := scope) (items := items)
    (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (fuel := fuel) (code := code) (nativeType := nativeType) (accepted := accepted)
    (nativeTyped := nativeTyped) (origin := origin)

theorem tree_of_lowerForItems_with_residual (residualMode : Bool)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
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
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code := by
  exact (Classical.choice (extraction_of_lowerForItems_with_residual residualMode (AssignmentDiagnosticOrigins.Factory.unchanged .unconditional source invalidOperand) binderPolicy allocationPolicy assignments unaryPolicy unique expressions nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped True.intro)).tree

/-- Compatibility entry for the former closed residual scope. -/
theorem tree_of_lowerForItems
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (expressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = false →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {next : Scope → Except SourceCoreBasic.Error Expr}
    (nextCertificate : ∀ context scope code,
      context.typeVariables = [] → context.residualTypeVariables = false →
      context.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope context →
      next scope = .ok code → continuation context scope code)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm}
    (syntaxTree : Syntax source expressionSyntax context items)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy parentSite fuel source scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source certificates definitions administrative type continuation
      context scope items code := by
  exact tree_of_lowerForItems_with_residual false (binderPolicy := binderPolicy) (allocationPolicy := allocationPolicy)
    (assignments := assignments) (unaryPolicy := unaryPolicy) (unique := unique) (expressions := expressions)
    (next := next) (nextCertificate := nextCertificate) (context := context) (scope := scope) (items := items)
    (syntaxTree := syntaxTree) (closed := closed) (residual := residual) (sourceSignatures := sourceSignatures)
    (declarations := declarations) (fuel := fuel) (code := code) (nativeType := nativeType) (accepted := accepted)
    (nativeTyped := nativeTyped)

end Solcore.SourceSemantics.CoreLowering.GenericForHeader
