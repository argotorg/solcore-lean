import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.EmittedForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericForHeaderTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedForHeaders

/-!
# Generic for headers

Certificates, meaning, reflection and posts of `for` headers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericForHeaderCertificates
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
theorem extraction_of_lowerForItems_with_coupled (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨initial, _⟩ := expressions context scope fuel initializer lowered closed residual sourceSignatures declarations initializerSyntax initializerNode initializerFound typed generated
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
      obtain ⟨child, _⟩ := expressions context scope fuel expression lowered closed residual sourceSignatures declarations syntaxTree expressionNode found typed generated
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
      obtain ⟨head, rfl, sameToken, prepared⟩ := GenericAssignmentStatements.Head.of_lower_with_prepared unique sourceSignatures sourceTyped writable rightTyped profile
        (fun id lowered member generated => by
          obtain ⟨syntaxTree, node, found, typed⟩ := children id member
          obtain ⟨tree, nativeTyped⟩ := expressions context scope fuel id lowered closed residual sourceSignatures declarations syntaxTree node found typed generated
          exact ⟨node, found, tree, nativeTyped⟩) compiled nativeTyped
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

theorem extraction_of_lowerForItems_with_prepared (residualMode : Bool) {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
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
    Nonempty (PreparedTokenDiagnosticExtraction diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault certificates definitions administrative type continuation
      context scope items code) := by
  obtain ⟨produced⟩ := extraction_of_lowerForItems_with_coupled residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped origin
  exact ⟨produced.original⟩

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
  obtain ⟨produced⟩ := extraction_of_lowerForItems_with_prepared residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions nextCertificate syntaxTree closed residual sourceSignatures declarations accepted nativeTyped origin
  exact ⟨produced.original⟩

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericForHeaderMeaning
/-! Successful ordinary header prefixes retain their real stopping scope and
all actual captured values. Their continuation agreement neither runs nor
assumes the syntactic continuation; initializer and post callers decide that. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Tail Result Fallthrough)

private theorem extended_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binder : TypedBinder} (first : BinderExtends owner context binder left)
    (second : BinderExtends owner context binder right) : left = right := by
  cases first; cases second; rfl

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension meaning faithful observations in
theorem Tree.preserves_prefix {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  induction tree generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after with
  | nil next =>
    cases trace
    exact ⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining ih =>
    cases trace with | cons first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases extended_eq extended other
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
          allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated
        obtain ⟨tail, maps, worlds, lastFrame, metadata, agreement⟩ :=
          ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        exact ⟨tail,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
          (ContinuationAgreement.letE allocationEval).trans agreement⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining ih =>
    cases trace with | cons first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases extended_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.value initialTrace)
        cases represented with
        | value payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
            allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
          obtain ⟨tail, finalMaps, finalWorlds, finalFrame, finalMetadata, agreement⟩ :=
            ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 rest
          refine ⟨tail,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), ?_⟩
          rw [sequence_rename]
          exact (ContinuationAgreement.bind initialEval).trans ((ContinuationAgreement.letE allocationEval).trans agreement)
      | letInitializedGeneralized _ captures poly other allocated => exact False.elim (poly mono)
  | discard found child remaining ih =>
    cases trace with | cons first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
            ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
          refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at agreement
          exact (ContinuationAgreement.bind first).trans agreement
  | @assign context scope assignment operator rhs rest body head remaining ih =>
    cases trace with | cons first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions extension program evidence (meaning _ valid) faithful observations
            environments heaps locals agrees actualTyped assigned
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNot context scope assignment rest body head remaining ih =>
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence
            environments heaps locals agrees actualTyped assigned
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNotProjected context scope assignment rest body head remaining ih =>
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions extension program evidence (meaning _ valid) faithful observations
            environments heaps locals agrees actualTyped assigned
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

include definitions registered extension meaning faithful observations in
theorem Tree.preserves_fault_reachable {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext after with
  | nil => cases trace
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    cases trace with
    | head failed => cases failed with | polymorphicLet poly unsupported => exact False.elim (poly mono)
    | tail first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases extended_eq extended other
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
          allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, maps, worlds, lastFrame, metadata⟩ :=
          ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        exact ⟨token, finalStore, finalMap, finalWorld, .letE allocationEval completed, matched, finalHeaps,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    rw [sequence_rename]
    cases trace with
    | head failed =>
      cases failed with
      | polymorphicLet poly unsupported => exact False.elim (poly mono)
      | letInitializer _ failed =>
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.fault failed)
        cases represented with | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩
    | tail first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases extended_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.value initialTrace)
        cases represented with
        | value payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
            allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
            ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 rest
          exact ⟨token, finalStore, finalMap, finalWorld, LanguageResult.bind_success _ initialEval (.letE allocationEval completed), matched, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata)⟩
      | letInitializedGeneralized _ captures poly other allocated => exact False.elim (poly mono)
  | @discard context scope expression expressionNode rest lowered body found child remaining remainingErrors ih =>
    rw [LoopRenaming.discard]
    cases trace with
    | head failed =>
      cases failed with | expression failed =>
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.fault failed)
        cases represented with | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩
    | tail first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
            ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
          rw [GenericExpressionMeaning.rename_prefix] at completed
          exact LocalSequence.discard_success _ first completed
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    cases trace with
    | head failed =>
      cases failed with | assignValue failed =>
        exact head.preserves_fault_reachable functions extension program evidence (meaning _ valid) faithful observations
          environments heaps locals agrees actualTyped headErrors failed body (LocalLoop.controlType type)
    | tail first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions extension program evidence (meaning _ valid) faithful observations
            environments heaps locals agrees actualTyped assigned
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    cases trace with
    | head failed =>
      cases failed with | assignBitNot failed =>
        exact head.preserves_fault functions program evidence
          environments heaps locals agrees headErrors failed body (LocalLoop.controlType type)
    | tail first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence
            environments heaps locals agrees actualTyped assigned
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 rest
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

include definitions registered extension meaning faithful observations in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.preserves_fault {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericForHeaderReflection
/-! Completed native headers reconstruct their independent source prefix or
first fault. A successful prefix exposes the real remaining evaluation under
its actual typed environment; no source trace or child execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Tail Result Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension meaning reflection faithful observations in
theorem Tree.reflects_reachable (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native value finalStore with
  | @nil context scope code next =>
    exact .continues ⟨scope, code, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩ .nil (.refl _) (.refl _) (.refl _ _) (.refl _) evaluated
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append
    have remainingEval := (ContinuationAgreement.letE allocationEval).unwrap evaluated
    have reflected := ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
      (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 remainingEval
    exact reflected.prepend (.letUninitialized mono extended .append)
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
      preservation (.of_allocation Dynamic.Heap.Allocates.append)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle, Evaluates actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, initial⟩
    obtain ⟨input, middleStore, initialEval⟩ := input
    obtain ⟨sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
      reflection _ valid child found
        environments heaps locals agrees actualTyped initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LanguageResult.bind_failure _ initialEval)
        exact .fault (.head (.letInitializer mono failed)) rfl matched middleHeaps maps worlds preservation metadata
    | value payload =>
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append
        have tailEval := (ContinuationAgreement.letE allocationEval).unwrap ((ContinuationAgreement.bind initialEval).unwrap evaluated)
        have reflected := ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (List.getElem?_eq_some_iff.mp frameRead).1).1 tailEval
        exact reflected.prepend (.letInitialized initialTrace mono extended .append)
          (maps.trans (show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩))
          (worlds.trans (show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩))
          (preservation.trans allocationFrame) (metadata.trans (.of_allocation Dynamic.Heap.Allocates.append))
  | @discard context scope expression expressionNode rest lowered body found child remaining remainingErrors ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        reflection _ valid child found
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with | fault matched =>
        cases trace with | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact .fault (.head (.expression failed)) rfl matched finalHeaps maps worlds preservation metadata
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        reflection _ valid child found
          environments heaps locals agrees actualTyped childEvaluation
      cases represented with | @value _ coreValue payload =>
        cases trace with | value childTrace =>
          have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact reflected.prepend (.expression childTrace) maps worlds preservation metadata
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    rcases head.reflects_reachable functions extension program evidence (meaning _ valid) (reflection _ valid) faithful observations
      environments heaps locals agrees actualTyped functionTypes headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, remainingEval⟩
    · exact .fault (.head (.assignValue trace)) rfl matched finalHeaps maps worlds preservation metadata
    · have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval)
      exact reflected.prepend (.assignValue trace) maps worlds preservation metadata

  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    rcases head.reflects functions program evidence
      environments heaps locals agrees actualTyped headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, remainingEval⟩
    · exact .fault (.head (.assignBitNot trace)) rfl matched finalHeaps maps worlds preservation metadata
    · have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval)
      exact reflected.prepend (.assignBitNot trace) maps worlds preservation metadata

include definitions registered extension meaning reflection faithful observations in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.GenericForHeaderPost
/-! The post header has an actual constant fallthrough continuation. Closing
that continuation recovers finite post execution and reflection. Source names
introduced by the post can then be forgotten without dropping their cells or
effects, or changing the captured outer native environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Tail Result Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

include definitions registered extension meaning faithful observations in
theorem Tree.preserves_post {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native (Fallthrough type) finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      Evaluates actual store (code.rename ξ) (LocalLoop.fallthroughValue type) tail.store ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions := by
  obtain ⟨tail, maps, worlds, preservation, metadata, agreement⟩ :=
    tree.preserves_prefix functions definitions registered extension program evidence meaning faithful observations
      valid environments heaps locals agrees actualTyped reference read unmapped trace
  refine ⟨tail, maps, worlds, preservation, metadata, agreement.wrap tail.fallthrough_evaluates,
    environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds⟩

include definitions registered extension meaning reflection faithful observations in
theorem Tree.reflects_post_reachable (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) := by
  have reflected := tree.reflects_reachable functions definitions registered extension program evidence meaning reflection faithful observations
    functionTypes errors valid environments heaps locals agrees actualTyped reference read unmapped evaluated
  cases reflected with
  | continues tail trace maps worlds preservation metadata remaining =>
    obtain ⟨same, storeEq⟩ := tail.fallthrough_reflects remaining
    exact .inl ⟨_, _, _, tail, trace, same, storeEq, maps, worlds, preservation, metadata,
      environments.extend maps worlds, locals.mono metadata, actualTyped.weaken worlds⟩
  | fault trace same matched finalHeaps maps worlds preservation metadata =>
    exact .inr ⟨_, _, _, _, _, _, trace, same, matched, finalHeaps, maps, worlds, preservation, metadata⟩

include definitions registered extension meaning reflection faithful observations in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects_post (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type (Fallthrough type)
      context scope items code) (errors : Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : Tail registry functions source solved evidence administrative frame globals contextLocation native
        (Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) := by
  apply Tree.reflects_post_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.GenericForHeader
end
