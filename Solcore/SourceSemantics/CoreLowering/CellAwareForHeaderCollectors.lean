import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates

/-! Actual header lowering determines every child, marked allocation and
operand token. Its final continuation is a static compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation source)
open CompatibleEncoding (bind_ok)
open CompatibleStatementBindings (binder_projected scope_bind)

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

private theorem operands_at {source : TypedSource} {context : SourceSemantics.Context}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (typed : SourceAssignmentHasType source context assignment operator rhs) :
    AssignmentOperandDiagnostics.OperandsLaw (GenericAssignmentDiagnostics.OperandRep table)
      operator (GenericAssignmentDiagnostics.token table site assignment.target.root operator) := by
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands prepared present.1 (.statement form)
      (AssignmentDiagnosticOrigins.raw_profile typed)
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands prepared present.1 (.header form member)
      (AssignmentDiagnosticOrigins.raw_profile typed)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : Compilation prepared named diagnostics namedCode)
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {approved : ExpressionId → Prop} {administrative : Core.Context} {reasonAt : ExpressionId → Word}
  {policy : SourceCoreLoops.Policy}

theorem collected
    (unique : NodeOccurrencesUnique (source named))
    (assignmentsPrepared : ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compiled.own.assignments)
    (assignmentPolicy : ∀ fuel scope site assignment operator rhs output next reasonAt,
      SourceCoreLoops.assignValue policy fuel (source named) scope site assignment operator rhs output next reasonAt =
      SourceCoreCompatibleDataPlaces.lower (.initial checked) checked.signatures policy.lowerExpression
        fuel (source named) scope site assignment operator (some rhs) output next reasonAt
        (diagnostics.placeReason named.signature.key site assignment.target.root none)
        (GenericAssignmentDiagnostics.token compiled.own.assignments site assignment.target.root operator)
        (fun type => diagnostics.placeReason named.signature.key site assignment.target.root (some type)))
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder (source named) scope binder = SourceCoreCompatibleDataExpressions.lowerBinder checked (source named) scope binder)
    (allocationPolicy : policy.sourceCells = some (CallableIndexedNamedGeneration.allocator prepared named))
    (children : ∀ sourceContext,
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations (source named) scope sourceContext →
      approved id → (source named).lookupExpression? id = some node →
      ExpressionHasType (source named) sourceContext id node.type →
      policy.lowerExpression fuel (source named) scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType prepared.layouts.definitions → certificates sourceContext scope id lowered)
    {finalContext : SourceSemantics.Context} {next : SourceCoreLocalCell.Scope → Except SourceCoreBasic.Error Expr}
    {continuation : SourceCoreLocalCell.Scope → Expr → Prop}
    (nextCertificate : ∀ scope code,
      CompatibleExpressionReads.ScopeDeclarations (source named) scope finalContext →
      next scope = .ok code → ∀ {nativeType},
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions →
      continuation scope code)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    (syntaxTree : CellAwareForHeaderAdmission.Syntax (source named) approved context items finalContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source named) scope context)
    {site : SourceCoreElaboration.ErrorSite}
    (origin : AssignmentDiagnosticOrigins.HeaderOriginFor true (source named) site items)
    {fuel : Nat} {type : Ty} {code : Expr} {nativeType : Ty}
    (accepted : SourceCoreLoops.lowerForItems policy site fuel (source named) scope items type reasonAt next = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType prepared.layouts.definitions) :
    ∃ finalScope terminal,
      continuation finalScope terminal ∧
      CellAwareForHeaderTree.Tree prepared named compiled certificates administrative type finalContext finalScope terminal
        context scope items code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil =>
    refine ⟨scope, code, nextCertificate scope code declarations ?_ nativeTyped, .nil⟩
    cases fuel <;> exact accepted
  | @absent context nextContext finalContext binder rest declaration mono extended ordinary remaining ih =>
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
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate
        (scope_bind payload declarations declaration extended) origin.tail generated
        (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)
      exact ⟨finalScope, terminal, nextReceipt, .absent declaration mono extended ordinary
        (binder_projected (binderPolicy scope binder mono ▸ projected)) allocation annotation same tail⟩
  | @initialized context nextContext finalContext binder initializer node rest declaration mono extended ordinary found sourceType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checkedType, checkedTypeEq, accepted⟩ := bind_ok accepted
      cases checkedType
      have sameType := ensure_same checkedTypeEq
      subst payload
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts (fun error => .sourceAllocation (reprStr error)) generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      have child := children context declarations value found typed generated childTyped
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate
        (scope_bind lowered.type declarations declaration extended) origin.tail generatedBody
        (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)
      exact ⟨finalScope, terminal, nextReceipt, .initialized declaration mono extended ordinary found sourceType
        typed child allocation annotation same tail⟩
  | @discard context finalContext expression node rest found typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate declarations origin.tail generatedBody tailTyped
      exact ⟨finalScope, terminal, nextReceipt,
        .discard found typed (children context declarations value found typed generated childTyped) tail⟩
  | @assign context finalContext assignment operator rhs node binder rest declaration targetType profile bare found sourceType typed value remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerForItems] at accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      rw [assignmentPolicy] at accepted
      obtain ⟨_projections, writable, rightTyped, runtimeProfile⟩ :=
        ScopedSourceForItemsAdmission.assignment_facts declaration targetType bare typed
      obtain ⟨actualBinder, preparedPlace, index, lowered, _binding, _rootType, _rawView, _slot,
        _layout, generated, _sameType, _profile, codeEq⟩ := CompatibleBareAssignment.of_lower bare accepted
      obtain ⟨_, rhsNative⟩ := (CallableIndexedOwnedPreparedNativeAssignmentChildren.execute_children
        (codeEq ▸ nativeTyped)).1
      have child : certificates context scope rhs lowered :=
        children context declarations value found (sourceType.symm ▸ rightTyped) generated rhsNative
      obtain ⟨head, emitted, token⟩ := GenericAssignmentStatements.Head.of_lower_bare_with_token
        (administrative := administrative) (definitions := prepared.layouts.definitions)
        bare unique writable rightTyped runtimeProfile (fun actual acceptedRight => by
          have same : actual = lowered := Except.ok.inj (acceptedRight.symm.trans generated)
          subst actual
          exact ⟨node, found, child⟩) accepted
      have tailTyped := TypedImperative.Native.execute_continuation (emitted ▸ nativeTyped)
      obtain ⟨first, tablePrepared⟩ := assignmentsPrepared
      have operands := operands_at tablePrepared origin.operand typed
      rw [← token] at operands
      obtain ⟨finalScope, terminal, nextReceipt, tail⟩ := ih nextCertificate declarations origin.tail generatedBody tailTyped
      rw [emitted]
      exact ⟨finalScope, terminal, nextReceipt, .assign head bare typed operands tail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderCollectors
