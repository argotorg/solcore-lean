import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeForHeaderCollectors

/-! The original imperative syntax/compiler induction retains local native
expression witnesses from the same enclosing emitted code. Lexical leaves and
match scrutinees use the actual native collectors; installed while/for closures
supply their raw condition typing by removal of the two administrative entries.
Actual assignment keys and present right-hand sides derive their local
native witnesses internally from the same code. For-post lexical children use
the same actual enclosing-code inversion as ordinary initializers/discards.
Source facts,
allocator identity, ordered occurrences and diagnostics remain unchanged.
This module constructs static extraction receipts, not a semantic E/F law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
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
  {definitions : DataEnvironment} {administrative : Core.Context}

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
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)

    {context : SourceSemantics.Context} {scope : Scope} {position : Position} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor tracked policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
      context scope position expected type code) := by
  classical
  induction syntaxTree generalizing scope fuel code nativeType with
  | body syntaxTree => exact ⟨CatalogCoupledExtractionFor.body (factory := factory) syntaxTree (CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy expressions syntaxTree closed residual sourceSignatures declarations projection accepted nativeTyped)⟩
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
          (scope_bind payload declarations declaration extended) projection generated (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩

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
      exact ⟨CatalogCoupledExtractionFor.initialized (factory := factory) found form mono extended ordinary initializerFound sourceType
        (expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped)
        allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩

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
        obtain ⟨childType, discardedTyped⟩ := computation_child nativeTyped
        exact ⟨CatalogCoupledExtractionFor.discard (factory := factory) found form notTail expressionFound (expressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated discardedTyped)
          (Classical.choice (ih closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

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
      exact ⟨CatalogCoupledExtractionFor.block (factory := factory) found form (Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
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
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
        exact ⟨CatalogCoupledExtractionFor.ifThen (factory := factory) found form conditionFound conditionType
          (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
          (Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)) (Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)) (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

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
      let child := Classical.choice (innerIH closed residual sourceSignatures declarations projection generatedInner headTyped)
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
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      obtain ⟨conditionNativeType, conditionNative⟩ := computation_child branchTyped
      let left := Classical.choice (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)
      let right := Classical.choice (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)
      let conditionTree := expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative
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
      obtain ⟨⟨_, loopBodyTyped⟩, loopTyped⟩ := TypedLexicalWhile.Native.while_body loopTyped
      have conditionNative := iterate_condition loopTyped
      exact ⟨CatalogCoupledExtractionFor.whileLoop (factory := factory) found form conditionFound conditionType
        (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionNative)
        (Classical.choice (loopIH closed residual sourceSignatures declarations projection generatedLoop loopBodyTyped))
        loopTyped
        (Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped))⟩

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
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.assign (factory := factory) found form head (.occurrence id.occurrence) (AssignmentDiagnosticOrigins.OccursFor.statement found form) sameToken sourceTyped rightTyped profile fuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection compiledBody (TypedImperative.Native.execute_continuation nativeTyped)))⟩

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
      refine ⟨CatalogCoupledExtractionFor.forLoop (factory := factory) found form ?_ ?_⟩
      · apply Classical.choice
        apply initialIH closed residual sourceSignatures declarations projection (nativeTyped := initialTyped)
        refine ⟨fuel, .occurrence id.occurrence, _, AssignmentDiagnosticOrigins.ForOriginFor.start found form, generatedInitial, ?_⟩
        intro loopScope nextCode generated
        obtain ⟨conditionCode, conditionGenerated, generated⟩ := bind_ok generated
        obtain ⟨checked, conditionChecked, generated⟩ := bind_ok generated
        cases checked
        obtain ⟨loopCode, loopGenerated, generated⟩ := bind_ok generated
        obtain ⟨postCode, postGenerated, generated⟩ := bind_ok generated
        cases generated
        exact ⟨conditionCode, loopCode, postCode, conditionGenerated, (unary_ensure_same conditionChecked).symm, loopGenerated, postGenerated, rfl⟩
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @initializersDone context condition conditionNode post statements expected conditionFound conditionType typed conditionSyntax loopBody postSyntax loopIH =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    have nextAccepted : next scope = .ok code := by cases headerFuel <;> exact generated
    obtain ⟨conditionCode, loopCode, postCode, conditionGenerated, conditionChecked, loopGenerated, postGenerated, rfl⟩ :=
      nextReceipt scope code nextAccepted
    rcases conditionCode with ⟨native, expression⟩
    dsimp only at conditionChecked
    subst native
    obtain ⟨⟨_, bodyTyped⟩, ⟨_, postTyped⟩, loopTyped⟩ := TypedImperativeFor.Native.iterate_children nativeTyped
    have conditionNative := iterate_condition loopTyped
    exact ⟨CatalogCoupledExtractionFor.initializersDone (factory := factory) conditionFound conditionType
      (expressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed conditionGenerated conditionNative)
      (Classical.choice (loopIH closed residual sourceSignatures declarations projection loopGenerated bodyTyped))
      (Classical.choice (CallableIndexedOwnedPreparedNativeForHeaderCollectors.extraction_of_lowerForItems_with_coupled residualMode factory binderPolicy allocationPolicy assignments unaryPolicy unique expressions
        (fun _ _ _ _ _ _ _ same => by cases same; rfl) postSyntax closed residual sourceSignatures declarations postGenerated postTyped origin.post_origin))
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
          (scope_bind payload declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generated, nextReceipt⟩ (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped)))⟩
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
      have initial := expressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated initializerTyped
      exact ⟨CatalogCoupledExtractionFor.initializerInitialized (factory := factory) mono extended ordinary initializerFound sourceType initial allocation annotation same
        (Classical.choice (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped)))⟩
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
      have child := expressions context closed residual sourceSignatures declarations syntaxTree found typed generated discardedTyped
      obtain ⟨_, bodyTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initializerDiscard (factory := factory) found child (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ bodyTyped))⟩
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
          exact ⟨node, found, expressions context closed residual sourceSignatures declarations
            syntaxTree found typed generated childNative⟩) compiled nativeTyped
      exact ⟨CatalogCoupledExtractionFor.initializerAssign (factory := factory) head parentSite origin.header.operand sameToken sourceTyped rightTyped profile headerFuel prepared (Classical.choice (ih closed residual sourceSignatures declarations projection ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩

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
        (TypedImperative.Native.execute_continuation nativeTyped)))⟩
  | @initializerBitNot context assignment rest condition post statements expected writable bare profile remaining ih =>
    obtain ⟨headerFuel, parentSite, next, origin, generated, nextReceipt⟩ := accepted
    cases headerFuel with
    | zero => cases generated
    | succ headerFuel =>
      simp only [SourceCoreLoops.lowerForItems, unaryPolicy] at generated
      obtain ⟨body, generatedBody, generated⟩ := bind_ok generated
      obtain ⟨head, rfl, sameToken⟩ := CompatibleBitNotStatements.Head.of_lower_with_token writable bare profile generated
      exact ⟨CatalogCoupledExtractionFor.initializerBitNot (factory := factory) head writable bare profile parentSite (EmittedDiagnosticTokenPlan.UnaryOccursFor.of_header origin.header) sameToken (Classical.choice (ih closed residual sourceSignatures declarations projection
        ⟨headerFuel, parentSite, next, origin.tail, generatedBody, nextReceipt⟩ (TypedImperative.Native.execute_continuation nativeTyped)))⟩


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
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType childTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped) generatedMatch matchedTyped
      refine ⟨CatalogCoupledExtractionFor.matchWith (factory := factory) found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt
        (CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary) ?_ ?_ rfl sourceSignatures⟩
      · intro request member childContext selectedContext
        apply Classical.choice
        obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
        have childDeclarations :=
          matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
        obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
        exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
          (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped
      · exact Classical.choice (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)


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
      obtain ⟨requests, receipt, _, generatedChildren⟩ := CallableIndexedOwnedPreparedNativeMatchCollectors.finite_typed_of_lower
        onError matchAllocator matchDefinitions (expressionCertificate := certificates context)
        (fun childFuel lowered generated _nativeType childTyped => expressions context closed residual sourceSignatures declarations
          scrutineeSyntax scrutineeFound scrutineeTyped generated childTyped) generatedMatch matchedTyped
      let descendants : ∀ request, request ∈ requests → ∀ childContext,
          GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
          CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source factory invalidUnary invalidProjection missingDefault expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
            childContext request.scope (.statements false request.statements) expected type request.code :=
        fun request member childContext selectedContext => Classical.choice (by
          obtain ⟨⟨childFuel, generated⟩, childTyped⟩ := generatedChildren request member
          have childDeclarations :=
            matchChildStatic scrutineeFound declarations receipt matchedTyped request member childContext selectedContext
          obtain ⟨sameSignatures, sameVariables, sameResidual⟩ := GenericMatchChildren.ScopedContextFor.closed_fields selectedContext
          exact childIH request childContext selectedContext.forget (sameVariables.trans closed) (sameResidual.trans residual)
            (sameSignatures.trans sourceSignatures) childDeclarations projection generated childTyped)
      have issued := GenericLexicalStatements.IssuedSuffix.of_accepted generatedBody
      let ordinary := CompatibleMatchSelectionPrefix.ordinary_of_source_ids receipt hiddenOrdinary armsOrdinary
      exact ⟨CatalogCoupledExtractionFor.terminalMatch (factory := factory) exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped matchCompilation
        matchValues matchDefinitions matchAllocator requests receipt ordinary descendants stops issued rfl sourceSignatures⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
