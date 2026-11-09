import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeMatchCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.EligibleSelected
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads

/-!
# Prepared callables: paired collectors

Paired native collectors of lexical and imperative statements, and paired profile extraction.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeLexicalCollectors
/-! One literal syntax/compiler induction retains independent actual and fixed
native typing at every used expression occurrence. Both contexts concern the
same scope, Source ID, compiler output and accepted action; neither witness is
rebased from the other. The resulting Tree remains the original static Tree.
Stopped suffixes retain issuance only. No expression execution is an input. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeLexicalCollectors
open Core Frontend SourceInference GenericLexicalStatements
open CompatibleEncoding (bind_ok)
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

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative fixedAdministrative : Core.Context}

/-- The original syntax/compiler induction supplies each callback with native
typing of that exact emitted expression, at its actual lexical scope. -/
theorem tree_of_typed_flow_with_residual (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions →
      HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative)
        lowered.expression fixedNativeType definitions → certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context mode statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType fixedNativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions)
    (fixedTyped : HasType (SourceCoreLocalCell.coreContext scope ++ fixedAdministrative) code fixedNativeType definitions) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType fixedNativeType with
  | nil allowed =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    cases accepted
    exact .nil allowed
  | @returnUnit context mode id node rest found form sourceType =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .returnUnit rest found form
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, fixedChildTyped⟩ := computation_child fixedTyped
      exact .returnValue rest found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped fixedChildTyped)
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, fixedChildTyped⟩ := computation_child fixedTyped
      exact .tail found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped fixedChildTyped)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated
          (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.absent_child allocation annotation same fixedTyped))

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      obtain ⟨_, fixedChildTyped⟩ := computation_child fixedTyped
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (extractExpressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated childTyped fixedChildTyped)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody
          (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped) (TypedLexicalWhile.Native.initialized_child allocation annotation same fixedTyped))

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
        obtain ⟨_, childTyped⟩ := computation_child nativeTyped
        obtain ⟨_, fixedChildTyped⟩ := computation_child fixedTyped
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        obtain ⟨_, fixedTailTyped⟩ := TypedLexicalWhile.Native.discard_child fixedTyped
        exact .discard found form notTail expressionFound (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped fixedChildTyped)
          (ih closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedInnerTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      exact .block found form (innerIH closed residual sourceSignatures declarations projection generatedInner innerTyped fixedInnerTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
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
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, fixedBranchTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨_, fixedConditionTyped⟩ := computation_child fixedBranchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped fixedConditionTyped)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨⟨_, fixedBranchTyped⟩, ⟨_, fixedTailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨_, fixedConditionTyped⟩ := computation_child fixedBranchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped fixedConditionTyped)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped fixedTailTyped)

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedInnerTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      exact .terminalBlock exactUnique found form
        (innerIH closed residual sourceSignatures declarations projection generatedInner innerTyped fixedInnerTyped) stops
        (IssuedSuffix.of_accepted generatedSuffix)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨⟨_, fixedBranchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children fixedTyped
      obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
      obtain ⟨_, fixedConditionTyped⟩ := computation_child fixedBranchTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      obtain ⟨⟨_, fixedThenTyped⟩, ⟨_, fixedElseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children fixedBranchTyped
      exact .terminalIf exactUnique found form conditionFound conditionType
        (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped fixedConditionTyped)
        (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped fixedThenTyped)
        (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped fixedElseTyped)
        thenStops elseStops (IssuedSuffix.of_accepted generatedSuffix)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeLexicalCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNativeImperativeCollectors
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
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
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
/-! Actual ordinary entry typing and fixed canonical body typing come from the
same prepared cached code. One paired compiler induction then manufactures
both local native witnesses for the certificate factory. The original Receipt,
Plan, structural eliminator and actual administrative indices are preserved.
Source syntax, selected metadata and diagnostic issuance remain independent.
No semantic execution law or arbitrary child context transport is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open RecursiveNamedPublicSpecializationMeaning RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedPreparedDirectNamedProfileExtraction (Receipt assignment_factory hidden_fresh)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {administrative : Core.Context}
  {first : Nat}
  (operandsTyped : AssignmentDiagnosticOrigins.OperandsTyped header.function.source)
  (issued : SourceCoreAssignmentFaultSites.prepare header.function.source first = .ok prepared.compilation.own.assignments)

/-- Only authentic Source syntax and local static certificates remain here.
Every raw child typing is manufactured by the enclosing-code collector. -/
structure Children where
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = compiled.compatible.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext →
    expressionSyntax header id → header.function.source.lookupExpression? id = some node →
    ExpressionHasType header.function.source sourceContext id node.type →
    header.policy.lowerExpression fuel header.function.source scope id header.reasonAt = .ok lowered →
    ∀ {nativeType fixedNativeType}, HasType (SourceCoreLocalCell.coreContext scope ++
      SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions →
    HasType (SourceCoreLocalCell.coreContext scope ++
      CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) header.named)
      lowered.expression fixedNativeType compiled.indexed.layouts.definitions → certificates header sourceContext scope id lowered
  syntaxTree : GenericImperativeMatch.Syntax header.function.source (expressionSyntax header) header.context
    (.statements true header.function.body) header.function.resultType

variable {recipe : SourceCoreIndexedSession.Recipe}
  (recipeAccepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
  {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
  {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame}
  (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers owner.key.locations 0 functions registry header arguments before initialStore mapping world
    administrative actualContext actual ξ frameLocation current ghost)


include prepared aligned recipeAccepted nativeMember in
/-- The exact cached native lambda and its actual bootstrap support derive the
literal parameter/global/frame body prefix, before any real entry transport. -/
theorem body_native_at_prefix :
    HasType (SourceCoreLocalCell.coreContext
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix» (compiled := compiled) header.named)
      header.body (LanguageResult.resultType header.output) compiled.indexed.layouts.definitions := by
  have typed := CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned nativeMember
  have support := CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported recipeAccepted prepared aligned
  have original : HasType
      ((compiled.indexed.base.globals.map (·.referenceType) ++ [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext nativeEntry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by simpa using typed
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original (by simpa using support)
  have minimalTyped : HasType
      (compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: [])
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType compiled.indexed.layouts.definitions := by
    simpa only [CallableIndexedAmbient.ambientDefinitions, List.append_nil, List.singleton_append] using minimal
  cases minimalTyped with
  | lambda parameterWF resultWF codeTyped =>
    obtain ⟨_, _, _, _, emitted⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry header.hook
    rw [emitted] at codeTyped
    have parameters := CallableIndexedParameterNativeInversion.withFrame_body codeTyped
    have body := CallableIndexedParameterNativeInversion.accepted_body header.onError header.acceptedPrefix parameters
    rw [CallableIndexedParameterNativeInversion.final_context] at body
    simpa only [CallableIndexedOwnedPreparedCanonicalCaptureReceipts.«prefix», header.parameterType, header.resultType,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using body


include aligned recipeAccepted nativeMember functions owner complete entry in
/-- Actual cache and support proofs transport the exact body to its real entry;
one finite collector then derives every visited child native witness. -/
theorem extract_at
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (children : Children (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := header) (administrative := administrative)) :
    Nonempty (Receipt (certificates := certificates) (expressionSyntax := expressionSyntax)
      (administrative := administrative) prepared operandsTyped issued) := by
  have nativeTyped := RecursiveNamedCatalogNativeContexts.canonical_cached complete aligned.globals
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed prepared aligned nativeMember)
    (CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported recipeAccepted prepared aligned) entry
  have fixedTyped := body_native_at_prefix prepared aligned recipeAccepted nativeMember
  have accepted := aligned.accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, emitted⟩ := CompatibleEncoding.bind_ok accepted
  have finished : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped :=
    Except.ok.inj emitted.symm
  rw [finished] at nativeTyped fixedTyped
  obtain ⟨_, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow nativeTyped
  obtain ⟨_, fixedFlowTyped⟩ := TypedLexicalWhile.Native.finished_flow fixedTyped
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidOperand prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.assignments prepared
  have unaries : CompatibleBitNotStatements.Policy header.policy (.initial compiled.compatible.checked)
      (Prepared.invalidProjection prepared) (Prepared.invalidUnary prepared) (Prepared.missingDefault prepared) := by
    rw [aligned.policy]
    exact Prepared.unary prepared
  obtain ⟨collected⟩ :=
    CallableIndexedOwnedPreparedPairedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled true .reachable
      (assignment_factory prepared operandsTyped issued)
      (Prepared.header_match prepared aligned) rfl rfl (Prepared.match_allocator prepared aligned)
      (GenericImperativeMatch.MatchChildStatic.of_hidden
        (matchCompilation := Prepared.ambientMatch prepared) (definitions := compiled.indexed.layouts.definitions)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        (certificates := certificates header) (hidden_fresh wellFormed))
      (Prepared.header_read prepared aligned) (Prepared.header_binder prepared aligned)
      (Prepared.header_allocator prepared aligned) children.expressions assignments unaries header.unique
      children.syntaxTree (RecursiveNamedSourceContextFacts.header_typeVariables header)
      (RecursiveNamedSourceContextFacts.header_residual header) (Prepared.header_signatures (header := header))
      (RecursiveNamedHeaderScopeDeclarations.header_scope
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (program := Program.ofChecked compiled.sourceProgram)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) header)
      aligned.projection generated flowTyped fixedFlowTyped
  exact ⟨⟨flow, generated, collected⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedNamedProfileExtraction
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEligibleExpressionFlowBounds
/-! The finite issued Header retains the same selected compiler packet used by
each child action. The actual paired collector constructs the finite child
Tree, both raw typings and the rich profile. The shared graded E hypothesis
then supplies child meaning to the original named flow producer once.

Occurrence-specific raw compiler Domain and Source syntax remain static
inputs. Neither a finished Tree nor an expression or body law is a static
construction input; arbitrary older profiles are not identified with issuers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEligibleExpressionFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedNamedDiagnosticSources
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedCanonicalCaptureReceipts («prefix»)
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Validity FlowPreserves FlowReflects bridge)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  (expressionSyntax : Header compiled → ExpressionId → Prop)
  (administrative : Core.Context)

/-- One literal child root, at the selected issuer, with its same finite Tree
and the actual and fixed native contexts supplied by the body collector. -/
def Certificate (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => ∃ predecessor,
    ∃ root : RootPolicyReceipt (compiled := compiled) input.prepared.named
      (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled packet.selected.diagnostics)
      packet.selected.code packet.selected.compilation predecessor packet.header.function.source
      scope id packet.header.reasonAt lowered,
    CallableIndexedOwnedPreparedPairedReachedNativeExpressionTreeBounds.RuntimeTree
      (sourceContext := sourceContext) (compilerScope := scope) (fuel := packet.header.readFuel)
      (solved := (context compiled.indexed input.prepared.named).solvedRequirements)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      headers (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      («prefix» (compiled := compiled) input.prepared.named) scope id lowered

/-- The receiving certificate family is fixed to this actual issued Header.
The flow theorem below is only about that same Header. -/
def certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ sourceContext => Certificate (headers := headers) packet expressionSyntax administrative sourceContext

/-- The raw Domain supplies genuine finite Source/compiler conditions at the
actual context and selected root. It contains no native or semantic child law. -/
structure Static where
  domain : ∀ sourceContext scope predecessor id lowered,
    ∀ root : RootPolicyReceipt (compiled := compiled) input.prepared.named
      (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled packet.selected.diagnostics)
      packet.selected.code packet.selected.compilation predecessor packet.header.function.source
      scope id packet.header.reasonAt lowered,
    CallableIndexedOwnedPreparedRawCompilerHeads.Domain
      (sourceContext := sourceContext) (scope := scope) (readFuel := packet.header.readFuel)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence) headers
  syntaxTree : GenericImperativeMatch.Syntax packet.header.function.source
    (expressionSyntax packet.header) packet.header.context
    (.statements true packet.header.function.body) packet.header.function.resultType

/-- Actual child acceptance manufactures its exact contextual root. One raw
compiler induction supplies its Tree; both native witnesses are forwarded. -/
theorem children (static : Static (headers := headers) packet expressionSyntax) :
    CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) (header := packet.header) (administrative := administrative) where
  syntaxTree := static.syntaxTree
  expressions := by
    intro sourceContext closed residual signatures scope fuel id node lowered declarations allowed found typed accepted
      nativeType fixedNativeType nativeTyped fixedTyped
    obtain ⟨predecessor, _fuel, ⟨root⟩⟩ :=
      CallableIndexedOwnedPreparedHeaderRootPolicyReceipts.at_accepted (prepared packet) packet.aligned accepted
    have actual : CallableIndexedOwnedPreparedPrincipalCompilerChildren.AcceptedAt
        root (fun _ id => expressionSyntax packet.header id) packet.header.readFuel
        (source input.prepared.named) sourceContext scope id lowered := by
      rw [← source packet]
      exact .intro found typed allowed declarations closed residual signatures root.selected.accepted
    have unique : NodeOccurrencesUnique (source input.prepared.named) := by
      rw [← source packet]
      exact packet.header.unique
    have tree := CallableIndexedOwnedPreparedRawCompilerHeads.tree_of_accepted
      (sourceContext := sourceContext) (scope := scope) (readFuel := packet.header.readFuel)
      root (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence) headers
      (static.domain sourceContext scope predecessor id lowered root) unique actual
    refine ⟨predecessor, root, tree, ⟨nativeType, nativeTyped⟩, ⟨fixedNativeType, ?_⟩⟩
    simpa only [packet.aligned.named, CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued] using fixedTyped

/-- The paired extraction's genuine coupled output constructs the rich
profile, retaining this child certificate family and the selected issuer. -/
def of_collected
    (extraction : CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Receipt
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) (administrative := administrative)
      (prepared packet) (issuer packet).typing.2 (assignments_prepared packet)) :
    CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
      (certificates := certificates (headers := headers) packet expressionSyntax administrative)
      (expressionSyntax := expressionSyntax) packet.header administrative :=
  CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.of_collected packet extraction

private theorem eligible_at
    {caller : Header compiled} {named : Named} {index : Nat}
    (member : caller ∈ headers) (same : caller.named = named)
    (selected : CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.SelectedReceipt compiled named index) :
    CallableIndexedOwnedPreparedEligibleSelectedNativeFamilyFlowStep.Eligible (headers := headers)
      selected (.ordinary caller) (some caller.function.evidence) caller.function.evidence := by
  cases same
  exact .ordinary member selected (some caller.function.evidence) rfl

section Meaning
variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (member : packet.header ∈ headers)

include member in
/-- The semantic E hypothesis is consumed at the same literal root and actual
administrative context. It is separate from every static certificate. -/
theorem preserves_children (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    ∀ sourceContext, Validity packet.header sourceContext →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (bridge (headers := headers) owner packet.header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          sourceContext packet.header.function.evidence packet.header.function.source
          (Certificate (headers := headers) packet expressionSyntax administrative sourceContext) faults size) := by
  intro sourceContext valid size within scope id lowered certified
  obtain ⟨predecessor, root, tree⟩ := certified
  have actualValid : CompatibleRuntimeContextValidity.Valid
      (context compiled.indexed input.prepared.named).solvedRequirements sourceContext packet.header.function.evidence := by
    change CompatibleRuntimeContextValidity.Valid
      input.prepared.named.specialized.function.solvedRequirements sourceContext packet.header.function.evidence
    have actual := valid.1
    change CompatibleRuntimeContextValidity.Valid packet.header.solved sourceContext packet.header.function.evidence at actual
    rw [packet.aligned.solved] at actual
    exact actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source input.prepared.named) := by
    rw [← source packet]
    exact valid.2
  have meaning : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionPreserves
      (headers := headers) (registry := registry) (faults := faults) functions packet.selected root
      (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      packet.header.readFuel
      (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (.ordinary packet.header) owner sourceContext packet.header.function.evidence size :=
    expressions packet.selected root (fun _ id => expressionSyntax packet.header id)
    (some packet.header.function.evidence) packet.header.readFuel
    (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
    (.ordinary packet.header) owner sourceContext packet.header.function.evidence
    (eligible_at member packet.aligned.named packet.selected) actualValid runtime size within
  unfold CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionPreserves at meaning
  rw [← source packet] at meaning
  intro node
  exact meaning scope tree (node := node)

include member in
/-- Reflection consumes the independent strict native E grade at this same
child and preserves its returned Source grade and reached caller. -/
theorem reflects_children (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    ∀ sourceContext, Validity packet.header sourceContext →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (bridge (headers := headers) owner packet.header)
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          sourceContext packet.header.function.evidence packet.header.function.source
          (Certificate (headers := headers) packet expressionSyntax administrative sourceContext) faults size) := by
  intro sourceContext valid size within scope id lowered certified
  obtain ⟨predecessor, root, tree⟩ := certified
  have actualValid : CompatibleRuntimeContextValidity.Valid
      (context compiled.indexed input.prepared.named).solvedRequirements sourceContext packet.header.function.evidence := by
    change CompatibleRuntimeContextValidity.Valid
      input.prepared.named.specialized.function.solvedRequirements sourceContext packet.header.function.evidence
    have actual := valid.1
    change CompatibleRuntimeContextValidity.Valid packet.header.solved sourceContext packet.header.function.evidence at actual
    rw [packet.aligned.solved] at actual
    exact actual
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      sourceContext (source input.prepared.named) := by
    rw [← source packet]
    exact valid.2
  have meaning : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionReflects
      (headers := headers) (registry := registry) (faults := faults) functions packet.selected root
      (fun _ id => expressionSyntax packet.header id) (some packet.header.function.evidence)
      packet.header.readFuel
      (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (.ordinary packet.header) owner sourceContext packet.header.function.evidence size :=
    expressions packet.selected root (fun _ id => expressionSyntax packet.header id)
    (some packet.header.function.evidence) packet.header.readFuel
    (SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
    (.ordinary packet.header) owner sourceContext packet.header.function.evidence
    (eligible_at member packet.aligned.named packet.selected) actualValid runtime size within
  unfold CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionReflects at meaning
  rw [← source packet] at meaning
  intro node
  exact meaning scope tree (node := node)
end Meaning

section Flows
variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : CallableIndexedOwnedPreparedCatalogNamedProfiles.Profile
    (certificates := certificates (headers := headers) packet expressionSyntax administrative)
    (expressionSyntax := expressionSyntax) packet.header administrative)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (member : packet.header ∈ headers)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : profile.receiving.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep profile.receiving.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token,
    EmittedDiagnosticTokenPlan.UnaryRep profile.receiving.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity packet.header context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context)
      (certificates := certificates (headers := headers) packet expressionSyntax administrative packet.header)
      (administrative := SourceCoreCompatibleCatalog.packTypes (packet.header.bindings.map Prod.snd) :: administrative)
      (factory := profile.factory) (faults := faults) (registry := registry) profile.receiving
      (bridge (headers := headers) owner packet.header) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets member in
/-- The original named preservation producer is invoked once with child
meaning derived from the shared E induction at this selected packet. -/
theorem preserves_flow [FunctionCalls.FaultTokens faults] (budget : Nat)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves (headers := headers) (registry := registry) (faults := faults) functions owner profile) :=
  CallableIndexedOwnedPreparedCatalogNamedFlowStep.preserves_flow profile owner functions extension
    faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget
    (preserves_children packet expressionSyntax administrative functions owner member budget expressions)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets member in
/-- Reflection invokes the same original producer once, retaining its strict
native budget and independent Source grade. -/
theorem reflects_flow [FunctionCalls.FaultTokens faults] (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressions : CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies.ExpressionsReflects
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions budget) :
    Below budget
      (FlowReflects (headers := headers) (registry := registry) (faults := faults) functions owner profile) :=
  CallableIndexedOwnedPreparedCatalogNamedFlowStep.reflects_flow profile owner functions extension
    faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes
    (reflects_children packet expressionSyntax administrative functions owner member budget expressions)
end Flows

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEligibleExpressionFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies
/-! The literal finite issued Header and a genuine bootstrap owner construct
rich profiles through the paired enclosing-code collector. Both child native
contexts remain available to the static certificate factory. Diagnostic tokens
are derived by the existing finite issuer bridge; no completed body law or
caller-supplied Profile is a static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedNamedDiagnosticSources
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled → ExpressionId → Prop}
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (origin : NamedOwner (headers := headers) keys functions registry)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (children : ∀ administrative, CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (header := packet.header) (administrative := administrative))

include accepted nativeMember complete wellFormed children in
/-- One genuine parameter entry drives one paired extraction. The returned
rich Profile keeps the original actual administrative context and issuer. -/
theorem profiles :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions origin.owner (header := packet.header)) := by
  refine ⟨?_⟩
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  have captureZero := origin.capture_zero
  rw [captureZero] at entry
  let extraction := Classical.choice (CallableIndexedOwnedPreparedPairedNamedProfileExtraction.extract_at
    (prepared packet) packet.aligned (issuer packet).typing.2 (assignments_prepared packet)
    accepted nativeMember functions origin.owner complete entry wellFormed (children administrative))
  exact CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.of_collected packet extraction

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds
/-! The actual Origin packet supplies Globals at its original caller bridge.
Literal finite issued rows and paired compiler children construct every rich
named profile at the real parameter entry. The genuine bootstrap owner proves
zero prefix and global count. Named leaves retain the original optional
caller dictionary and consume only the strict body induction family. No
completed Profile, body law or weak-model inverse is a static input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedCanonicalFlowBounds (Origin)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds (SourceFlows NativeFlows CallerEvidence)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (inputs : List (Input compiled))
  (rows : Inventory inputs)


variable {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (seed : NamedOwner (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) keys functions registry)
  (sameOwner : seed.owner = owner)
  (origin : Origin compiled)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
  (staticChildren : ∀ {input} (packet : Issued input), Inventory.HasRow packet rows → ∀ administrative,
    CallableIndexedOwnedPreparedPairedNamedProfileExtraction.Children
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (header := packet.header) (administrative := administrative))

include wellFormed accepted nativeMember complete staticChildren in
private theorem profiles_exists (header)
    (member : header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions seed.owner (header := header)) := by
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact CallableIndexedOwnedPreparedPairedCatalogNamedProfileFamilies.profiles
    (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    packet accepted nativeMember functions seed complete wellFormed (staticChildren packet retained)

include wellFormed accepted nativeMember complete staticChildren in
private theorem profiles :
    Nonempty (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
        functions seed.owner (header := header)) := by
  refine ⟨?_⟩
  intro header member arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  let chosen := @Classical.choice _ (profiles_exists (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren) header member)
  exact chosen entry

private theorem layouts :
    ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      header.layouts = compiled.indexed.layouts := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact packet.aligned.layouts

include staticChildren in
private theorem syntaxTree :
    ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      GenericImperativeMatch.Syntax header.function.source (expressionSyntax header)
        header.context (.statements true header.function.body) header.function.resultType := by
  intro header member
  obtain ⟨input, packet, retained, same⟩ := rows.mem_headers header member
  subst header
  exact (staticChildren packet retained []).syntaxTree

variable {named : CallableIndexedNamedGeneration.Named}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  (evidence : Dynamic.EvidenceEnvironment)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context
    (CallableIndexedNamedGeneration.source named))
  (covers : evidence.Covers context)
  (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (sameEvidence : CallerEvidence callerEvidence evidence)

local notation "bridge" => Origin.bridge (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin owner
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "calls" => RecursiveNamedCallEvidenceHeads.Calls (prepared := compiled.indexed.ancestry)
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
  callerEvidence (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (CallableIndexedNamedGeneration.context compiled.indexed named)
  (CallableIndexedNamedGeneration.source named) context certificate

include wellFormed accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- The same real named call leaf preserves the original caller protocol and
returned pool. Profiles are constructed from finite issuer-aligned children. -/
theorem preserves_calls (idsUnique : RequirementIdsUnique context)
    (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) → SourceFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  obtain ⟨issuedProfiles⟩ := profiles (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren)
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.preserves_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin seed.owner)
    wellFormed runtime covers unique idsUnique (layouts (rows := rows))
    (syntaxTree (rows := rows) (staticChildren := staticChildren))
    issuedProfiles
    wellFormed.function_ids callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

include wellFormed accepted nativeMember seed sameOwner complete staticChildren runtime covers unique sameEvidence in
/-- Reflection keeps the independent Source grade returned by the actual typed
finish and restores the original complete caller packet. -/
theorem reflects_calls (budget size : Nat) (within : size ≤ budget)
    (children : Below budget (CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence (CallableIndexedNamedGeneration.source named) certificate faults))
    (bodies : ∀ header, header ∈ (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) → NativeFlows (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) (keys := keys)
      (owner := owner) (functions := functions) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) header budget) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge model context evidence
      (CallableIndexedNamedGeneration.source named) calls faults size := by
  cases sameOwner
  obtain ⟨issuedProfiles⟩ := profiles (wellFormed := wellFormed) (inputs := inputs) (rows := rows)
    (accepted := accepted) (nativeMember := nativeMember) (functions := functions)
    (seed := seed) (complete := complete) (staticChildren := staticChildren)
  have original := CallableIndexedOwnedPreparedCatalogTypedNamedCallBounds.reflects_calls
    (functions := functions) (faults := faults) (owner := seed.owner) (captureZero := seed.capture_zero)
    (compilation := CallableIndexedNamedGeneration.context compiled.indexed named)
    (source := CallableIndexedNamedGeneration.source named) (context := context) (certificate := certificate)
    (globals := fun header member => seed.globals member) evidence
    (CallableIndexedOwnedPreparedOriginGlobalsCarriers.carrier (headers := (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)) origin seed.owner)
    wellFormed runtime covers unique (layouts (rows := rows))
    (syntaxTree (rows := rows) (staticChildren := staticChildren))
    issuedProfiles
    callerEvidence sameEvidence budget size within
  cases origin <;> exact @original children bodies

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedOriginNamedCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedSelectedAssociationFlowBounds
/-! The shared paired E family supplies the actual retained closure F.
Only the literal prefix specialization is passed to the original association
producer. Strict Source and native grades stay independent; no arbitrary
call-leaf semantics or completed body law is added to a static receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedSelectedAssociationFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedNativeDirectCellOrigins (Association)
open CallableIndexedOwnedPreparedSelectedNativeFamilyQualification (facet)
open CallableIndexedOwnedPreparedEligiblePairedExpressionFamilies
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (receiving : CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.Receivings
    (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
    (registry := registry) (faults := faults) functions extension)

include faithful observations wellFormed receiving in
/-- Paired E through n constructs the same selected closure F through n. -/
theorem preserves_at_most [FunctionCalls.FaultTokens faults] (budget : Nat)
    (expressions : ExpressionsPreserves (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ∀ {mapping world function native bindings parameter result}
      (member : Association (facet headers) headers keys bodyRegistry faults
        mapping world function native bindings parameter result),
      RecursiveNamedHeaderContracts.AtMost budget
        (CallableIndexedOwnedPreparedDirectLambdaInvocationBounds.FlowPreserves
          functions member (registry := registry)) :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.preserves_at_most
    functions extension faithful observations wellFormed receiving budget
    (preserves_at_prefix functions expressions)

include faithful observations wellFormed receiving in
/-- The dispatcher receives only strict F from smaller shared E budgets. -/
theorem preserves_below [FunctionCalls.FaultTokens faults] (budget : Nat)
    (expressions : ∀ child, child < budget → ExpressionsPreserves
      (headers := headers) (keys := keys) (registry := registry) (faults := faults) functions child) :
    ClosurePreservesBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.preserves_below
    functions extension faithful observations wellFormed receiving budget
    (fun child smaller => preserves_at_prefix functions (expressions child smaller))

include faithful observations wellFormed receiving in
/-- Strict native E constructs strict F with its own recovered Source grade. -/
theorem reflects_below [FunctionCalls.FaultTokens faults] (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (expressions : ExpressionsReflects (headers := headers) (keys := keys)
      (registry := registry) (faults := faults) functions budget) :
    ClosureReflectsBelow (qualification := facet headers) (headers := headers)
      (keys := keys) (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      functions budget :=
  CallableIndexedOwnedPreparedEligibleSelectedAssociationFlowBounds.reflects_below
    functions extension faithful observations wellFormed receiving budget functionTypes
    (reflects_at_prefix functions expressions)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPairedSelectedAssociationFlowBounds
end
