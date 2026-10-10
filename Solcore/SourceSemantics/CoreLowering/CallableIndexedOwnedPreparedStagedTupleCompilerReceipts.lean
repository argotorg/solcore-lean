import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleTreeBounds

/-! The original accepted compiler action constructs a finite tuple certificate.
Its actual ordered mapM children are extracted by structural syntax descent.
Leaves retain the existing read/literal/group/pair tree and literal sites.
Static policy and raw typing are independent inputs; no child meaning is a
compiler premise. A group around a new arbitrary tuple is outside this syntax. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleCompilerReceipts
open Core Frontend SourceInference

/-- Only actual original source syntax is stored. The ordered child list may
contain repeated identifiers and any finite arity. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | leaf {id} (tree : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | tuple {id node ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id

/-- These are exact static policy results on the supported source occurrences.
They contain no runtime trace or desired certificate/meaning conclusion. -/
structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

private theorem product_policy {policy compilation readFuel values source scope reasonAt}
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt) :
    CompatibleExpressionProducts.PolicyFor policy compilation readFuel values source scope reasonAt :=
  ⟨fun id tree => policyFor.special id (.leaf tree),
   fun id tree => policyFor.read id (.leaf tree), policyFor.lower, policyFor.leaf⟩

/-- One genuine successful action constructs every reached child's static
receipt internally. The runtime fold consumes this same positive certificate. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node →
      node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    CallableIndexedOwnedPreparedStagedTupleTreeBounds.Certificate
      readFuel values source context compilation.solvedRequirements reasonAt scope id lowered := by
  induction syntaxTree generalizing node fuel lowered with
  | leaf tree =>
      exact .leaf (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions
        unique declarations (product_policy policyFor)
        (fun id node tree found => coercions id node (.leaf tree) found)
        tree found typed accepted)
  | tuple originalFound form children ih =>
      cases fuel with
      | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
      | succ fuel =>
          exact RecursiveStageTupleMeaning.of_functions_with_leaves
            (CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate
              readFuel values source context compilation.solvedRequirements reasonAt)
            unique found (by
              have same := Option.some.inj (originalFound.symm.trans found)
              cases same
              exact form) typed
            (policyFor.special _ (.tuple originalFound form children))
            (policyFor.read _ (.tuple originalFound form children)) policyFor.leaf accepted
            (fun child member childNode code childFound childTyped childAccepted =>
              ih child member childFound childTyped childAccepted)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleCompilerReceipts
