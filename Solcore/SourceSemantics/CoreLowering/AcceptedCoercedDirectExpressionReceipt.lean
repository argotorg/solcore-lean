import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTree

/-! A nonempty original coercion suffix forces the genuine evidence branch.
The resulting receipt retains its complete selected call and ordered children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child Supported)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

local notation "policy" => root.selected.policy
local notation "body" => root.selected.lowerBody
local notation "current" => context compiled.indexed named

theorem of_head {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {lowered : SourceCoreBasic.LoweredExpr}
    (head : Head policy body fuel current source scope id reasonAt lowered)
    (form : head.node.form = .call callee arguments (.declaration instantiation))
    (supported : Supported (current).plan instantiation)
    (coercions : head.node.coercions ≠ [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (current).owner ∧ binding.initializer = id)) = none) :
    Nonempty (CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) head.node lowered) := by
  cases selected : head.special with
  | none =>
    have actual : specialAction policy body fuel current source scope id reasonAt = .ok none :=
      head.selected.trans (congrArg Except.ok selected)
    obtain ⟨receipt⟩ := AcceptedDirectExpressionReceipt.of_supported
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      head.found form supported actual
      (AcceptedNamedExpressionPolicy.direct_read root.compilerPolicy head.found form) head.accepted
    have same := Option.some.inj (receipt.metadata.found.symm.trans head.found)
    exact False.elim (coercions (same ▸ receipt.metadata.coercions))
  | some output =>
    have same := head.result output selected
    have selected' : head.special = some lowered := selected.trans (congrArg some same.symm)
    have actual : specialAction policy body fuel current source scope id reasonAt = .ok (some lowered) :=
      head.selected.trans (congrArg Except.ok selected')
    have extracted := AcceptedContextualDirectReceipt.of_special compilation root.compilerPolicy
      head.found form actual
    cases extracted with
    | inl receipt => exact receipt
    | inr initializers =>
      obtain ⟨initializer⟩ := initializers
      have found := initializer.found
      rw [ordinary] at found
      cases found

/-- Each leaf is matched to its own successful action in the full ordered
argument list, at the actual predecessor budget. -/
theorem children {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {reasonAt : ExpressionId → Word}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableCoercionExpressionCertificates.Direct compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) node lowered)
    (forms : ∀ argument ∈ arguments, ∃ node,
      source.lookupExpression? argument = some node ∧ LeafForm node.form) :
    ∀ argument ∈ arguments,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        source argument (fun _ => False) := by
  intro argument member
  obtain ⟨code, present⟩ := (mapM_receipt receipt.argumentsAccepted).2.2 argument member
  have generated := (mapM_receipt receipt.argumentsAccepted).2.1 (argument, code) present
  have accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel current
      source scope argument reasonAt = .ok code := by
    simpa only [Child, Nat.min_eq_right (Nat.le_succ fuel)] using generated
  cases fuel with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted; cases accepted
  | succ predecessor =>
    obtain ⟨head⟩ := Head.of_accepted accepted
    obtain ⟨original, found, form⟩ := forms argument member
    have same := Option.some.inj (head.found.symm.trans found)
    have leaf : LeafForm head.node.form := same ▸ form
    rcases leaf.view with literal | ⟨name, binder, read⟩
    · exact .leaf (.literal head.found literal)
    · exact .leaf (.read head.found read)

end Solcore.SourceSemantics.CoreLowering.AcceptedCoercedDirectExpressionReceipt
