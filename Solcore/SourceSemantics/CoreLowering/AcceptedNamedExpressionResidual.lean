import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTree

/-! A residual retains the exact accepted Header expression and a boundary
reached through its own original, ordered compiler child actions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)

structure Residual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (_directSites : DeclarationInstantiation → Prop)
    (fuel : Nat) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered
  predecessor : Nat
  sameFuel : fuel = predecessor + 1
  root : RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics prepared.code
    prepared.compilation predecessor source scope id header.reasonAt lowered
  tree : Trace root source scope header.reasonAt (predecessor + 1) id lowered
  boundary : Boundary tree

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
