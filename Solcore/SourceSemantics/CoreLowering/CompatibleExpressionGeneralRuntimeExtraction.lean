import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntime

/-! Actual Functions compilation supplies the existing General Tree and its
same-tree literal support. Only visited compiler leaves require numeric row
receipts; the original complete ledger and unused templates remain untouched.
Source typing, ordinary policy, constructor formation and runtime environment
conditions remain independent. Contextual dispatch, calls, lambdas and output
coercions are separate interfaces. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
open Core Frontend SourceInference
open CompatibleExpressionGeneral

/-- The single compiler extraction retains actual numeric validator results
at every literal child. No external child certificate or execution law remains. -/
theorem of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {sourceContext : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (signatures : sourceContext.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (Syntax source))
    (policyFor : PolicyFor policy context readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope id reasonAt = .ok lowered) :
    CompatibleExpressionGeneralRuntime.Certificate readFuel values source sourceContext context.solvedRequirements reasonAt scope id lowered := by
  apply CompatibleExpressionGeneral.tree_of_functions_with_literals
    (fun _ id code => CompatibleExpressionLiteralRuntime.Certificate context.solvedRequirements source id code)
    ?_ unique declarations signatures constructorValid policyFor coercions syntaxTree found typed accepted
  intro child childNode childFuel childCode childFound atomic unitType special readPolicy leafPolicy generated
  have receipt := CompatibleExpressionLiteralRuntime.of_functions childFound atomic unitType special readPolicy leafPolicy generated
  exact ⟨receipt.forget, receipt⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionGeneralRuntimeExtraction
