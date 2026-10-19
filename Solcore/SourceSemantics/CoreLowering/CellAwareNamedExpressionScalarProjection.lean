import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionCertificates

/-! Scalar operand selection follows the actual emitted type. Generalized
read bundles and builtin handles have a product carrier and cannot pass the
compiler's scalar operand check. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context)
open GeneralizedLocalInitializerCompilation (namedPolicy)
open CellAwareNamedExpressionCertificates (Tree)

def Scalar (type : Core.Ty) : Prop := type = .bool ∨ type = .word ∨ type = .integer

private theorem function_not_scalar (parameter result : Core.Ty) :
    ¬ Scalar (CallableContract.functionType parameter result) := by
  simp [Scalar, CallableContract.functionType]

theorem unary_input_scalar (operator : Syntax.UnaryOp) (type : Core.Ty) :
    Scalar (CompatibleExpressionConditionals.selectedUnary operator type).operandType := by
  unfold CompatibleExpressionConditionals.selectedUnary
  split
  · simp [Scalar, UnaryOp.operandType]
  · cases operator <;> simp [Scalar, SourceCorePrimitive.unaryOperator, UnaryOp.operandType]

theorem binary_input_scalar (mode : CompatibleExpressionPrimitives.Mode) (operator : Syntax.BinaryOp) :
    Scalar (mode.operandType operator) := by
  cases mode <;> cases operator <;>
    simp [Scalar, CompatibleExpressionPrimitives.Mode.operandType,
      SourceCorePrimitive.binaryOperandType, SourceCoreInteger.binaryOperandType]

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    {compiled : Compilation prepared named diagnostics code} {rootFuel : Nat}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

theorem projected (tree : Tree compiled rootFuel source sourceContext reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (scalar : Scalar lowered.type) : checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | plain receipt => exact CompatibleExpressionPrimitives.Tree.projected (.product receipt.1) found
  | builtin receipt =>
    exact False.elim (function_not_scalar _ _ (receipt.nativeType ▸ scalar))
  | generalized receipt recipe =>
    exact False.elim (function_not_scalar _ _ (recipe.nativeType ▸ (receipt.type.symm ▸ scalar)))
  | group metadata _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | pair metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | index header _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans header.metadata.found)
    exact header.metadata.projected
  | unary metadata _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | binary metadata _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
    cases Option.some.inj (found.symm.trans metadata.found)
    exact metadata.projected
  | call compiler _ _ _ _ _ =>
    have contextual : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
        (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, compiler.found, compiler.originalForm]
    have read := compiler.read
    simp only [namedPolicy, contextual, bind, Except.bind] at read
    change SourceCoreCompatibleDataExpressions.readExpression checked source id = .ok (compiler.node, compiler.type) at read
    have metadata := CompatibleExpressionReads.metadata_of_read read
    cases Option.some.inj (found.symm.trans metadata.found)
    have nativeType : lowered.type = compiler.type := congrArg (fun output => output.type) compiler.output
    exact metadata.projected.trans (congrArg Except.ok nativeType.symm)

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionScalarProjection
