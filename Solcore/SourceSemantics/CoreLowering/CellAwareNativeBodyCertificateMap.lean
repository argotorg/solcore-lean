import Solcore.SourceSemantics.CoreLowering.CellAwareNamedBodySupport

/-! Pointwise static certificate inclusion retains every original statement,
initializer packet, marked allocation and emitted native expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
open Core Frontend SourceInference

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : SourceCoreGeneralFunctions.Function}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode}
  {first second : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {reasonAt : ExpressionId → Word}

theorem map_tree
    (included : ∀ context scope id lowered, first context scope id lowered → second context scope id lowered)
    {context scope mode statements expected type code}
    (tree : CellAwareNativeBodyTree.Tree prepared named compiled first administrative reasonAt
      context scope mode statements expected type code) :
    CellAwareNativeBodyTree.Tree prepared named compiled second administrative reasonAt
      context scope mode statements expected type code := by
  induction tree with
  | returning rest found form expressionFound valueType typed value =>
    exact .returning rest found form expressionFound valueType typed (included _ _ _ _ value)
  | tail found form expressionFound valueType typed value =>
    exact .tail found form expressionFound valueType typed (included _ _ _ _ value)
  | generalizedInitialized found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same _remaining ih =>
    exact .generalizedInitialized found form declaration polymorphic extended ordinary initializerFound initializerForm
      valueType requirements coercions site initial nativeTyped allocation annotation same ih

def map_body
    (included : ∀ context scope id lowered, first context scope id lowered → second context scope id lowered)
    {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareNamedBodySupport.Body compiled first administrative context expected) :
    CellAwareNamedBodySupport.Body compiled second administrative context expected :=
  ⟨body.flow, map_tree included body.tree, body.emitted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareNativeBodyCertificateMap
