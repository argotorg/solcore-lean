import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues

/-! One prior function export keeps its original handle, raw Source type,
independent Source value and exact native payload. Its validation budget is
the budget of that export, independent of later input-validation budgets. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
open Core Frontend SourceInference

structure Entry where
  sourceType : TypeSystem.Ty
  source : Dynamic.Value
  handle : SourceCorePublicValues.Handle
  native : Core.Value
  nativeType : Core.Ty
  fuel : Nat

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
