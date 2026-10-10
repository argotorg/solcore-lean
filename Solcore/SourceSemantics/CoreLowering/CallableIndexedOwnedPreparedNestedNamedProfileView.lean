import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedDirectTypedNamedBodyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations

/-! The original actual Header collector retains the same accepted body,
flow action and static compiler Tree. This forward view copies those fields
into the nested caller interface through its honest static constructor. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {certificates : CallableIndexedOwnedFunctionValues.Header compiled program →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {runtime : Bool} {administrative : Core.Context}

/-- Static fields are copied forward from the original real compiler profile.
Neither direction of body semantics is supplied by this conversion. -/
def of_direct
    (profile : CallableIndexedOwnedDirectTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative) :
    CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile
      (certificates := certificates) (expressionSyntax := expressionSyntax) runtime header administrative :=
  CallableIndexedOwnedPreparedNestedTypedNamedBodyContinuations.Profile.of_extracted
    profile.initialValid profile.accepted profile.projection profile.generated profile.tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNestedNamedProfileView
