import Solcore.Frontend.SourceInference.ExpressionProperties

/-! Regression: nominal exhaustiveness must not accept an empty arm list by
vacuous quantification over an empty constructor catalog. -/

set_option autoImplicit false

namespace Tests.SourceInferenceEmptyMatchGuard

open Solcore.Frontend Solcore.Frontend.SourceInference Solcore.TypeSystem

example (context : Context) (state : State) (scrutineeType : Ty) :
    Detail.exhaustsNominalConstructors context state scrutineeType [] = false := by
  rfl

end Tests.SourceInferenceEmptyMatchGuard
