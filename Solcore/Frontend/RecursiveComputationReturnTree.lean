import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.ComputationReturnTreeEvaluation
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.RecursiveLocalComputationEvaluation

/-! Concrete recursive-expression bodies instantiate the shared engine.
Their five operations and relations do not introduce parallel proof aliases. -/

set_option autoImplicit false

namespace Solcore.Frontend

abbrev elaborateRecursiveComputationReturnTree? :=
  elaborateComputationReturnTree? elaborateRecursiveLocalComputation?

abbrev RecursiveComputationReturnTreeHasType :=
  ComputationReturnTreeHasType RecursiveLocalComputationHasType

abbrev RecursiveComputationReturnTreeElaborates :=
  ComputationReturnTreeElaborates RecursiveLocalComputationElaborates

abbrev RecursiveComputationReturnTreeEvaluates :=
  ComputationReturnTreeEvaluates RecursiveLocalComputationEvaluates

abbrev RecursiveComputationReturnTreeEvaluatesWithCost :=
  ComputationReturnTreeEvaluatesWithCost RecursiveLocalComputationEvaluatesWithCost

end Solcore.Frontend
