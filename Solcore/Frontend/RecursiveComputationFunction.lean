import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation

/-! Concrete entry operations and independent provenance select the recursive
child. Shared laws are applied directly; old explicit endpoints are unchanged. -/

set_option autoImplicit false

namespace Solcore.Frontend

abbrev RecursiveComputationFunctionCompiles :=
  ComputationFunctionCompiles RecursiveLocalComputationElaborates

abbrev RecursiveComputationFunctionPrepares :=
  ComputationFunctionPrepares RecursiveLocalComputationElaborates

abbrev compileRecursiveComputationFunction? :=
  compileComputationFunction? elaborateRecursiveLocalComputation?

abbrev prepareRecursiveComputationFunction? :=
  prepareComputationFunction? elaborateRecursiveLocalComputation?

abbrev runRecursiveComputationFunction? :=
  runComputationFunction? elaborateRecursiveLocalComputation?

end Solcore.Frontend
