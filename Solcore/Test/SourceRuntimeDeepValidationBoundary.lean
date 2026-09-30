import Solcore.Frontend.SourceRuntimeDeepValidation

/-! Core adapters can validate source heaps, captures and checked-code
provenance without acquiring a source execution entry point. Uninitialized
cells remain admissible, including opaque initial heap cells. -/

namespace Tests.SourceRuntimeDeepValidationBoundary
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open SourceTypedRuntime

#check Value.HasDeepTypeFuel
#check Value.HasPlanCode
#check RuntimeState.isDeeplySafe
#check RuntimeState.isDeeplySafe_sound
#check ClosureCodeAndEvidenceValid
#check InstantiatedLocalEvidenceValid
#check RuntimeSourceImage
#check PreparedDeepExecution

example (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan) :
    ({ heap := [{ type := .error, value := none }] } : RuntimeState).isDeeplySafe
      0 signatures plan = true := by
  rfl

example (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan) :
    ({ heap := [{ type := .error, value := none }] } : RuntimeState).HasDeepTypes
      signatures plan := by
  have accepted :
      ({ heap := [{ type := .error, value := none }] } : RuntimeState).isDeeplySafe
        0 signatures plan = true := rfl
  exact (RuntimeState.isDeeplySafe_sound accepted).hasDeepTypes

example (raw : TypeSystem.Ty) :
    defaultValue? 1 (.proxy raw) = some (.proxy raw) := rfl

example (rawKey rawValue : TypeSystem.Ty) :
    defaultValue? 1 (.mapping rawKey rawValue) =
      some (.mapping rawKey rawValue []) := rfl

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.invokeSpecialization
#check_failure Solcore.Frontend.SourceTypedRuntime.evaluate
#check_failure Solcore.Frontend.SourceTypedRuntime.executeStatement
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

end Tests.SourceRuntimeDeepValidationBoundary
