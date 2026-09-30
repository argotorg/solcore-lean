import Solcore.Frontend.SourceRuntimeValidation

/-! Core adapters can preserve the existing source input contract and result
carrier without importing any typed-source runtime execution entry point. -/

#check Solcore.Frontend.SourceTypedRuntime.Value
#check Solcore.Frontend.SourceTypedRuntime.RunResult
#check Solcore.Frontend.SourceTypedRuntime.Value.type?
#check Solcore.Frontend.SourceTypedRuntime.Value.validateTypeFuel
#check Solcore.Frontend.SourceTypedRuntime.validateInputs

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.invokeSpecialization
#check_failure Solcore.Frontend.SourceTypedRuntime.evaluateExpression
#check_failure Solcore.Frontend.SourceTypedRuntime.executeStatement
