import Solcore.Frontend.Current

/-! The current public frontend exposes Core invocation and pure source
boundary certificates without exporting the historical source evaluator. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runTrusted
#check_failure Solcore.Frontend.SourceTypedRuntime.runWithValidationFuel
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

#check Solcore.Frontend.SourceCoreUnifiedCompilation.prepare
#check Solcore.Frontend.SourceCoreUnifiedCompilation.Compiled.run
#check Solcore.Frontend.SourceCompiler.CompiledEntry.runTypedWithCheckpoint
#check Solcore.Frontend.SourceCompiler.CompiledEntry.TypedCheckpoint.resume
#check Solcore.Frontend.SourceTypedRuntime.Value.HasPreparedType
#check Solcore.Frontend.SourceTypedRuntime.PreparedDeepExecution
#check Solcore.Frontend.SourceTypedRuntime.checkedLambdaNode_provenance
#check Solcore.Frontend.SourceTypedRuntime.closure_hasPlanCode_checkedLambdaNode
#check Solcore.Frontend.SourceTypedRuntime.exactSpecialization
#check Solcore.Frontend.SourceTypedRuntime.validateExecutablePlan
#check Solcore.Frontend.SourceTypedRuntime.prepareExecutablePlanEvidence
