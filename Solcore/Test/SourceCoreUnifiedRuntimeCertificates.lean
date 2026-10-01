import Solcore.Frontend.SourceCoreUnifiedRuntimeCertificates

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceTypedRuntime.runDeepCertifiedWithValidationFuel

/-! Actual-request certificates use public run/resume equations. Neither source
execution witnesses nor caller-supplied plan equality/BEq assumptions are used. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedRuntimeCertificates
open Solcore Solcore.Frontend SourceInference SourceCoreUnifiedRuntime

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared} {execution : Execution prepared}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (produced : result.execution = some execution) :
    execution.root.entry.key = key ∧ execution.arguments = arguments ∧
      execution.validationFuel = validationFuel ∧ execution.initial = initial :=
  run_execution_request ran produced

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel : Nat}
    {initial : SourceState} {result : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : result.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  run_done_certificate ran selected done

example {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {key : Key} {arguments : List SourceValue} {validationFuel executionFuel resumeFuel : Nat}
    {initial : SourceState} {result resumed : Result prepared} {value : SourceValue} {final : SourceState}
    {specialized : SourceSpecialization.SpecializedFunction}
    (ran : SourceCoreUnifiedRuntime.run prepared key arguments validationFuel executionFuel initial = .ok result)
    (continued : result.resume resumeFuel = .ok resumed)
    (selected : SourceCompilationPlan.exactSpecialization program.base.validationPlan key = .ok specialized)
    (done : resumed.observation = .done value final) :
    SourceTypedRuntime.PreparedDeepExecution program.base.sourceProgram program.base.validationPlan
      (specialized.function.typedBody.inputs.map (·.scheme.body)) specialized.function.inferredBodyType
      arguments initial value final :=
  run_resume_done_certificate ran continued selected done

end Tests.SourceCoreUnifiedRuntimeCertificates
