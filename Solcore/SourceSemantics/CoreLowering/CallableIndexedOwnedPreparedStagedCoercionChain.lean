import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineEvaluation

/-! An ordered conversion certificate retains each actual compiler step and
its independent Source method selection, together with raw endpoint typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedCoercionAuthority (Port)

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  (project : SourceCoreEvidence.Projector) (compilation : SourceCoreFunctions.Context)
  (caller : SourceSpecialization.SpecializedFunction)
  (available : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  (scope : SourceCoreBasic.Scope) (node : ExpressionNode)
  (policy : SourceCoreFunctions.CallablePolicy)
  (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
  (stages : Staging.Recursive.Registry)

inductive Chain : TypeSystem.Ty → TypeSystem.Ty → SourceCoreBasic.LoweredExpr →
    List SourceInference.CoercionStep → SourceCoreBasic.LoweredExpr → List CallableCoercionSpine.Call → Type where
  | nil {source input} : Chain source source input [] input []
  | cons {coercion target input middle output rest call calls}
      (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
        scope node policy input coercion middle call)
      (port : Port step context invocation.evidence stages)
      (valid : CoercionStepValid context coercion)
      (tail : Chain coercion.target target middle rest output calls) :
      Chain coercion.source target input (coercion :: rest) output (call :: calls)

variable {compiled project compilation caller available scope node policy context invocation stages}
  {source target : TypeSystem.Ty} {input output : SourceCoreBasic.LoweredExpr}
  {steps : List SourceInference.CoercionStep} {calls : List CallableCoercionSpine.Call}
  (chain : Chain compiled project compilation caller available scope node policy context invocation stages
    source target input steps output calls)

include chain

theorem Chain.spine : CallableCoercionSpine.Spine compiled.sourceProgram project compilation caller available
    scope node policy input steps output calls := by
  induction chain with
  | nil => exact .nil
  | cons step _ _ _ ih => exact .cons step ih

theorem Chain.valid : CoercionPathValid context source target steps := by
  induction chain with
  | nil => exact .nil _
  | cons _ _ valid _ ih => exact .cons valid ih

theorem Chain.final_type (ξ : Renaming) :
    CallableCoercionSpine.finalType input.type (calls.map (CallableCoercionSpine.Call.rename ξ)) = output.type := by
  induction chain with
  | nil => rfl
  | cons step _ _ _ ih =>
      simpa only [List.map_cons, CallableCoercionSpine.finalType, CallableCoercionSpine.Call.rename,
        step.emitted] using ih

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
