import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorMethodAuthority
import Solcore.SourceSemantics.CoreLowering.CallableCoercionSpineCertificates

/-! A coercion port retains the actual ordered compiler step and selected Source
method. Parameter entry and method execution use the shared physical family. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
open Core Frontend SourceInference

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {compilation : SourceCoreFunctions.Context}
  {caller : SourceSpecialization.SpecializedFunction}
  {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {scope : SourceCoreBasic.Scope} {node : ExpressionNode}
  {policy : SourceCoreFunctions.CallablePolicy}
  {input output : SourceCoreBasic.LoweredExpr} {coercion : CoercionStep}
  {call : CallableCoercionSpine.Call}
  (step : CallableCoercionSpine.Step compiled.sourceProgram project compilation caller available
    scope node policy input coercion output call)

structure Port (context : SourceSemantics.Context) (callerEvidence : Dynamic.EvidenceEnvironment)
    (stages : Staging.Recursive.Registry) where
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled step.method
  signature : principal.named.signature = call.signature
  slot : principal.cached.index = step.globalIndex
  parameters : principal.named.inputs.map (fun binding => binding.1.scheme.body) = [coercion.source]
  result : principal.sourceBody.resultType = coercion.target
  selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context callerEvidence "Coerce" "coerce" coercion.requirements principal.sourceBody principal.dictionary
  agrees : ∀ sourceBody dictionary,
    Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
      context callerEvidence "Coerce" "coerce" coercion.requirements sourceBody dictionary →
      sourceBody = principal.sourceBody ∧ dictionary = principal.dictionary
  child : Staging.Recursive.Scope
  staged : stages.Closure principal.sourceFunction child
  diagnostics : ∃ diagnostics : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
    compiled.indexed.base.diagnostics = some diagnostics ∧
    principal.cached.diagnostics = match compiled.indexed.base.callableContext with
      | none => diagnostics.program
      | some native => {diagnostics.program with rootTable := native.diagnostics.rootTable}
  resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
    compiled.sourceProgram principal.named.specialized principal.dictionary
  sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
    (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionAuthority
