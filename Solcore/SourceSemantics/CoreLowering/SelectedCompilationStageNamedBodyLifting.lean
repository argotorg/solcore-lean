import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedTerminalLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedScopedLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedBodySupport

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open SelectedCompilationPhysicalNamedBodySupport (Support)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageLiftBounds
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
  {semanticFaults : FunctionCalls.FaultRep}

variable {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {body : Body header}
  (support : Support (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
    (semanticFaults := semanticFaults) header body)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {faults : RecursiveStageMeaning.FaultRep}
  {child : Staging.Recursive.Scope} (selected : stages.Closure header.function child)
local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled receiving
    (fun reason token => faults (.semantic reason) token))

include support profile certified extension selected semantic assignmentInterpretation in
theorem lifts {budget : Nat}
    (children : ∀ size, size < budget →
      LiftsRootsAt
        (headers := headers) (keys := keys) model stages semanticFaults size)
    (preservation : ∀ size, SelectedCompilationMixedRootBounds.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults faults size) :
    NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget := by
  cases support with
  | terminal terminal static =>
    exact SelectedCompilationStageNamedTerminalLifting.lifts
      static selected certified children
  | formation terminal static globals =>
    exact SelectedCompilationStageNamedTerminalLifting.formation selected static
  | «scoped» body receipt compilation static =>
    exact SelectedCompilationStageNamedScopedLifting.lifts (semantic := semantic) (assignmentInterpretation := assignmentInterpretation)
      static body.aligned.globals functions (CallableIndexedLambdaValues.identity_faithful compiled.indexed) (CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
      selected extension body.layouts children preservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedBodyLifting
