import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeSourceTreeLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSourceLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareImperativeBodyProducer

/-! The accepted body supplies all lifting evidence internally. Ordinary Source
execution may stop at an actual selected-stage rejection at its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceBodyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole (Program.ofChecked whole.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole (Program.ofChecked whole.sourceProgram))}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key = .ok named.specialized)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : whole.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver whole.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt whole.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry
    completion.result.context.registry)
  {invocation : Staging.Recursive.Scope}
  (authority : CellAwareNamedCallPorts.Authority (compiled := whole) named invocation)
  (wellFormed : ProgramWellFormed (Program.ofChecked whole.sourceProgram))

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry functions
local notation "stages" => SelectedCompilationPhysicalProgramSupport.stages whole
local notation "faults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "program" => Program.ofChecked whole.sourceProgram

variable
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel whole.compatible.checked completion.result.context.registry
        (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile))
      (GeneralizedLocalInstanceValues.model whole.indexed)))
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)


include bindings transport record receiver extension authority wellFormed registered in
theorem lifts
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context : SourceSemantics.Context} {expected : TypeSystem.Ty}
    (body : CellAwareImperativeBodyProducer.Body compiled (CellAwareNamedBodyProducer.Certificate compiled)
      administrative context expected)
    (issuer : CellAwareNamedDiagnosticIssuer.Named whole.indexed named (diagnostics.reasonAt named.signature.key))
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt whole.indexed diagnostics) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context
      (CellAwareImperativeBodyProducer.scope named) true compiled.statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime
  exact CellAwareImperativeSourceTreeLifting.lifts bridge bindings transport functions extension compiled record producer registered
    (fun _ _ represented => CallableIndexedOwnedIssuedAssignmentRecipes.operands compiled issued receiver represented)
    (CallableIndexedLambdaValues.identity_faithful whole.indexed) (CellAwarePhysicalFunctionOrigins.observations profile)
    (CellAwareNamedAssignmentDiagnostics.ready record runtime.graph.nodeOccurrencesUnique issued receiver functions protocol)
    (fun related => CompatibleExpressionPrimitives.bool_fields related) (fun _ _ => .unit)
    (fun childContext childRuntime childCovers childLedger size =>
      CellAwareNamedExpressionSourceLifting.lifts compiled bridge profile receiver extension authority sourceEq issuer
        record childLedger (by simpa only [sourceEq] using childRuntime) wellFormed childCovers size)
    (fun childContext childRuntime childCovers childLedger size =>
      CellAwareNamedExpressionMeaning.preserves compiled bridge profile receiver extension authority sourceEq issuer
        record childLedger (by simpa only [sourceEq] using childRuntime) wellFormed childCovers size)
    sourceEq body.tree issuer (size := size) environments heaps locals agrees actualTyped runtime

end Solcore.SourceSemantics.CoreLowering.CellAwareImperativeNamedSourceBodyLifting
