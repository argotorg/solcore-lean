import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentDiagnosticAuthorityReception
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedCallerFamily

/-! The closed physical mixed family supplies named body ports for actual
terminal expressions, genuine lambda formation or scoped statements at every reached registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open SelectedCompilationPhysicalMixedCallerFamily (MethodSupports MixedMethodSupports)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (SelectedCompilationPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : SelectedCompilationPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    SelectedCompilationPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPreparedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    SelectedCompilationPhysicalClosureStaticSupport.SupportFor association stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
theorem preserves_with_methods
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport mixedMethodSupport in
theorem reflects_with_methods (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.reflects_with_methods
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners mixedMethodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
theorem preserves_with_bodies
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.preserves (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.preserves_with_bodies
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport methodSupport in
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  exact SelectedCompilationPhysicalNamedBodySupport.reflects (semantic := semantic)
        (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
    (bodySupport header member) profile (certificates header member) extension selected
    (fun size _ => SelectedCompilationPhysicalMixedCallerFamily.reflects_with_bodies
      receiver stagePrepared profile bodyTyping certificates observations extension semantic bodies bodySupport
      closurePackets closureSupport owners methodSupport stageEq size)

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem preserves
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  preserves_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport header member selected budget

include closurePackets closureSupport owners receiver stagePrepared profile bodyTyping certificates observations extension semantic terminals namedSupport methodSupport in
/-- The previous terminal family keeps its original public body-port API. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  reflects_with_bodies receiver stagePrepared profile bodyTyping certificates observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => SelectedCompilationPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq header member selected budget

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalMixedNamedFamilyPorts
