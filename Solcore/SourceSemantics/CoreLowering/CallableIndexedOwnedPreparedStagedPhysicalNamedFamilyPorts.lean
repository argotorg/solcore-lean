import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalCallerFamily

/-! Actual ordinary named bodies obtain both physical invocation ports from
the closed numeric family. Public adapters need only the genuine static packets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
  (methodSupport : CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.MethodSupports
    (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem preserves (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.preserves
    (namedSupport header member) selected wellFormed
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.preserves
      receiver profile wellFormed observations extension semantic terminals namedSupport methodSupport size)

include receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport.reflects
    (namedSupport header member) selected wellFormed
    (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalCallerFamily.reflects
      receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport stageEq size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFamilyPorts
