import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedPhysicalClosureArguments
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection

/-! An actual public session carries its indexed runtime, Source heap and
positive physical history. Calls retain their own public options and receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

abbrev StartedCall := @RecursiveNamedPublicPhysicalSessionState.StartedCall
abbrev Call := @RecursiveNamedPublicPhysicalSessionState.Call
abbrev FunctionCall := @RecursiveNamedPublicPhysicalSessionState.FunctionCall
abbrev SourceCall := @RecursiveNamedPublicPhysicalSessionState.SourceCall
abbrev PlainValue := @RecursiveNamedPublicPhysicalSessionState.PlainValue
abbrev PlainFault := @RecursiveNamedPublicPhysicalSessionState.PlainFault
abbrev FailureProjection := @RecursiveNamedPublicPhysicalSessionState.FailureProjection

section SourceOutcomes
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {anchor header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap} {arguments : List Dynamic.Value}

theorem SourceCall.value_plain {value : Dynamic.Value}
    (trace : SourceCall anchor header invocation before arguments (.value value) after) :
    PlainValue anchor header invocation before arguments value after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.value_plain trace

theorem SourceCall.semanticFault_plain {reason : Dynamic.SemanticFault}
    (trace : SourceCall anchor header invocation before arguments (.fault (.semantic reason)) after) :
    PlainFault anchor header invocation before arguments reason after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.semanticFault_plain trace

theorem SourceCall.failure_plain {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor header invocation before arguments (.fault failure) after) :
    FailureProjection anchor header invocation before arguments failure after :=
  RecursiveNamedPublicPhysicalSessionState.SourceCall.failure_plain trace
end SourceOutcomes

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)}

def functions (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys compiled)
    initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) profile

structure State (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers rows)
    (keys compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicPhysicalHistory.History (headers := headers rows)
    (keys := keys compiled) (functions := functions rows initial profile)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    session mapping world heap store caller entries

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
