import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily

/-! The closed physical mixed family supplies named body ports for actual
terminal expressions or genuine lambda formation at every reached registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily (MethodSupports)

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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (terminals : ∀ header, header ∈ headers → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) header (terminals header member))
      { _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
          (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults)
          header (terminals header member) // header.globals = compiled.indexed.base.globals.length })
  (closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor association.original stages)
  (closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys bodyRegistry semanticFaults
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original stages (closurePackets association))
  (owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (methodSupport : MethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem preserves (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  cases namedSupport header member with
  | inl static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.preserves
      static selected wellFormed
      (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.preserves
        receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport
        closurePackets closureSupport owners methodSupport size)
  | inr static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.preserves
      profile static.val selected wellFormed static.property

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (member : header ∈ headers) {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child callFaults budget := by
  cases namedSupport header member with
  | inl static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.reflects
      static selected wellFormed
      (fun size _ => CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.reflects
        receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport
        closurePackets closureSupport owners methodSupport stageEq size)
  | inr static =>
    exact CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.reflects
      profile static.val selected wellFormed static.property

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts
