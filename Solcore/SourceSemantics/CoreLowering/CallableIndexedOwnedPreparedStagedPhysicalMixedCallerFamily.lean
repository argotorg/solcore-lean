import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalIndirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds

/-! One strong induction closes ordinary calls, selected methods and retained indirect callees
at actual complete physical cache states. Every body continuation comes from
an authentic static packet and a strictly smaller expression proof. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedStagedPhysicalMixedRootBounds
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport (Packet Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}

/-- Genuine packets for every selected method, at the exact retained SourceAt.
No execution, allocation or body law is part of this static family. -/
def MethodSupports : Prop :=
  ∀ {policy body fuel compilation source scope id reasonAt lowered context caller}
    (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked) source scope id reasonAt lowered)
    (port : Port (compiled := compiled) receipt context caller stages),
    ∃ packet : Packet port.principal, packet.sourceAt = port.sourceAt ∧
      Support port.principal packet headers stages semanticFaults

/-- Method bodies may retain either an actual terminal or scoped compiler packet. -/
def MixedMethodSupports : Prop :=
  ∀ {policy body fuel compilation source scope id reasonAt lowered context caller}
    (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked) source scope id reasonAt lowered)
    (port : Port (compiled := compiled) receipt context caller stages),
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet port.principal,
      packet.sourceAt = port.sourceAt ∧
      CallableIndexedOwnedPreparedStagedMethodBodies.Support port.principal packet headers stages semanticFaults

/-- Existing terminal method support embeds without changing its static receipts. -/
theorem MethodSupports.toMixed
    (support : MethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults)) :
    MixedMethodSupports (compiled := compiled) (headers := headers)
      (stages := stages) (semanticFaults := semanticFaults) := by
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  obtain ⟨packet, sourceAt, supported⟩ := support receipt port
  exact ⟨.terminal packet, sourceAt, supported⟩

private theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) : stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [sourceType, ih rest]

private theorem named_descriptor (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

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
  (bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (bodySupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := bodyRegistry) (stages := stages)
      (semanticFaults := semanticFaults) header (bodies header member))
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
  (mixedMethodSupport : MixedMethodSupports (compiled := compiled) (headers := headers) (stages := stages) (semanticFaults := semanticFaults))

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include closurePackets closureSupport owners stagePrepared receiver profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
/-- Every ordinary and method body uses only strictly smaller Source grades. -/
theorem preserves_with_methods (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  induction size using Nat.strongRecOn with
  | ind budget ih =>
    intro context invocation scope expression lowered root owner keyPhysical
    let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
      owner root.compilation.administrativePrefix keyPhysical.locations
    have namedBodies : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
        ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
          (headers := headers) (keys := keys) header model stages child callFaults size := by
      intro size within header member child selected
      exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.preserves
        (bodySupport header member) profile wellFormed extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    have directHeads : PreservesDirect callerBridge.forgetSlots model stages callFaults budget root.support.certificate := by
      intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
      obtain ⟨port⟩ := root.support.directReady compiler path
      have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
        compiler port.toReady wellFormed root.support.runtime.signatures application
      have ordered := rows.1 ▸ sequence
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds.preserves
        owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
        functions callFaults root.support.unique wellFormed root.support.runtime root.support.covers
        size ordered childMeaning
        (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
    have methodHeads : PreservesMethod callerBridge.forgetSlots model stages callFaults budget root.support.certificate := by
      intro fuel current id code types compiler path sequence size within childMeaning
      obtain ⟨port⟩ := root.support.methodReady compiler path
      obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port
      have bodies : CallableIndexedOwnedPreparedStagedMethodHeadBounds.SourceBodies
          (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
        intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
          heapTyped argumentsTyped stable child selected
        have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
          simpa only [sourceAtEq] using argumentsTyped
        simpa only [sourceAtEq] using
          CallableIndexedOwnedPreparedStagedMethodBodyBounds.source_continuation
            port.principal packet static wellFormed functions selected installed owner keyPhysical caller
            heapTyped packetArguments stable extension size
            (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
      intro actualScope actualId actualCode point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans compiler.metadata.found)
      have rows := CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types compiler port
        wellFormed root.support.runtime root.support.unique typed
      have ordered := tree_types sequence root.support.unique rows.1 ▸ sequence
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ outcome after
      exact CallableIndexedOwnedPreparedStagedMethodHeadBounds.preserves
        owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
        (fun state => state.base.property) functions callFaults root.support.unique wellFormed
        root.support.runtime root.support.covers size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
    have indirectHeads : PreservesIndirect callerBridge.forgetSlots model stages callFaults budget root.support.certificate := by
      intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
      obtain ⟨port⟩ := root.support.callsReady compiler path
      have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
          current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro actualScope actualId actualCode point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedPhysicalIndirectHeadBounds.preserves
        callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
        wellFormed root.support.runtime root.support.covers root.support.unique root.support.actualFunctionType
        observations closurePackets closureSupport bodies
        compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
    intro current id code point
    exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.preserves_reached_with_functions
      callerBridge.forgetSlots receiver functions wellFormed root.support.runtime root.support.covers root.support.unique
      observations extension semantic root.support.sameLedger root.support.runtimeLedger root.support.uninitialized
      budget root.support.certificate (.root (by simp)) directHeads methodHeads root.support.indexReady indirectHeads
      budget (Nat.le_refl _) point

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport mixedMethodSupport in
/-- Every ordinary and method body uses only strictly smaller native grades. -/
theorem reflects_with_methods (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  subst stages
  induction size using Nat.strongRecOn with
  | ind budget ih =>
    intro context invocation scope expression lowered root owner keyPhysical
    let callerBridge := CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
      owner root.compilation.administrativePrefix keyPhysical.locations
    have namedBodies : ∀ size, size ≤ budget → ∀ header (member : header ∈ headers),
        ∀ {child : Staging.Recursive.Scope}, (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
          (headers := headers) (keys := keys) header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child callFaults size := by
      intro size within header member child selected
      exact CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.reflects
        (bodySupport header member) profile wellFormed extension selected
        (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
    have directHeads : ReflectsDirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget root.support.certificate := by
      intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
      obtain ⟨port⟩ := root.support.directReady compiler path
      have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
        compiler port.toReady wellFormed root.support.runtime.signatures application
      have ordered := rows.1 ▸ sequence
      obtain ⟨descriptor⟩ := named_descriptor port.header
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds.reflects
        owner compiler port.toPort port.evidence callerBridge keyPhysical (fun state => state.physical)
        functions callFaults root.support.unique wellFormed root.support.runtime root.support.covers stagePrepared descriptor
        size ordered childMeaning
        (fun selected => namedBodies size within port.header port.member selected) ⟨rfl, rfl, rfl⟩
    have methodHeads : ReflectsMethod callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget root.support.certificate := by
      intro fuel current id code types compiler path sequence size within childMeaning
      obtain ⟨port⟩ := root.support.methodReady compiler path
      obtain ⟨packet, sourceAtEq, static⟩ := mixedMethodSupport compiler port
      have bodies : CallableIndexedOwnedPreparedStagedMethodHeadBounds.NativeBodies
          (headers := headers) (receiving := completion.result.context.registry) owner compiler port functions callFaults size := by
        intro mapping world heap store callerScope canonical administrative arguments payloads caller installed _parameters
          heapTyped argumentsTyped stable child selected
        have packetArguments : Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments packet.sourceAt.types := by
          simpa only [sourceAtEq] using argumentsTyped
        simpa only [sourceAtEq] using
          CallableIndexedOwnedPreparedStagedMethodBodyBounds.native_continuation
            port.principal packet static wellFormed functions selected installed owner keyPhysical caller
            heapTyped packetArguments stable extension size
            (fun smaller strict => ih smaller (Nat.lt_of_lt_of_le strict within))
      intro actualScope actualId actualCode point actual found typed
      obtain ⟨rfl, rfl, rfl⟩ := point
      cases Option.some.inj (found.symm.trans compiler.metadata.found)
      have rows := CallableIndexedOwnedPreparedStagedMethodArgumentRows.raw_types compiler port
        wellFormed root.support.runtime root.support.unique typed
      have ordered := tree_types sequence root.support.unique rows.1 ▸ sequence
      intro mapping world administrativeContext environment canonical actualEnvironment actualContext before store ξ value finalStore
      exact CallableIndexedOwnedPreparedStagedMethodHeadBounds.reflects
        owner compiler port callerBridge keyPhysical.frame (fun state => state.physical)
        (fun state => state.base.property) functions callFaults root.support.unique wellFormed
        root.support.runtime root.support.covers size ordered childMeaning bodies ⟨rfl, rfl, rfl⟩ found typed
    have indirectHeads : ReflectsIndirect callerBridge.forgetSlots model (RecursiveNamedPreparedStageScopes.registry stagePrepared) callFaults budget root.support.certificate := by
      intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
      obtain ⟨port⟩ := root.support.callsReady compiler path
      have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
          current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro actualScope actualId actualCode point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedPhysicalIndirectHeadBounds.reflects
        callerBridge.forgetSlots (fun state => state.physical) owners receiver stagePrepared rfl profile
        wellFormed root.support.runtime root.support.covers root.support.unique root.support.actualFunctionType
        observations closurePackets closureSupport bodies
        rfl compiler port calleeCertified sequence size childMeaning budget ih (namedBodies size within) within ⟨rfl, rfl, rfl⟩
    intro current id code point
    exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.reflects_reached_with_functions
      callerBridge.forgetSlots receiver functions wellFormed root.support.runtime root.support.covers root.support.unique
      observations extension semantic root.support.sameLedger root.support.runtimeLedger root.support.uninitialized
      budget root.support.certificate (.root (by simp)) directHeads methodHeads root.support.indexReady indirectHeads
      budget (Nat.le_refl _) point

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem preserves_with_bodies (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_methods receiver stagePrepared profile wellFormed observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic bodies bodySupport methodSupport in
/-- The existing named-body API embeds its terminal method packets. -/
theorem reflects_with_bodies (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_methods receiver stagePrepared profile wellFormed observations extension semantic
    bodies bodySupport closurePackets closureSupport owners methodSupport.toMixed stageEq size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal families delegate to the same body-generic induction. -/
theorem preserves (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  preserves_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport size

include closurePackets closureSupport owners receiver stagePrepared profile wellFormed observations extension semantic terminals namedSupport methodSupport in
/-- Existing terminal reflection retains its original arguments and conclusion. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  reflects_with_bodies receiver stagePrepared profile wellFormed observations extension semantic
    (fun header member => CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal (terminals header member))
    (fun header member => CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.of_terminal_support
      (terminals header member) (namedSupport header member))
    closurePackets closureSupport owners methodSupport stageEq size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily
