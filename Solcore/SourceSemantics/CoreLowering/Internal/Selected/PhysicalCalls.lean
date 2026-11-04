import Solcore.SourceSemantics.CoreLowering.Internal.Selected.IndirectDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalPreservationDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedIndirectTerminalReflectionDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.DirectCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedPayloadReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectArgumentRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments

/-!
# Selected compilations: physical calls

Named, direct and indirect call bounds on the physical protocol, with global dispatch and caller preservation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectDispatch
/-! The original caller prefix classifies fault, builtin, closure and global
branches once. Mixed closure packets retain their exact Association and static
support; strict Root children use the same parent budget. Authentic named
global prefixes and every reached state remain the existing contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)
open SelectedCompilationIndirectBuiltinPreservationDispatch (ParentAt)
open SelectedCompilationIndirectBuiltinApplicationDispatch (ParentResult)
open SelectedCompilationGlobalCallPrefixes (GlobalApplicationPrefix)
open SelectedCompilationGlobalCallPrefixes (GlobalAppliedPrefix)
open SelectedCompilationGlobalCallPrefixes (GlobalAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))



variable (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

include physical owners receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped runtime actualFunctionType observations semantic assignmentInterpretation in
/-- One original Source parent constructs its complete native result or
retains the authentic named suffix. The concrete call producers reuse the
literal callee and argument evaluations and their reached pool. -/
theorem preserves_parent_or_global (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after ∨
    GlobalAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge (profile := profile) compiler prepared initial budget size outcome after := by
  rcases SelectedCompilationIndirectSourcePrefixDispatch.preserves_fault_or_application
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (functionModel := functions)
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique guardFrame
      sourceParent tree unique parentTyped stagePrepared receiver budget children trace within with fault | application
  · exact .inl ⟨trace, fault⟩
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, calleeTrace, accepted, argumentsTrace, called, constructedPrefix⟩ := application
    cases sizeEq
    rcases SelectedCompilationIndirectBuiltinPreservationDispatch.preserves_builtin_or_user
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (functionModel := functions)
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations calleeTrace accepted argumentsTrace called constructedPrefix with user | parent
    · rcases SelectedCompilationPhysicalClosureUserDispatch.preserves_closure_or_global (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          bridge profile physical owners compiler prepared initial sourceParent occurrence stagePrepared receiver
          runtime sourceEq tree unique parentTyped found guardFrame actualFunctionType
          packets supported budget bodyChildren user.1 calleeTrace accepted argumentsTrace called (Nat.le_of_lt strict)
          user.2 with closureParent | global
      · exact .inl closureParent
      · exact .inr ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap,
          argumentsHeap, sources, rfl, strict, global⟩
    · exact .inl parent

include physical owners receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped runtime actualFunctionType observations semantic assignmentInterpretation in
/-- One original native parent completion either gives full Source parent
meaning or retains its actual named application prefix. Concrete call branches
share the same reached state; no caller or argument trace is replayed. -/
theorem reflects_parent_or_global (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (functionModel := functions) (completion := completion)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge compiler prepared initial budget value finalStore := by
  rcases SelectedCompilationIndirectRetainedCalleeFaultDispatch.reflects_fault_or_application
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (functionModel := functions)
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped budget children completed within with fault | application
  · obtain ⟨sourceSize, failure, after, token, finalMap, finalWorld, trace, valueEq,
      native, represented, finalHeaps, maps, worlds, frame, metadata,
      returned, related, post⟩ := fault
    cases valueEq
    exact .inl ⟨sourceSize, .fault failure, after, finalMap, finalWorld, trace, native,
      represented, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  · rcases SelectedCompilationIndirectBuiltinApplicationDispatch.reflects_builtin_or_user
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) (functionModel := functions)
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations completed application with user | parent
    · exact SelectedCompilationPhysicalClosureUserDispatch.reflects_closure_or_global (semantic := semantic)
        (assignmentInterpretation := assignmentInterpretation)
        bridge profile physical owners compiler prepared initial sourceParent occurrence stagePrepared receiver
        runtime sourceEq tree unique parentTyped found actualFunctionType
        packets supported bodyChildren completed user
    · exact .inl parent

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedNamedEntryBounds (Prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
variable {arguments : List Dynamic.Value} {payloads : List Value}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

include functions owner caller header physicalCapture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where the body port
reconstructs the staged body. The original global application and the
literal restored caller are then constructed with its actual final lexical context. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: (physicalCapture.named).captured) store
      (header.code.rename (physicalCapture.named).embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry) (payloads := payloads) functions owner caller header (physicalCapture.named)
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds.native_prefix
    (functions := functions) (registry := registry) owner caller header (physicalCapture.named) sameLayouts member represented heaps completed
  let receipt := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.parameter_receipt functions owner caller header (physicalCapture.named) packet.toPrefix stable heapTyped argumentsTyped
  have source := SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  have physicalEntry := (physicalAuthority.install (caller.rows owner.position).authority.frame.read
    (.state packet.index)).extend packet.entry.frame
  have physicalSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) packet.entry.canonical := by
    obtain ⟨added, length, same⟩ := packet.spine
    intro slot signature found
    rw [same]
    have offset : (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + slot =
        added.length + (slot + 1) := by simp only [List.length_map, List.length_reverse]; omega
    rw [offset, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using physicalCapture.slots slot signature found
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected packet.entry.environments packet.entry.heaps packet.entry.locals
      packet.entry.lookups packet.entry.actualTyped packet.reached admitted owner
      (fun zero globals => receipt.packet zero globals)
      physicalCapture.keyPhysical physicalEntry physicalSlots
      packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies
    (caller := invocation) (context := context) sourceAt stagePrepared selected
    header.extended packet.entry.allocation trace matched
  have maps := packet.entry.maps.trans bodyMaps
  have worlds := packet.entry.worlds.trans bodyWorlds
  have frame := packet.entry.frame.trans bodyFrame
  have metadata := packet.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := packet.related.trans bodyRelated
  have physical : (caller.rows owner.position).authority.frameLocation = keys[owner.position.val].frameLocation :=
    (caller.rows owner.position).frame_eq
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  have storeEq : finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex (body :=
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        finalMap, finalWorld, after, packet.bodyStore, packet.entry.canonical⟩) caller owner.position).store := by
    simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical] using packet.restored
  have whole := completed.sound
  rw [storeEq] at whole
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld, applied, ?_⟩
  rw [storeEq]
  exact ⟨whole, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, restoredRelated, restoredPost⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationPreservation
/-! Authentic named parameter allocation and body preservation compose with
literal caller restoration. Body ports permit arbitrary final lexical Source
contexts while restoring the entry native scope and full caller admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open SelectedCompilationNamedAdmission (body_prefix)

section Native
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
variable {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header physicalCapture sourceAt in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header (physicalCapture.named)
        context outcome after value finalStore finalMap finalWorld faults := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : (physicalCapture.named).canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using (physicalCapture.named).reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, allocated, bodyTrace, converted, smaller⟩ := body_prefix sourceAt owners arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift))
      (DataPatternValues.packValues payloads :: (physicalCapture.named).canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift (physicalCapture.named).layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped (physicalCapture.named).typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement, spine⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds.parameters_with_state_spine installedAuthority
    (physicalCapture.named).environments liveLocals liveReference (physicalCapture.named).coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, (physicalCapture.named).administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped).heapTyped, receipt.rows⟩
  have physicalEntry := (physicalAuthority.install authority.frame.read (.state index)).extend entry.frame
  have physicalSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical := by
    obtain ⟨added, length, same⟩ := spine
    intro slot signature found
    rw [same]
    have offset : (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + slot =
        added.length + (slot + 1) := by simp only [List.length_map, List.length_reverse]; omega
    rw [offset, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using physicalCapture.slots slot signature found
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected entry.environments entry.heaps entry.locals entry.lookups
      entry.actualTyped parameterState admitted owner
      (fun zero globals => receipt.packet zero globals)
      physicalCapture.keyPhysical physicalEntry physicalSlots
      bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: (physicalCapture.named).captured)[(physicalCapture.named).embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using (physicalCapture.named).capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: (physicalCapture.named).captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename (physicalCapture.named).embedding.lift = withFrame
      (.var ((physicalCapture.named).embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename (physicalCapture.named).embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position,
    restoredRelated, restoredPost⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using
    (renamed.symm ▸ evaluation)
end Native
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedInvocationPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedApplicationBounds
/-! The complete retained named carrier applies its literal native closure.
The real apply rule gives the invocation its strict native grade. The original
staged Source application and exact returned caller pool remain independent of
that grade; the invocation producers retain nested stage failure identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

open CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds (carrier)

include functions owner caller header physicalCapture sourceAt in
/-- Source allocation and its selected body construct the exact invocation,
then the physical payload apply rule. No native grade is equated to Source. -/
theorem application_preserves
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptor : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context before (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [carrier (owner := owner) header physicalCapture.named identity descriptor, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header physicalCapture.named
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    SelectedCompilationPhysicalNamedInvocationPreservation.preserves_invocation
      functions owner caller header physicalCapture sourceAt sameLayouts physicalAuthority member owners certified
      stable heapTyped argumentsTyped represented heaps supports budget children trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) result.1, result⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))

include functions owner caller header physicalCapture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual complete native apply supplies a strict body invocation grade.
Its original Header and authenticated staged scope then construct the Source
application, with the exact full postcondition in the returned caller pool. -/
theorem application_reflects
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptorWord : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (owner := owner) header physicalCapture.named identity descriptorWord, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      Evaluates [carrier (owner := owner) header physicalCapture.named identity descriptorWord, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header physicalCapture.named
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨bodySize, smaller, invoked⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    SelectedCompilationPhysicalNamedInvocationBounds.reflects_invocation
      functions owner caller header physicalCapture prepared aligned stagePrepared descriptor sourceAt
      sameLayouts physicalAuthority member certified stable heapTyped argumentsTyped represented heaps supports budget children
      invoked (Nat.le_trans (Nat.le_of_lt smaller) within)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, result⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedParentBounds
/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
Static named compiler provenance and strict expression coverage are inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (argumentsTyped : Dynamic.ValuesHaveTypes context argumentsHeap sources sourceTypes)
  (argumentMetadata : Dynamic.HeapMetadataExtend calleeHeap argumentsHeap)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header argumentMap argumentWorld argumentsStore)
  (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled argumentMap argumentsStore)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (certifiedAt : SelectedCompilationNamedArgumentRows.CertifiedAt (header := header) (function := function))
  (certified : SelectedCompilationNamedSourceTyping.Certified header)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
    (owner := owner) header physicalCapture.named identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions compiler prepared dispatch selected callerPrepared count runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt certifiedAt certified nativeType admitted in
private theorem arguments_at :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    SelectedCompilationNamedArgumentRows.accepted_rows sourceAt compiler certifiedAt
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    SelectedCompilationNamedArgumentRows.arguments_at sourceAt certifiedAt certified
      runtime admitted.heap argumentsTyped (calleeTyped.mono argumentMetadata) bundle physicalArity
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge functions compiler initial reached related maps worlds frame heapMetadata owner header physicalCapture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := values) functions owner (bridge.pool reached) header physicalCapture.named
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge functions compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted owners runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult owner header physicalCapture physicalAuthority sourceAt certifiedAt certified
  identity descriptorWord carrierEq nativeType sameLayouts member in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at bridge functions compiler prepared reached admitted dispatch selected callerPrepared count runtime
      calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt
      certifiedAt certified nativeType
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    SelectedCompilationPhysicalNamedApplicationBounds.application_preserves
      functions owner (bridge.pool reached) header physicalCapture sourceAt sameLayouts physicalAuthority member owners certified
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget children called within
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge functions compiler initial reached related maps worlds frame heapMetadata owner header physicalCapture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge functions compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted runtime
  calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult owner header physicalCapture physicalAuthority sourceAt certifiedAt certified
  identity descriptorWord carrierEq nativeType sameLayouts member namedPrepared aligned
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at bridge functions compiler prepared reached admitted dispatch selected callerPrepared count runtime
      calleeTyped actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult header sourceAt
      certifiedAt certified nativeType
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    SelectedCompilationPhysicalNamedApplicationBounds.application_reflects
      functions owner (bridge.pool reached) header physicalCapture sourceAt
      namedPrepared aligned stagePrepared descriptor sameLayouts physicalAuthority member certified admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget children application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge functions compiler initial reached related maps worlds frame heapMetadata owner header physicalCapture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedGlobalDispatch
/-! Internal chosen-body dispatch for the eventual numeric body family.
The static factory selects one genuine packet; the body hypothesis belongs to
that packet alone. Existing failure, physical arity, parameter/body execution
and saved caller restoration proofs retain their original indices. Original
Source typing and compiler-policy transport remain separate static obligations.
-/
/-! A positive global payload retains its actual Header, Source instantiation,
dictionary and native captured code. The selected physical count is decided
at the real argument endpoint before this Header's body producer.
Static per-Header compiler coverage and numeric child coverage remain inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedGlobalDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open SelectedCompilationGlobalCallPrefixes (GlobalApplicationPrefix)
open SelectedCompilationGlobalCallPrefixes (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry preparedStages)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include bridge profile compiler prepared initial physical owners sourceParent occurrence preparedStages stageEq callerPrepared receiver
  bodyTyping certificates runtime actualFunctionType in
/-- The actual global prefix exposes its original Header before any execution
law is used. Physical mismatch returns the original arity parent; equal count
runs the retained named body producer at the real reached argument state. -/
theorem reflects_global
    (bodies : ∀ header, header ∈ headers → Body header)
    {budget size : Nat} {value : Value} {finalStore : Store}
    (children : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry preparedStages).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry preparedStages)
          child callFaults budget)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (global : GlobalApplicationPrefix (functionModel := functions) (completion := completion) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  obtain ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
    calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
    _callView, boundary, heaps, maps, worlds, frame, heapMetadata, argumentsTyped, argumentMetadata, ⟨reached, related, admitted⟩,
    suffixSize, suffix, strict⟩ := global
  have origin : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨originalType, ⟨association⟩, _runtimeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member profile origin function rfl
  let owner := association.owner
  let header := association.header
  let identity := association.identity
  let descriptor := association.descriptor
  have member : header ∈ headers := association.member
  have sourceAt := association.sourceAt
  have nativeType := association.type_eq
  let terminal := bodies header member
  have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at sourceAt bodyTyping terminal.prepared terminal.aligned
  have certified := certificates header member
  have physicalAuthority := physical.extend frame
  obtain ⟨⟨capture, sameCapture⟩⟩ := association.at_store terminal.prepared terminal.aligned
    (owners owner) physicalAuthority
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture.named identity descriptor.id := by
    rw [sameCapture]
    exact association.native_eq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
        returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
        SelectedCompilationPhysicalNamedParentBounds.reflects_suffix
          bridge functions compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted runtime
          rawCallee actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult
          owner header capture physicalAuthority sourceAt certifiedAt certified identity descriptor.id carrierEq nativeType terminal.layouts member
          terminal.prepared terminal.aligned preparedStages descriptor stageEq
          budget (children header member) calleeTrace argumentsTrace suffix (Nat.le_of_lt strict)
      exact ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
        resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
        returned, returnedRelated, returnedPost⟩
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have mismatch : header.function.parameters.length ≠ sources.length := by
        intro same
        exact count (physical.trans (same.trans valuesCount))
      have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.arity_failure
        (actual := preparedStages) (caller := invocation) (context := context) (heap := argumentsHeap) sourceAt mismatch
      have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
          (Staging.Recursive.Size.stepSize []) invocation context argumentsHeap (.global function) sources
          (.fault (.semantic (.argumentArityMismatch header.function.parameters.length sources.length))) argumentsHeap := by
        simpa only [stageEq] using applied
      have failedSource := Staging.Recursive.Size.Expression.applied occurrence compiler.argumentCoercions
        calleeTrace accepted argumentsTrace sourceParent.arity called
      have lowerType : lowered.type = compiler.resultType :=
        (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
      obtain ⟨sameValue, sameStore⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
          dispatch.shape selected dispatch.found count suffix
      cases sameStore
      obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
        CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
          compiler prepared preparedStages selected receiver initial functions reached related heaps
          (sourceResult := compiler.original.type) (resultCore := lowered.type) count
      cases sameState
      refine ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
        .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
        argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
        heapMetadata, reached, keptRelated, ?_⟩
      · simpa only [physical, valuesCount] using failedSource
      · have exactValue : value = .inLeft lowered.type
            (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
          simpa only [lowerType] using sameValue
        rw [exactValue]
        exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
      · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
        exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩

include bridge profile compiler prepared initial physical owners sourceParent occurrence preparedStages callerPrepared receiver
  bodyTyping certificates runtime actualFunctionType in
/-- The genuine global Source suffix retains its original allocation and body
scope. The actual Header and physical row select body execution or arity
failure, and both branches preserve every reached caller effect. -/
theorem preserves_global
    (bodies : ∀ header, header ∈ headers → Body header)
    (guardFrame : invocation.guards = CallableLedger.frame sidecar)
    (budget : Nat)
    (children : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child callFaults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (global : GlobalAppliedPrefix (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial
      calleeSize argumentsSize applicationSize sourceValue calleeHeap argumentsHeap sources outcome after)
    (within : applicationSize ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after := by
  obtain ⟨function, selectedFunction, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩ := global
  cases selectedFunction
  obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
    calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
    originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
    represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
    frame, heapMetadata, argumentsTyped, argumentMetadata, reached, related, admitted⟩ := prefixResult
  have origin : CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins headers keys bodyRegistry
      completion.result.context.registry semanticFaults profile finalMap finalWorld
      calleeNode.type (.global function) carrier compiler.calleeCode.type := by
    exact calleeRelated
  obtain ⟨originalType, ⟨association⟩, _runtimeType⟩ :=
    CallableIndexedOwnedPreparedPhysicalCellOrigins.PayloadOrigins.named_member profile origin function rfl
  let owner := association.owner
  let header := association.header
  let identity := association.identity
  let descriptor := association.descriptor
  have member : header ∈ headers := association.member
  have sourceAt := association.sourceAt
  have nativeType := association.type_eq
  let terminal := bodies header member
  have certifiedAt := SelectedCompilationNamedArgumentRows.certified_at sourceAt bodyTyping terminal.prepared terminal.aligned
  have certified := certificates header member
  have physicalAuthority := physical.extend frame
  obtain ⟨⟨capture, sameCapture⟩⟩ := association.at_store terminal.prepared terminal.aligned
    (owners owner) physicalAuthority
  have carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
      (owner := owner) header capture.named identity descriptor.id := by
    rw [sameCapture]
    exact association.native_eq
  cases boundary with
  | user dispatch selected =>
    by_cases count : dispatch.row.entry.parameterCount = ids.length
    · have calleeNative := calleePost.1
      obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
        _calleeFrame, calleeMetadata, _calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
      have calleeHeapTyped := calleeAdmission.at_value.2.heap
      have rawCallee : Dynamic.ValueHasType context calleeHeap (.global function)
          (.function rawParameter rawResult) := by
        simpa only [functionType] using calleeTyped
      exact SelectedCompilationPhysicalNamedParentBounds.preserves_parent
        bridge functions compiler prepared sourceParent occurrence initial reached related admitted
        heaps maps worlds frame heapMetadata dispatch selected callerPrepared count accepted bodyTyping.function_ids runtime
        rawCallee actualFunctionType represented argumentsTyped argumentMetadata bundle originalResult
        owner header capture physicalAuthority sourceAt certifiedAt certified identity descriptor.id carrierEq nativeType terminal.layouts member
        budget (children header member)
        calleeTrace argumentsTrace called within calleeNative firstGate argumentsNative
    · have physical := CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count
        sourceAt callerPrepared dispatch selected
      have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
      have different : header.function.parameters.length ≠ ids.length := by
        simpa only [physical] using count
      have bodyUnique : ∀ actualBody,
          Dynamic.FunctionInstantiates (Program.ofChecked compiled.sourceProgram) function.instantiation actualBody →
          RecursiveNamedCatalog.Header.sourceBody header = actualBody := by
        intro actualBody instantiated
        exact BuiltinNamedCalls.instantiation_unique bodyTyping.function_ids sourceAt.frame.instantiated instantiated
      cases called with
      | global instantiated _covers _roots _selected _parameters allocate _body _converted =>
        have same := bodyUnique _ instantiated
        cases same
        have actualCount := (congrArg List.length sourceAt.frame.parameters).trans
          (allocate.length_eq.trans valuesCount)
        exact False.elim (different actualCount)
      | globalArity instantiated mismatch =>
        have same := bodyUnique _ instantiated
        cases same
        have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
            prepared.site.call ids (.global function) := by
          simpa only [guardFrame, prepared.call] using accepted
        have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
            (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
            (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
          simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
            using argumentsNative
        have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
          (result := compiler.resultType) dispatch selected actualAccepted count
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
        change Evaluates actual store
          (CallableContract.call prepared.site.gates
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
            (compiler.calleeCode.expression.rename ξ)
            ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
        rw [← prepared.lowered_rename compiler ξ] at native
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) count
        cases sameState
        have loweredType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
            compiler.original.type
            (.fault (.semantic (.argumentArityMismatch
              (RecursiveNamedCatalog.Header.sourceBody header).source.inputs.length sources.length))) reached :=
          ⟨admitted.rows, by intro value impossible; cases impossible⟩
        refine ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity
          (.globalArity instantiated mismatch),
          .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
            .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
          argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame, heapMetadata,
          reached, keptRelated, post⟩
        · simpa only [loweredType] using native
        · simpa only [physical, sourceAt.frame.parameters, valuesCount] using faultRep

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalNamedGlobalDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectCallBounds
/-! Original whole indirect calls consume the mixed closure dispatch and the
unchanged selected named global producer. Caller callee/argument children and
strict called Root children are distinct and share the literal point budget.
The original ParentAt/ParentResult includes the full restored caller post. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))


variable (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

include physical owners receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped bodyTyping certificates runtime actualFunctionType observations semantic assignmentInterpretation in
/-- One original native completion gives full staged Source parent meaning,
including the actual named global branch and restored caller post. -/
theorem reflects_parent
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedTerminals : ∀ header, header ∈ headers → Body header)
    (namedChildren : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          child callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  rcases SelectedCompilationPhysicalIndirectDispatch.reflects_parent_or_global (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      bridge physical owners receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped runtime actualFunctionType observations
      budget children closurePackets closureSupport bodyChildren completed within with parent | global
  · exact parent
  · exact SelectedCompilationPhysicalNamedGlobalDispatch.reflects_global
      bridge profile compiler prepared initial (physical initial) owners sourceParent occurrence stagePrepared stageEq caller receiver
      bodyTyping certificates runtime actualFunctionType
      namedTerminals namedChildren completed global

include physical owners receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped bodyTyping certificates runtime actualFunctionType observations semantic assignmentInterpretation in
/-- One original staged Source parent constructs its native completion and
full caller post. The authentic named branch uses its actual strict application
child; Source and native grades remain independent. -/
theorem preserves_parent (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedTerminals : ∀ header, header ∈ headers → Body header)
    (namedChildren : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after := by
  rcases SelectedCompilationPhysicalIndirectDispatch.preserves_parent_or_global (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      bridge physical owners receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped runtime actualFunctionType observations
      budget children closurePackets closureSupport bodyChildren trace within with parent | global
  · exact parent
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, globalPrefix⟩ := global
    cases sizeEq
    exact SelectedCompilationPhysicalNamedGlobalDispatch.preserves_global
      bridge profile compiler prepared initial (physical initial) owners sourceParent occurrence stagePrepared caller receiver
      bodyTyping certificates runtime actualFunctionType
      namedTerminals guardFrame budget namedChildren globalPrefix (Nat.le_of_lt strict)

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectHeadBounds
/-! Call-head assembly for the original static Port and Point. The structural
caller supplies strict callee/argument children. The numeric family supplies
Root children below its outer budget, restricted here to the current call size.
Actual selected closure bodies and named body ports then construct
the original whole-call result and restored caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Point Port)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
  (certificates : ∀ header, header ∈ headers → SelectedCompilationNamedSourceTyping.Certified header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include physical owners bridge receiver stagePrepared sourceEq profile bodyTyping certificates runtime unique
  actualFunctionType observations closurePackets closureSupport namedTerminals semantic assignmentInterpretation in
/-- Reuse the original whole-call producer at the supplied genuine Source
grade. The returned caller state and post are retained literally. -/
theorem preserves
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : PreservesBelow bridge context model stages invocation certificate callFaults size)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    (within : size ≤ budget) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact (SelectedCompilationPhysicalIndirectCallBounds.preserves_parent (semantic := semantic)
    (assignmentInterpretation := assignmentInterpretation)
    bridge physical owners receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
    profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
    admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
    bodyTyping certificates runtime actualFunctionType observations
    size children closurePackets closureSupport
    (fun childSize smaller => bodyChildren childSize (Nat.lt_of_lt_of_le smaller within))
    namedTerminals namedChildren trace (Nat.le_refl _)).2

include physical owners bridge receiver stagePrepared sourceEq profile bodyTyping certificates runtime unique
  actualFunctionType observations closurePackets closureSupport namedTerminals semantic assignmentInterpretation in
/-- The native completion keeps its independent Source grade and exact
staged fault scope. Only the duplicate native evaluation witness is omitted. -/
theorem reflects
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : ReflectsBelow bridge context model stages invocation certificate callFaults size)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    (within : size ≤ budget) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  have actualNamedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) child
          callFaults size := by
    simpa only [stageEq] using namedChildren
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, finalHeaps, maps, worlds, frame, metadataExtended, reached, related, post⟩ :=
    SelectedCompilationPhysicalIndirectCallBounds.reflects_parent (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      bridge physical owners receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
      profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
      admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
      bodyTyping certificates runtime actualFunctionType observations
      stageEq size children closurePackets closureSupport
      (fun childSize smaller => bodyChildren childSize (Nat.lt_of_lt_of_le smaller within))
      namedTerminals actualNamedChildren completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadataExtended, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalDirectBounds
/-! Direct declaration calls retain all physical cache slots through reached
parameter entry. The same authentic Header, Source evidence and actual native
closure are used; physical method authority crosses the nested body and is
restored with the exact caller state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalDirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
universe u

open CallableIndexedOwnedPreparedStagedPhysicalDirectHeadBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (shaped : SelectedCompilationSourceSignatureFacts.Shape port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem result_type : lowered.type = port.header.output :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans port.header.resultType)

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

section Preservation
variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults unique owners certified shaped runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope}, stages.Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        port.header model stages child faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rcases CallableIndexedOwnedPreparedStagedDirectSourceInversion.children
      unique receipt.metadata.found receipt.form receipt.metadata.coercions trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      calleeOccurrence, valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationWithin : invocationSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed represented
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationPhysicalNamedInvocationPreservation.preserves_invocation
        functions owner (callerBridge.pool reached) port.header capture port.sourceAt
        port.aligned.layouts (physical reached) port.member owners certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning invoked invocationWithin
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.header.slot) + 1))
        (.cellRef (OptionalCell.cellType port.header.named.signature.functionType)
          (owner.key.locations port.header)) middleStore from
        .var (agrees (callerBridge.slots initial port.header port.member))) capture.read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
  · subst outcome
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact post.fault
end Preservation

section Reflection
variable {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named port.header.named.signature.key))

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults unique certified shaped runtime stagePrepared descriptor in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        port.header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults size) :
    ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  have rows := SelectedCompilationDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.declaration instantiation)) receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form,
      rfl, receipt.metadata.coercions⟩
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace := Staging.Recursive.Size.Expression.directArgumentsFault occurrence calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [← receipt.result, ← port.signature]
      exact .fault matched
    · exact post.fault
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed payloads
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, _bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationPhysicalNamedInvocationBounds.reflects_invocation functions owner (callerBridge.pool reached)
        port.header capture port.prepared port.aligned stagePrepared descriptor port.sourceAt
        port.aligned.layouts (physical reached) port.member certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning bodyEvaluation (Nat.le_of_lt bodySmaller)
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace := Staging.Recursive.Size.Expression.directApplied occurrence calleeOccurrence valid sourceTrace produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · have rowsStable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨rowsStable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic reason => exact ⟨rowsStable, by intro _ impossible; cases impossible⟩
          | stage origin call reason => exact rowsStable
end Reflection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalDirectBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds
/-! Raw declaration calls retain the original Source form, requirements and
coercions while evaluating the actual compiler operand. Genuine named entry
and restoration preserve all physical slots and the exact caller state. The
result uses the original raw type; the surrounding coercion path supplies the
final expression result and admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Port EvidenceAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (shaped : SelectedCompilationSourceSignatureFacts.Shape port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem result_type : receipt.operand.type = port.header.output := by
  rw [receipt.native.emitted]
  exact (congrArg SourceCoreCalls.Signature.resultType port.signature).symm.trans port.header.resultType

private theorem parameter_type : port.header.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
  rw [port.signature]
  exact receipt.native.inputType

/-- Raw evaluation keeps the original form and complete coercion partition. -/
def RawPreservesAt (stages : Staging.Recursive.Registry) (size : Nat) : Prop :=
  ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
      environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram) stages size invocation context
      environment before node.form node.requirements node.coercions outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (receipt.operand.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.rawType receipt.operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.rawType outcome reached

/-- Native raw completion reconstructs the independent original raw form. -/
def RawReflectsAt (stages : Staging.Recursive.Registry) (size : Nat) : Prop :=
  ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
      environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    EvaluationSize size actual store (receipt.operand.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram) stages sourceSize invocation context
        environment before node.form node.requirements node.coercions outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.rawType receipt.operand.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.rawType outcome reached

section Preservation
variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults unique owners certified shaped runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope}, stages.Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        port.header model stages child faults size) :
    RawPreservesAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults stages size := by
  intro typed mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types receipt unique typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rcases CallableIndexedOwnedPreparedStagedRawDirectArguments.children receipt trace with
    ⟨sequenceSize, invocationSize, argumentsHeap, sources, name, evidence, sameSize,
      calleeOccurrence, valid, sourceTrace, produced, invoked⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    have invocationWithin : invocationSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationRawDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed represented
    have sourceEq := CallableIndexedOwnedPreparedStagedRawDirectArguments.global_eq receipt port evidenceAt produced
    rw [sourceEq] at invoked
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationPhysicalNamedInvocationPreservation.preserves_invocation
        functions owner (callerBridge.pool reached) port.header capture port.sourceAt
        port.aligned.layouts (physical reached) port.member owners certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning invoked invocationWithin
    have selected := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (scope.length + compilation.administrativePrefix + port.header.slot) + 1))
        (.cellRef (OptionalCell.cellType port.header.named.signature.functionType)
          (owner.key.locations port.header)) middleStore from
        .var (agrees (callerBridge.slots initial port.header port.member))) capture.read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.native.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selected bodyEvaluated
    · simpa only [rows.2, nativeResult] using result
    · have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨stable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic => exact ⟨stable, by intro _ impossible; cases impossible⟩
          | stage => exact stable
  · subst outcome
    have argumentsWithin : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace argumentsWithin
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post.fault⟩
    · rw [receipt.native.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.native.emitted] using SourceCoreCalls.call_argument_failure
        (signature := receipt.native.signature) (index := ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
        (internalReason := compilation.internalReason) (receipt.native.inputType.symm ▸ argumentsEvaluated)
end Preservation

section Reflection
variable {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named port.header.named.signature.key))

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults unique certified shaped runtime stagePrepared descriptor in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (childMeaning : ReflectsBelow bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      invocation children faults size)
    (bodyMeaning : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        port.header model (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults size) :
    RawReflectsAt (context := context) (receiving := receiving) owner receipt callerBridge functions faults (RecursiveNamedPreparedStageScopes.registry stagePrepared) size := by
  intro typed mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types receipt unique typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have orderedTyping := rows.1 ▸ typing
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.callee_receipt receipt port runtime calleeValid
  rw [receipt.native.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | @fault failure token matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.header.named.signature)
      (index := ξ (scope.length + compilation.administrativePrefix + port.header.slot))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    have trace : Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) (Staging.Recursive.Size.stepSize [sourceSize]) invocation context environment before
        node.form node.requirements node.coercions (.fault failure) argumentsHeap := by
      rw [receipt.form]
      exact .rawDirectArgumentsFault calleeOccurrence sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post.fault⟩
    · rw [nativeResult, port.header.resultType]
      exact .fault matched
  | @values sources values payloads =>
    obtain ⟨parameters, headerHeap, headerArguments, supports⟩ :=
      SelectedCompilationRawDirectArgumentRows.at_successful_arguments receipt port
        certified runtime post.at_values.heap post.values_typed payloads
    obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
      port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound (agrees (callerBridge.slots initial port.header port.member)) capture.read completed
    obtain ⟨invocationSize, outcome, after, finalMap, finalWorld, invoked, _bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, finalState, bodyRelated, bodyPost⟩ :=
      SelectedCompilationPhysicalNamedInvocationBounds.reflects_invocation functions owner (callerBridge.pool reached)
        port.header capture port.prepared port.aligned stagePrepared descriptor port.sourceAt
        port.aligned.layouts (physical reached) port.member certified post.at_values.rows headerHeap headerArguments
        parameters middleHeaps supports size bodyMeaning bodyEvaluation (Nat.le_of_lt bodySmaller)
    have produced := evidenceAt.produces
    have sourceEq := CallableIndexedOwnedPreparedStagedRawDirectArguments.global_eq receipt port evidenceAt produced
    rw [← sourceEq] at invoked
    have trace : Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) (Staging.Recursive.Size.stepSize [sourceSize, invocationSize]) invocation context environment before
        node.form node.requirements node.coercions outcome after := by
      rw [receipt.form]
      exact .rawDirectApplied calleeOccurrence valid sourceTrace produced invoked
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [rows.2, nativeResult] using result
    · have stable := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
        (callerBridge.pool initial) (callerBridge.pool returned) admitted.rows (argumentFrame.trans bodyFrame)
      cases outcome with
      | value value =>
          refine ⟨stable, ?_⟩
          intro actual same
          cases same
          exact ⟨rows.2 ▸ bodyPost.at_value.1, bodyPost.at_value.2.heap⟩
      | fault failure => cases failure with
          | semantic => exact ⟨stable, by intro _ impossible; cases impossible⟩
          | stage => exact stable
end Reflection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds
end
