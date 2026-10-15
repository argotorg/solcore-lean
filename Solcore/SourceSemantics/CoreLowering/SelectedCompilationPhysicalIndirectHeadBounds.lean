import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds

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
