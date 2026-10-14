import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedConstructorHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTupleHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOperatorBounds

/-! Structural recursion connects direct and indirect calls at their actual
compiler occurrences. The caller retains authentic canonical global slots;
ordinary children use its identical pool and restoration. Direct authority
comes from the finite inventory, and strict named-body hypotheses belong to
the exact selected Header. Source and native execution grades stay independent. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls DirectCalls NoMethods)
open CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority (IndexReady)
open CallableIndexedOwnedPreparedStagedCallerHeadHandlers
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "bridge" => callerBridge.forgetSlots

/-- Direct authority belongs only to the actual reached static subtree. -/
def DirectReady {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) : Prop :=
  ∀ {callFuel callScope callId actualCallee actualIds instantiation actualCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body callFuel compilation
      (.initial compiled.compatible.checked) invocation.source callScope callId actualCallee actualIds
      instantiation reasonAt actualCode), DirectCalls compiler root → Nonempty
        (CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler headers context invocation.evidence)

private theorem named_descriptor (header : CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram)) :
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

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include owner callerBridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves_reached
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    NoMethods root → DirectReady (headers := headers) root → IndexReady root → CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  intro noMethods directReady indexReady ports
  have directHeads : PreservesDirect bridge model stages callFaults budget root := by
    intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
    obtain ⟨port⟩ := directReady compiler path
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
      compiler port.toReady wellFormed runtime.signatures application
    have ordered := rows.1 ▸ sequence
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CallableIndexedOwnedPreparedStagedDirectHeadBounds.preserves
      owner compiler port.toPort port.evidence callerBridge functions callFaults unique wellFormed runtime covers
      size ordered childMeaning (namedChildren size within port.header port.member) ⟨rfl, rfl, rfl⟩
  have methodHeads : PreservesMethod bridge model stages callFaults budget root := by
    intro fuel current id code types compiler path
    exact (noMethods compiler path).elim
  have indirectHeads : PreservesIndirect bridge model stages callFaults budget root := by
    intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
    obtain ⟨port⟩ := ports compiler path
    have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
        current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds.preserves (semantic := semantic)
      bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
      actualFunctionType observations closurePackets closureSupport namedTerminals
      compiler port calleeCertified sequence size childMeaning
      budget bodyChildren canonicalChildren (namedChildren size within) within ⟨rfl, rfl, rfl⟩
  exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.preserves_reached
    owner callerBridge receiver profile wellFormed runtime covers unique observations extension semantic
    sameLedger runtimeLedger uninitializedOn budget root reached
    directHeads methodHeads indexReady indirectHeads

include owner callerBridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects_reached (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    NoMethods root → DirectReady (headers := headers) root → IndexReady root → CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  intro noMethods directReady indexReady ports
  have directHeads : ReflectsDirect bridge model stages callFaults budget root := by
    intro fuel current id callee ids instantiation code types compiler path calleeTyped application sequence size within childMeaning
    obtain ⟨port⟩ := directReady compiler path
    have rows := CallableIndexedOwnedPreparedStagedDirectCallAuthority.Ready.source_types
      compiler port.toReady wellFormed runtime.signatures application
    have ordered := rows.1 ▸ sequence
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    obtain ⟨descriptor⟩ := named_descriptor port.header
    have reflected : ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        invocation (CallableIndexedOwnedPreparedStagedDirectHeadBounds.Point current child code) callFaults size :=
      CallableIndexedOwnedPreparedStagedDirectHeadBounds.reflects
      owner compiler port.toPort port.evidence callerBridge functions callFaults unique wellFormed runtime covers
      stagePrepared descriptor size ordered (stageEq ▸ childMeaning)
      (stageEq ▸ namedChildren size within port.header port.member)
    have inStages : ReflectsAt bridge context model stages invocation
        (CallableIndexedOwnedPreparedStagedDirectHeadBounds.Point current child code) callFaults size :=
      stageEq.symm ▸ reflected
    intro node
    exact inStages ⟨rfl, rfl, rfl⟩ (node := node)
  have methodHeads : ReflectsMethod bridge model stages callFaults budget root := by
    intro fuel current id code types compiler path
    exact (noMethods compiler path).elim
  have indirectHeads : ReflectsIndirect bridge model stages callFaults budget root := by
    intro fuel current id callee ids metadata code types compiler path sequence size within childMeaning
    obtain ⟨port⟩ := ports compiler path
    have calleeCertified : RecursiveStageTupleMeaning.Entries current compiler.entries
        current callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
    intro current child code point
    obtain ⟨rfl, rfl, rfl⟩ := point
    exact CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds.reflects (semantic := semantic)
      bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
      actualFunctionType observations closurePackets closureSupport namedTerminals
      stageEq compiler port calleeCertified sequence size childMeaning
      budget bodyChildren canonicalChildren (namedChildren size within) within ⟨rfl, rfl, rfl⟩
  exact CallableIndexedOwnedPreparedStagedSharedRecursiveCallerBounds.reflects_reached
    owner callerBridge receiver profile wellFormed runtime covers unique observations extension semantic
    sameLedger runtimeLedger uninitializedOn budget root reached
    directHeads methodHeads indexReady indirectHeads

include owner callerBridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → DirectReady (headers := headers) root → IndexReady root → CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact preserves_reached (faultRoot := rootId) owner callerBridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closurePackets closureSupport namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    budget bodyChildren canonicalChildren namedChildren root (.root (by simp))


include owner callerBridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → DirectReady (headers := headers) root → IndexReady root → CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact reflects_reached (faultRoot := rootId) owner callerBridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closurePackets closureSupport namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    stageEq budget bodyChildren canonicalChildren namedChildren root (.root (by simp))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds
