import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicApplicationResults
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DirectCallers
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedClosures
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReadyFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.MethodOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions

/-!
# Staged bounds: ordinary sequence callers

Sequence callers of ordinary rows, mixed recursive body and caller bounds, and the readiness of general and scoped calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
/-! Static indirect-call authority at every genuine selected ordinary closure
scope. Direct and builtin ancestors retain their actual recursive argument
paths; original Source typing and the prepared guard frame determine each port. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralPolicyFor GeneralSyntax Certificate)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function localScope administrative)
  {readFuel callFuel : Nat} {context : SourceSemantics.Context}
  {callScope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {lowered : SourceCoreBasic.LoweredExpr}
  (profile : GeneralPolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    function.source callScope code.reasonAt)
  (syntaxTree : GeneralSyntax function.source id)
  (compiler : CallableIndirectCallCertificates.Receipt code.policy code.lowerBody callFuel
    code.compilation function.source callScope id callee ids metadata code.reasonAt lowered)
  (typed : ExpressionHasType function.source context id compiler.original.type)

include profile syntaxTree typed in
/-- Recover the actual full owner, original Source view and guard frame from
one Code's authentic stage producer. No invocation or sidecar is chosen by
an execution premise, and the emitted compiler receipt stays unchanged. -/
private theorem canonical_scope_port
    (source : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram
      compiled.indexed.base.plan code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source) :
    ∃ sidecar : SourceCoreStageContracts.Sidecar,
      SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
        code.compilation.owner = .ok sidecar ∧
      (RecursiveStageRegistry.registry compiled.sourceProgram compiled.indexed.base.plan
        compiled.indexed.ancestry.graph.inputs.callable.table).Closure function
        (RecursiveStageRegistry.scope sidecar code.active function) ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
        (compiled := compiled)
        (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler) := by
  obtain ⟨sidecar, issued, selected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code source unique
  have readPolicy := profile.read id syntaxTree
  have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent
    compiler readPolicy
  obtain ⟨prepared⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.prepared
    compiler readPolicy code.active code.callables
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, bundle, resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler parent unique typed
  obtain ⟨calleeNode, contains, stored⟩ := calleeTyped.stored_type
  have calleeFound := lookupExpression?_complete unique contains
  have sourceEq := source.source issued
  have originalUnique : NodeOccurrencesUnique sidecar.source := by
    have substituted : NodeOccurrencesUnique (sidecar.source.applySubstitution code.active) :=
      sourceEq ▸ unique
    change ((sidecar.source.applySubstitution code.active).nodes.map Node.occurrenceId).Nodup
      at substituted
    change (sidecar.source.nodes.map Node.occurrenceId).Nodup
    simpa only [TypedSource.applySubstitution_nodeOccurrenceIds] using substituted
  let port : CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds.Port
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope sidecar code.active function) compiler := {
    prepared := prepared
    sidecar := sidecar
    caller := by rw [prepared.caller]; exact issued
    view := Or.inr ⟨code.active, sourceEq⟩
    guardFrame := rfl
    originalUnique := originalUnique
    sourceParent := parent
    calleeNode := calleeNode
    calleeFound := calleeFound }
  exact ⟨sidecar, issued, selected, ⟨port⟩⟩


variable (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)

/-- The selected frame comes from the actual accepted preparation. The original
compiler certificate supplies the exact indirect-call path, even beneath a
direct declaration or builtin call. -/
theorem calls_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function scope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context code.reasonAt rootScope rootId rootCode)
    (rootSyntax : GeneralSyntax invocation.source rootId) :
    CallsReady (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected⟩ :=
    CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code sourceReceipt unique
  have guardFrame := RecursiveNamedPreparedScopeCoherence.selected_frame stagePrepared accepted wellFormed signatureMember sourceOwner
    issued sourceReceipt selected
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.calls_syntax_of path rootSyntax
  have profile := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.retained_policy_for_native
    retained metadata callScope code.reasonAt
  have parentTyped := CallableIndexedOwnedPreparedStagedRecursiveCallerRawTyping.parent_typed
    compiler unique typed path
  obtain ⟨actualSidecar, actualIssued, _actualSelected, ⟨port⟩⟩ :=
    canonical_scope_port code profile syntaxTree compiler parentTyped sourceReceipt unique
  have same : actualSidecar = canonical := Except.ok.inj (actualIssued.symm.trans issued)
  cases same

  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryGeneralCallsReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
/-! Simultaneous numeric recursion closes pool and canonical caller roots.
Actual named parameter packets supply canonical slots, while existing closure
packets retain their original pool support. Every called body consumes a
strictly smaller grade; structural children retain their independent bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds (PreservesRootsAt ReflectsRootsAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves_both [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size ∧
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  induction size using Nat.strongRecOn with
  | ind size ih =>
    constructor
    · intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.preserves_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
            (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes
        root.support.callsReady size (Nat.le_refl _)
    · intro context invocation scope expression lowered root owner caller callerBridge
      exact CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds.preserves_reached
        owner callerBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
            (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.directReady root.support.indexReady
        root.support.callsReady size (Nat.le_refl _)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size :=
  (preserves_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic size).1

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem preserves_canonical [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  (preserves_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic size).2

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects_both [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size ∧
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  induction size using Nat.strongRecOn with
  | ind size ih =>
    constructor
    · intro context invocation scope expression lowered root
      exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.reflects_reached
        poolBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
            (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes
        root.support.callsReady size (Nat.le_refl _)
    · intro context invocation scope expression lowered root owner caller callerBridge
      exact CallableIndexedOwnedPreparedStagedCanonicalRecursiveCallerBounds.reflects_reached
        owner callerBridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
        root.support.covers root.support.unique root.support.actualFunctionType observations
        extension semantic closurePackets closureSupport namedTerminals root.support.sameLedger
        root.support.runtimeLedger root.support.uninitialized stageEq size
        (fun childSize smaller => (ih childSize smaller).1)
        (fun childSize smaller => (ih childSize smaller).2)
        (fun childSize within named member {_child} selected =>
          CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
            (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
            (namedSupport named member) profile root.support.wellFormed selected extension
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).1)
            (fun smaller strict => (ih smaller (Nat.lt_of_lt_of_le strict within)).2))
        root.support.certificate (.root (by simp)) root.support.noMethods root.support.directReady root.support.indexReady
        root.support.callsReady size (Nat.le_refl _)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    ReflectsRootsAt (completion := completion) (stages := stages) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile size :=
  (reflects_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic stageEq size).1

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic in
theorem reflects_canonical [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared) (size : Nat) :
    CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
      (headers := headers) (keys := keys) model stages semanticFaults callFaults size :=
  (reflects_both profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared observations extension semantic stageEq size).2

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds
/-! Accepted original Source compilation issues the recursive caller certificate.
The mixed numeric family closes terminal or discard closure bodies, and the
structural caller fold constructs every caller child internally. Original raw
typing, policy, declarations, read diagnostics and exact issued call authority
remain static inputs. The caller protocol has its own universe and restored state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- The accepted compiler action issues the actual tree used for Source preservation. -/
theorem preserves_compiled [FunctionCalls.FaultTokens semanticFaults]
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    have bodies : ∀ childSize,
        CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
          (completion := completion) (stages := stages) (headers := headers) (keys := keys)
          (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
      CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
        (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic)
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.preserves
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
      sameLedger runtimeLedger uninitialized size (fun childSize _ => bodies childSize)
      (fun childSize _ =>
        CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves_canonical
          (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
          (namedTerminals := namedTerminals) (namedSupport := namedSupport)
          (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
          (extension := extension) (semantic := semantic) childSize)
      (fun _childSize _within named member {_child} selected =>
        CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
          (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
          (namedSupport named member) profile wellFormed selected extension
          (fun smaller _strict => bodies smaller)
          (fun smaller _strict =>
            CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves_canonical
              (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
              (namedTerminals := namedTerminals) (namedSupport := namedSupport)
              (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
              (extension := extension) (semantic := semantic) smaller))
      root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size (Nat.le_refl _) certified

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- The same issued tree reflects native completion to its independent Source grade. -/
theorem reflects_compiled [FunctionCalls.FaultTokens semanticFaults]
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
    let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted
    have bodies : ∀ childSize,
        CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
          (completion := completion) (stages := stages) (headers := headers) (keys := keys)
          (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
      CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
        (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) stageEq
    intro scope id lowered certified
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds.reflects
      bridge receiver stagePrepared profile wellFormed runtime covers unique
      actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
      sameLedger runtimeLedger uninitialized stageEq size (fun childSize _ => bodies childSize)
      (fun childSize _ =>
        CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects_canonical
          (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
          (namedTerminals := namedTerminals) (namedSupport := namedSupport)
          (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
          (extension := extension) (semantic := semantic) stageEq childSize)
      (fun _childSize _within named member {_child} selected =>
        CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
          (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
          (namedSupport named member) profile wellFormed selected extension
          (fun smaller _strict => bodies smaller)
          (fun smaller _strict =>
            CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects_canonical
              (profile := profile) (closurePackets := closurePackets) (closureSupport := closureSupport)
              (namedTerminals := namedTerminals) (namedSupport := namedSupport)
              (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
              (extension := extension) (semantic := semantic) stageEq smaller))
      root (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy root syntaxTree policyFor)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root syntaxTree)
      (CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root syntaxTree) ports size (Nat.le_refl _) certified

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
/-! Static coverage supplies a dependent packet and support at each actual
Association. Each proof chooses that pair locally and uses the accepted caller
compiler theorem. The production recipe and supported body shape remain genuine
coverage obligations. Classical.choice is confined to the theorem proofs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  (closureCoverage : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    Nonempty (Σ packet : PacketFor association stages, SupportFor association stages packet))
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureCoverage namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- Static Association coverage suffices for the same accepted caller preservation theorem. -/
theorem preserves_compiled [FunctionCalls.FaultTokens semanticFaults]
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    classical
    let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore),
        Σ packet : PacketFor association stages, SupportFor association stages packet :=
      fun association => Classical.choice (closureCoverage association)
    let packets : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), PacketFor association stages :=
      fun association => (chosen association).1
    let supported : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), SupportFor association stages (packets association) :=
      fun association => (chosen association).2
    intro current id child point
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds.preserves_compiled
      (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
      (profile := profile) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (unique := unique) (actualFunctionType := actualFunctionType) (observations := observations)
      (extension := extension) (semantic := semantic)
      (closurePackets := packets) (closureSupport := supported)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (uninitialized := uninitialized)
      declarations policyFor coercions syntaxTree found typed accepted ports size point

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closureCoverage namedTerminals namedSupport
  sameLedger runtimeLedger uninitialized in
/-- The same local dependent choice retains the independent Source reflection grade. -/
theorem reflects_compiled [FunctionCalls.FaultTokens semanticFaults]
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {rootScope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations invocation.source rootScope context)
    (policyFor : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.PolicyFor policy
      compilation readFuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source rootScope reasonAt)
    (coercions : ∀ id node,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [])
    {rootId : ExpressionId}
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId)
    {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
    (typed : ExpressionHasType invocation.source context rootId node.type)
    {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body compilerFuel compilation
      invocation.source rootScope rootId reasonAt = .ok rootCode)
    (ports : CallsReady (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
      unique declarations policyFor coercions syntaxTree found typed accepted))
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point rootScope rootId rootCode) callFaults size := by
    classical
    let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore),
        Σ packet : PacketFor association stages, SupportFor association stages packet :=
      fun association => Classical.choice (closureCoverage association)
    let packets : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), PacketFor association stages :=
      fun association => (chosen association).1
    let supported : ∀ {mapping world function native bindings parameterCore resultCore}
        (association : Association headers keys bodyRegistry semanticFaults mapping world function native
          bindings parameterCore resultCore), SupportFor association stages (packets association) :=
      fun association => (chosen association).2
    intro current id child point
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveCallerCompilerBounds.reflects_compiled
      (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
      (profile := profile) (wellFormed := wellFormed) (runtime := runtime) (covers := covers)
      (unique := unique) (actualFunctionType := actualFunctionType) (observations := observations)
      (extension := extension) (semantic := semantic)
      (closurePackets := packets) (closureSupport := supported)
      (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (sameLedger := sameLedger) (runtimeLedger := runtimeLedger) (uninitialized := uninitialized)
      stageEq declarations policyFor coercions syntaxTree found typed accepted ports size point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
/-! Connect empty bodies and actual ordinary-owner sequence receipts to the
existing numeric caller/body proof. Associations keep their exact Code and
BodyWith context. Empty bodies obtain their original footer and selected scope
from preparation; sequence packets obtain exact child call readiness.
Principal nonempty and named body support remain explicit static inputs.
Full retained policy, original metadata and sequence conditions are retained.

The combined named/anonymous registry is used throughout. The actual ordinary
caller's exact call ports and ordinary sequence coverage are constructed here.
No expression execution or whole-body meaning law is an input. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories
  (Choice Conditions ChoiceFor ConditionsFor ReadyFor ShapeFor choose_for packet_for support_for)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Syntax)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableAncestryMetadata (eraseRequirements)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)


/-- Construct ports for this exact certificate in the combined registry.
The full original policy receipt is retained independently of the body recipe. -/
private theorem calls_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function scope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {signature : ProgramFunctionSignature}
    (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
    (sourceOwner : function.source.owner = signature.id)
    {invocation : Staging.Recursive.Scope}
    (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType invocation.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context code.reasonAt rootScope rootId rootCode)
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source rootId) :
    CallsReady (compiled := compiled) (invocation := invocation) root := by
  rcases invocation with ⟨origin, actualSource, owned, invocationContext, evidence, guards⟩
  have sameSource : actualSource = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  subst actualSource
  obtain ⟨canonical, issued, _canonicalSelected, ready⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalCallsReady.canonical_calls_ready
      code retained metadata sourceReceipt unique typed root tree
  have guardFrame := RecursiveNamedPreparedScopeCoherence.selected_frame stagePrepared accepted wellFormed signatureMember sourceOwner
    issued sourceReceipt selected
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  obtain ⟨port⟩ := ready compiler path
  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound }⟩

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}

/-- Static sequence grammar and conditions at one exact Code and BodyWith
context. Conditions may depend on the authentic compiler choice, which the
consumer constructs. Ordinary owner membership is a supported-family
restriction; this does not establish coverage for implementation methods. -/
structure OrdinarySequence {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (named : CallableIndexedNamedGeneration.Named)
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults) where
  shape : CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts.Shape code.view function.body
  conditions : (choice : Choice code (stages := (RecursiveNamedPreparedStageScopes.registry stagePrepared))) → Conditions code body choice
  readFuel : ∀ choice, (conditions choice).readFuel = compiled.indexed.fuel
  retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code
  metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
    compiled.indexed named function.source
  signature : ProgramFunctionSignature
  signatureMember : signature ∈ compiled.sourceProgram.signatures.functions
  sourceOwner : function.source.owner = signature.id

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

/-- Ordinary Associations supply static producer conditions at their own Code.
Principal Associations retain their existing dependent packet/support pair;
they are not required to have an ordinary function declaration owner. -/
def SequenceFor {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) : Type :=
  match association with
  | .ordinary _ _ code _ support _ _ _ _ _ _ =>
      OrdinarySequence stagePrepared support.caller.named code support.body
  | .principal _ _ _ _ _ _ _ _ _ _ _ =>
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared), SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet

/-- Static coverage accepts genuine compiler packets and support. Empty bodies
and ordinary sequences retain their existing producer conveniences. No body
execution or semantic law is stored in any branch. -/
inductive OrdinarySequenceFor {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) : Type where
  | sequence (support : SequenceFor stagePrepared association) : OrdinarySequenceFor association
  | empty (body : function.body = []) (unit : function.resultType = .unit) : OrdinarySequenceFor association
  | compiled (supported : Nonempty (Σ packet :
      PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared),
      SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet)) :
      OrdinarySequenceFor association

private theorem sequence_ready {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {expressionSyntax : TypedSource → ExpressionId → Prop}
    {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (code : Code compiled.indexed function scope administrative)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
    (packet : OrdinarySequence stagePrepared named code body)
    (choice : Choice code (stages := (RecursiveNamedPreparedStageScopes.registry stagePrepared)))
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.Ready
      code body choice (packet.conditions choice) := by
  intro invocation selected
  let static := CallableIndexedOwnedPreparedStagedDiscardSequenceRecipeCompilerFactories.static
    code body choice (packet.conditions choice) invocation selected
  refine ⟨?_⟩
  intro expression child used
  have typed := (static.authority expression child used).typed
  have syntaxTree := CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original
    static.edited static.avoids (static.syntaxTree expression child used)
    (CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping.children_reached
      choice.packet.receipt.tree static.edited.metadata expression child used)
  have certificate := static.certificate expression child used
  have atIndices (readFuel : Nat) (reasonAt : ExpressionId → Word)
      (sameFuel : readFuel = compiled.indexed.fuel) (sameReason : reasonAt = code.reasonAt)
      (root : Certificate code.policy code.lowerBody code.compilation readFuel
        (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
        invocation.source body.toContext.context reasonAt
        (CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.parameterScope code) expression child) :
      CallsReady (compiled := compiled) (invocation := invocation) root := by
    subst readFuel
    subst reasonAt
    exact calls_ready stagePrepared code packet.retained packet.metadata sourceReceipt body.unique
      accepted wellFormed packet.signatureMember packet.sourceOwner selected typed root syntaxTree
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  exact atIndices (packet.conditions choice).readFuel choice.packet.reasonAt
    (packet.readFuel choice) choice.reason certificate compiler path

/-- Construct empty or ordinary sequence packets using actual preparation,
retaining the exact principal fallback. The resulting family feeds the same
numeric theorem and original caller restoration. -/
theorem sequence_coverage
    (family : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
    {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
    (accepted : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
      compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore) :
    Nonempty (Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared), SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet) := by
  have input := family association
  cases input with
  | compiled supported => exact supported
  | empty empty unit =>
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
      obtain ⟨sidecar, _issued, selected⟩ :=
        CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
      obtain ⟨packet, packetSupport⟩ := CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts.of_empty
        code provenance.body_recipe support.body empty unit
        (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
      exact ⟨⟨.empty packet, packetSupport⟩⟩
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
      obtain ⟨sidecar, _issued, selected⟩ :=
        CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
      obtain ⟨packet, packetSupport⟩ := CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts.of_empty
        code provenance.body_recipe support.body empty unit
        (RecursiveStageRegistry.scope sidecar code.active function)
        (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
      exact ⟨⟨.empty packet, packetSupport⟩⟩
  | sequence input =>
    cases association with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
        let association := Association.ordinary owner captured code history support origin prefixContext
          globals referenceIndex typed provenance
        obtain ⟨sidecar, _issued, selected⟩ :=
          CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.unique
        have shape : ShapeFor association := input.shape
        obtain ⟨chosen⟩ := choose_for association shape
          (RecursiveStageRegistry.scope sidecar code.active function)
          (RecursiveNamedPreparedStageScopes.anonymous_preserved stagePrepared selected)
        have ready := sequence_ready stagePrepared code support.body input chosen
          support.source_receipt accepted wellFormed
        exact ⟨⟨packet_for association chosen,
          support_for association chosen (input.conditions chosen) ready⟩⟩
    | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
        exact ⟨input⟩

section Caller
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
      headers keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  {before : SourceCompilationPlan.Plan} {fuel budget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram before fuel budget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

variable {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context} {named : CallableIndexedNamedGeneration.Named}
  (code : Code compiled.indexed function localScope administrative)
  (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
  (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
    compiled.indexed named function.source)
  (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
    code.compilation.owner code.active function.source)
  (unique : NodeOccurrencesUnique function.source)
  {signature : ProgramFunctionSignature}
  (signatureMember : signature ∈ compiled.sourceProgram.signatures.functions)
  (sourceOwner : function.source.owner = signature.id)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  (selected : ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).Closure function invocation)
  {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
  (conditions : OriginalConditions compiled code.policy code.compilation compiled.indexed.fuel context invocation
    code.reasonAt rootScope semanticFaults)
  (syntaxTree : Syntax invocation.source rootId)
  {node : ExpressionNode} (found : invocation.source.lookupExpression? rootId = some node)
  (typed : ExpressionHasType invocation.source context rootId node.type)
  {compilerFuel : Nat} {rootCode : SourceCoreBasic.LoweredExpr}
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody compilerFuel
    code.compilation invocation.source rootScope rootId code.reasonAt = .ok rootCode)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry
  (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver profile observations extension semantic family namedTerminals namedSupport
  acceptedPlan wellFormed retained metadata sourceReceipt unique signatureMember sourceOwner
  selected conditions syntaxTree found typed accepted in
/-- The accepted ordinary caller and prepared ordinary sequence bodies feed
numeric preservation, with the original principal and named static support. -/
theorem preserves_compiled [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation (Point rootScope rootId rootCode) callFaults size := by
  have sourceEq : invocation.source = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  have metadataAt : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named invocation.source := by
    rw [sourceEq]
    exact metadata
  have policyFor := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadataAt rootScope code.reasonAt
  let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    conditions.unique conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted
  have ready : CallsReady (compiled := compiled) (invocation := invocation) root :=
    calls_ready stagePrepared code retained metadata sourceReceipt unique
    acceptedPlan wellFormed signatureMember sourceOwner selected typed root syntaxTree
  intro current expression emitted point
  exact CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds.preserves_compiled
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (wellFormed := conditions.wellFormed) (runtime := conditions.runtime)
    (covers := conditions.covers) (unique := conditions.unique)
    (actualFunctionType := conditions.actualFunctionType) (observations := observations)
    (extension := extension) (semantic := semantic)
    (closureCoverage := sequence_coverage stagePrepared family acceptedPlan wellFormed)
    (namedTerminals := namedTerminals) (namedSupport := namedSupport)
    (sameLedger := conditions.sameLedger) (runtimeLedger := conditions.runtimeLedger)
    (uninitialized := conditions.uninitialized)
    conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted ready size point

include bridge receiver profile observations extension semantic family namedTerminals namedSupport
  acceptedPlan wellFormed retained metadata sourceReceipt unique signatureMember sourceOwner
  selected conditions syntaxTree found typed accepted in
/-- The same actual caller and ordinary sequence producer feed numeric
reflection, retaining the original principal and named static support. -/
theorem reflects_compiled [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    ReflectsAt bridge context model (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation (Point rootScope rootId rootCode) callFaults size := by
  have sourceEq : invocation.source = function.source := ((RecursiveNamedPreparedStageScopes.registry stagePrepared)).source selected
  have metadataAt : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named invocation.source := by
    rw [sourceEq]
    exact metadata
  have policyFor := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    retained metadataAt rootScope code.reasonAt
  let root := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions
    conditions.unique conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted
  have ready : CallsReady (compiled := compiled) (invocation := invocation) root :=
    calls_ready stagePrepared code retained metadata sourceReceipt unique
    acceptedPlan wellFormed signatureMember sourceOwner selected typed root syntaxTree
  intro current expression emitted point
  exact CallableIndexedOwnedPreparedStagedMixedCoveredCallerCompilerBounds.reflects_compiled
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (wellFormed := conditions.wellFormed) (runtime := conditions.runtime)
    (covers := conditions.covers) (unique := conditions.unique)
    (actualFunctionType := conditions.actualFunctionType) (observations := observations)
    (extension := extension) (semantic := semantic)
    (closureCoverage := sequence_coverage stagePrepared family acceptedPlan wellFormed)
    (namedTerminals := namedTerminals) (namedSupport := namedSupport)
    (sameLedger := conditions.sameLedger) (runtimeLedger := conditions.runtimeLedger)
    (uninitialized := conditions.uninitialized)
    rfl conditions.declarations policyFor conditions.coercions syntaxTree found typed accepted ready size point

end Caller

section PublicRoot
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
      headers keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  {beforePlan : SourceCompilationPlan.Plan} {planFuel planBudget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram beforePlan planFuel planBudget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) headers root header)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)))
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)
  (heapTyped : Dynamic.HeapWellTyped header.function.context before)
  {arguments : List Dynamic.Value} {payloads : List Value}
  (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world header.bindings arguments payloads)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "rootBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- The actual cached root consumes the mixed numeric family. Ordinary closure
packets come from preparation, and the selected named packet supplies its own
static roots. The exact optional-cell read, parameter entry, body, restoration
and root argument packing are all executed by the existing producers. -/
theorem preserves_root [FunctionCalls.FaultTokens semanticFaults]
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments outcome after) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ value finalStore finalMap finalWorld required,
        (∀ fuel, required ≤ fuel → runStateful fuel
          (.initial root.body
            (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
          .done value finalStore) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared),
        SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet :=
    fun association => Classical.choice (sequence_coverage stagePrepared family acceptedPlan wellFormed association)
  let packet := namedTerminals header selected.member
  have children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) header rootModel
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child rootFaults size := by
    intro child childSelected
    exact CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.preserves (semantic := semantic)
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
      (namedSupport header selected.member) profile wellFormed childSelected extension
      (fun smaller _strict => CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) smaller)
      (fun smaller _strict => CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves_canonical
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) smaller)
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner selected.member
  let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedInvocationPreservation.preserves_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (capture := nativeCapture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (sourceAt := sourceAt)
      packet.layouts selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size children trace (Nat.le_refl _)
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  have read := OptionalCell.read_success Word.zero
    (show Evaluates
      (DataPatternValues.packValues payloads :: payloads.reverse ++
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store
      (.var (header.slot + root.types.length + 1))
      (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) store
      from .var actualReference) capture.read
  have called := SourceCoreCalls.call_success argumentsEvaluated read result.1
  have rootEvaluation : Evaluates
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      store root.body value finalStore := by
    simpa only [selected.shape.2] using called
  obtain ⟨required, run⟩ := evaluation_runStateful_complete_with_sufficient_fuel rootEvaluation
  exact ⟨nativeCapture, value, finalStore, finalMap, finalWorld, required, run, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports in
/-- A completed original root exposes its exact cached named body. Numeric
reflection supplies the staged application and actual returned pool; a staged
rejection remains a staged rejection rather than an ordinary Dynamic fault. -/
theorem reflects_root [FunctionCalls.FaultTokens semanticFaults]
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel
      (.initial root.body
        (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) store) =
      .done value finalStore) :
    ∃ capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world,
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
          (.global function) arguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  classical
  let chosen : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore),
      Σ packet : PacketFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared),
        SupportFor association (RecursiveNamedPreparedStageScopes.registry stagePrepared) packet :=
    fun association => Classical.choice (sequence_coverage stagePrepared family acceptedPlan wellFormed association)
  let packet := namedTerminals header selected.member
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner selected.member
  let nativeCapture := CallableIndexedOwnedFunctionValues.NamedCapture.of_capture capture
  have argumentsEvaluated := selected.arguments_evaluate represented store
  have actualReference :
      (payloads.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot + root.types.length]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) := by
    simpa only [selected.argument_length represented, RecursiveGlobalInitializationMeaning.shift] using
      (RecursiveNamedPublicRootMeaning.globals_agree payloads
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) globalReference)
  obtain ⟨size, measured⟩ := evaluation_has_size (runStateful_evaluation_sound completed)
  rw [selected.shape.2] at measured
  obtain ⟨bodySize, smaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
    argumentsEvaluated actualReference capture.read measured
  have children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
        (headers := headers) (keys := keys) header rootModel
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child rootFaults size := by
    intro child childSelected
    exact CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support.reflects (semantic := semantic)
      (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
      (namedSupport header selected.member) profile wellFormed childSelected extension
      (fun smaller _strict => CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) rfl smaller)
      (fun smaller _strict => CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects_canonical
        (profile := profile) (closurePackets := fun association => (chosen association).1)
        (closureSupport := fun association => (chosen association).2)
        (namedTerminals := namedTerminals) (namedSupport := namedSupport)
        (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
        (extension := extension) (semantic := semantic) rfl smaller)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedInvocationBounds.reflects_invocation
      (functions := rootFunctions) (registry := completion.result.context.registry)
      (owner := owner) (caller := caller) (header := header) (capture := nativeCapture)
      (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
      (prepared := packet.prepared) (aligned := packet.aligned) (stagePrepared := stagePrepared)
      (descriptor := descriptor) (sourceAt := sourceAt)
      packet.layouts selected.member wellFormed stable heapTyped argumentsTyped represented heaps
      supports size children bodyEvaluation (Nat.le_of_lt smaller)
  exact ⟨nativeCapture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩

variable {recipe : SourceCoreIndexedSession.Recipe} {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {encodedValues : SourceCoreCompatibleValues.Context} {options : SourceCoreExecution.RunOptions}
  (sameCompiled : recipe.compiled = compiled)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe (sameCompiled.symm ▸ root)
    world store payloads encodedValues)

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- An actual public success reaches the same cached named body and staged
Source application. Export metadata and the body model's receiving metadata
retain their own actual receipts; no registry equality is invented. -/
theorem public_run_succeeded_reflects [FunctionCalls.FaultTokens semanticFaults]
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
        generation value finalStore actual ∧
      publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
      publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    exported, valueEq, typeEq, budgetEq, sessionAt, trace, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- Public failure retains the actual staged failure relation. In particular,
a nested stage rejection is not relabeled as a Dynamic semantic fault. -/
theorem public_run_failed_reflects [FunctionCalls.FaultTokens semanticFaults]
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
      (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping),
      nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨actualCheckpoint, accepted, resumed⟩ := publicRun
  have same : actualCheckpoint = publicCheckpoint := Except.ok.inj (accepted.symm.trans publicStart)
  subst actualCheckpoint
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨capture, sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    reflects_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) descriptor
      (started.initial.native_done_iff.mp completed)
  exact ⟨actual, value, finalStore, capture, sourceSize, outcome, after, finalMap, finalWorld,
    failed, sessionAt, trace, result⟩

include receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  selected owner caller globalReference stable heapTyped argumentsTyped represented heaps sourceAt supports
  sameCompiled started in
/-- A staged Source Word result is preserved by the same public checkpoint
at sufficient native fuel. The actual export budget remains independent of
the input budget and the staged trace is retained unchanged. -/
theorem public_word_preserved [FunctionCalls.FaultTokens semanticFaults]
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context before
      (.global function) arguments (.value (.word word)) after) :
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world)
      (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
        ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions owner caller header capture context (.value (.word word)) after
          (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  cases sameCompiled
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, completes, result⟩ :=
    preserves_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := owner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports) trace
  have represented := result.2.1
  rw [outputWord] at represented
  have nativeWord : value = .inRight .word (.word word) := by
    cases represented with
    | value payload =>
        obtain ⟨actualWord, sourceEq, nativeEq⟩ := CompatiblePlaceModifier.word_fields observations payload
        have same : word = actualWord := Dynamic.Value.word.inj sourceEq
        cases same
        exact congrArg (fun payload => Core.Value.inRight .word payload) nativeEq
  rw [nativeWord] at completes result
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rootWord := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2.trans resultWord
  rw [rootWord] at requested
  exact ⟨capture, finalStore, finalMap, finalWorld, required,
    fun fuel enough outcome resumed => RecursiveNamedPublicExecutionMeaning.resume_word_succeeded
      atCheckpoint resumed (started.initial.native_done_iff.mpr (completes fuel enough)) requested positive,
    result⟩

end PublicRoot

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds
/-! Preservation and reflection of a supported recursive discard sequence
retain its original staged trace and reached admission. Ordinary returned values and
semantic faults additionally expose the exact lexical exit. A stage rejection
keeps its original scope, call, reason, context and prefix heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Sequence SequenceSupport parameterScope PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)

/-- Ordinary exits and stage rejection retain distinct literal outcomes. -/
inductive ExitReceipt (checked : SourceCoreCompatibleCatalog.Checked)
    (definitions : DataEnvironment) (mapping : LocationMap) (world : StoreTyping)
    (administrative : Core.Context) (program : Program) (stages : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (environment : Dynamic.Environment) (before after : Dynamic.Heap) :
    Staging.Recursive.Outcome → Prop where
  | returned {value : Dynamic.Value}
      (exit : TypedMixedNamedBody.ReachedExit checked definitions mapping world administrative
        program function context scope environment before after (.value value)) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.value value)
  | semanticFault {reason : Dynamic.SemanticFault}
      (exit : TypedMixedNamedBody.ReachedExit checked definitions mapping world administrative
        program function context scope environment before after (.fault reason)) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.fault (.semantic reason))
  | stageRejected {rejectionScope : Staging.Recursive.Scope} {call : ExpressionId}
      {reason : Staging.CallGuard.Fault}
      (trace : Staging.Recursive.Statements program stages invocation context environment before
        function.body context (.fault (.stage rejectionScope call reason)) after) :
      ExitReceipt checked definitions mapping world administrative program stages invocation
        function context scope environment before after (.fault (.stage rejectionScope call reason))

/-- Actual trace and extension receipts construct the appropriate exit branch. -/
theorem exit_receipt_of_trace
    {checked : SourceCoreCompatibleCatalog.Checked} {definitions : DataEnvironment}
    {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {administrative : Core.Context} {program : Program} {stages : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment} {before after : Dynamic.Heap}
    (selected : stages.Closure function invocation)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog)
      mapping world administrative scope environment canonical definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (metadata : Dynamic.HeapMetadataExtend before after) {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Statements program stages invocation context environment before
      function.body context (control outcome) after) :
    ExitReceipt checked definitions finalMap finalWorld administrative program stages invocation
      function context scope environment before after outcome := by
  cases outcome with
  | value value =>
    exact .returned
      (CallableIndexedOwnedPreparedStagedBodyExitReceipts.reached_returned
        selected environments locals maps worlds metadata rfl trace)
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact .semanticFault
        (CallableIndexedOwnedPreparedStagedBodyExitReceipts.reached_semanticFault
          selected environments locals maps worlds metadata rfl trace)
    | stage rejectionScope call reason => exact .stageRejected trace

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {capturedContext : Core.Context} {code : Code compiled.indexed function scope capturedContext}
  {inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
  (packet : Sequence code stages)
  (support : SequenceSupport code inputs stages packet semanticFaults)
  {child : Staging.Recursive.Scope} (selected : stages.Closure function child)

variable {mapping : LocationMap} {world : StoreTyping}
  {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative (parameterScope code) environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before inputs.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : State headers keys ⟨parameterScope code, mapping, world, before, store, canonical⟩)
  (admitted : Admission
    (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
      (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
    inputs.context initial)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry
  (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge
  (compiled := compiled) (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys)

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
  observations extension semantic support selected environments heaps locals agrees actualTyped admitted in
/-- Closed strict child preservation supplies the literal body evaluation once.
The original trace retains its ordinary exit or exact stage rejection alongside
the full reached PostAdmission. -/
theorem preserves_body_with_exit [FunctionCalls.FaultTokens semanticFaults] {size : Nat}
    {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size child inputs.context environment before function.body finalContext bodyOutcome after) :
    finalContext = inputs.context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.receipt.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExitReceipt compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld administrative (Program.ofChecked compiled.sourceProgram) stages child
        function inputs.context (parameterScope code) environment before after outcome ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  have children : ∀ childSize, childSize < size →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize := by
    intro childSize _
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.preserves
      profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
      observations extension semantic childSize
  obtain ⟨sameContext, outcome, sameBody, bodyResult, value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.preserves_body
      (profile := profile) packet support selected environments heaps locals agrees actualTyped
      initial admitted children (Nat.le_refl size) trace
  have original : Staging.Recursive.Statements (Program.ofChecked compiled.sourceProgram) stages
      child inputs.context environment before function.body inputs.context (control outcome) after := by
    simpa only [sameContext, sameBody] using trace.sound
  have exit := exit_receipt_of_trace selected environments locals maps worlds metadata original
  exact ⟨sameContext, outcome, sameBody, bodyResult, value, finalStore, finalMap, finalWorld,
    evaluated, represented, finalHeaps, maps, worlds, frame, metadata, exit, reached, related, post⟩

include closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
  observations extension semantic stageEq support selected environments heaps locals agrees actualTyped admitted in
/-- Closed strict child reflection supplies the body trace once; every result
retains its nested fault representation and reached PostAdmission. -/
theorem reflects_body_with_exit [FunctionCalls.FaultTokens semanticFaults] {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.receipt.body.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        child inputs.context environment before function.body inputs.context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType code.receipt.resultCore callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExitReceipt compiled.compatible.checked
        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
        finalMap finalWorld administrative (Program.ofChecked compiled.sourceProgram) stages child
        function inputs.context (parameterScope code) environment before after outcome ∧
      ∃ reached : State headers keys
        ⟨parameterScope code, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          poolBridge inputs.context function.resultType outcome reached := by
  have children : ∀ childSize, childSize < size →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize := by
    intro childSize _
    exact CallableIndexedOwnedPreparedStagedMixedRecursiveBodyBounds.reflects
      profile closurePackets closureSupport namedTerminals namedSupport receiver stagePrepared
      observations extension semantic stageEq childSize
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, bodyResult, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerBodyBounds.reflects_body
      (profile := profile) packet support selected environments heaps locals agrees actualTyped
      initial admitted children (Nat.le_refl size) completed
  have exit := exit_receipt_of_trace selected environments locals maps worlds metadata trace.sound
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, bodyResult, represented,
    finalHeaps, maps, worlds, frame, metadata, exit, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceBodyExitBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyRecipeCompilerFactories
/-! The retained production recipe constructs a discard packet at the actual
Code and BodyWith context. Its concrete loop policy supplies expression and
statement callbacks internally. Ordinary and principal Associations keep their
own named seed, dictionary and Code; no Produced Site is reconstructed.
Discard shape, original policy and typing authority, declarations and readiness
at the exact issued child certificates remain genuine static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyRecipeCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaBodyRecipes (Retained BodyRecipe)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Discard DiscardSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

/-- One packet retains its exact compiler callback, reason and fuel. -/
structure Choice where
  packet : Discard code stages
  callback : packet.policy.lowerExpression =
    FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  fuel : packet.fuel = code.fuel

/-- Existential production data is consumed in a proof goal, at the same Code.
The body grammar and actual Source-selected child are independent inputs. -/
theorem choose (named : Named) (retained : Retained named code)
    (statement next : StatementId) (rest : List StatementId)
    (firstExpression terminalExpression : ExpressionId)
    (bodyShape : function.body = statement :: next :: rest)
    (shape : CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
      code.view statement firstExpression terminalExpression (next :: rest))
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code policy callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed named compilation.own.assignments diagnostics expression)
    shape (by simpa only [bodyShape] using accepted)
  let packet : Discard code stages := {
    policy := policy
    fuel := code.fuel
    statement := statement
    next := next
    rest := rest
    firstExpression := firstExpression
    terminalExpression := terminalExpression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    body := bodyShape
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed named compilation.own.assignments diagnostics expression
    reason := rfl
    fuel := rfl }⟩

private theorem terminal_reaches {source view : TypedSource}
    {statement next : StatementId} {rest : List StatementId} {expression : ExpressionId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      view expression (next :: rest)) :
    Reaches source ((statement :: next :: rest).map NodeId.statement) (.expression expression) := by
  cases terminal with
  | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates code
  (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice code (stages := stages))

/-- Per-scope original authority remains independent of the retained recipe.
The actual frame, parameter inputs and child paths come from Code and BodyWith. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure function child → LocalView child.source code.view changed
  avoids : ∀ child, stages.Closure function child →
    Avoids child.source (function.body.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure function child →
    PolicyFor code.policy code.compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      (parameterScope code) choice.packet.reasonAt
  viewProfile : PolicyFor code.policy code.compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) code.view
    (parameterScope code) choice.packet.reasonAt
  firstSyntax : Syntax code.view choice.packet.firstExpression
  terminalSyntax : Syntax code.view choice.packet.terminalExpression
  original : ∀ child, stages.Closure function child →
    OriginalConditions compiled code.policy code.compilation readFuel body.toContext.context child
      choice.packet.reasonAt (parameterScope code) semanticFaults

/-- Statement metadata transports only the actual first reference path. -/
theorem first_reached : Reaches function.source (function.body.map NodeId.statement)
    (.expression choice.packet.firstExpression) := by
  have reached : Reaches function.source
      ((choice.packet.statement :: choice.packet.next :: choice.packet.rest).map NodeId.statement)
      (.expression choice.packet.firstExpression) :=
    .statement (.root (by simp))
      (code.viewOfSource.statement choice.packet.receipt.shape.found)
      (by simp [choice.packet.receipt.shape.form, StatementForm.references])
  simpa only [choice.packet.body] using reached

/-- The terminal reference retains its literal second statement occurrence. -/
theorem terminal_reached : Reaches function.source (function.body.map NodeId.statement)
    (.expression choice.packet.terminalExpression) := by
  have reached := terminal_reaches (statement := choice.packet.statement)
    code.viewOfSource choice.packet.receipt.shape.terminal
  simpa only [choice.packet.body] using reached

/-- The checked original issuer receives genuine frame and parameter typing.
It does not obtain raw typing or a source action from metadata equality. -/
theorem static (conditions : Conditions code body choice)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := code.view) (scope := parameterScope code)
      (statement := choice.packet.statement) (next := choice.packet.next) (rest := choice.packet.rest)
      (firstExpression := choice.packet.firstExpression) (terminalExpression := choice.packet.terminalExpression)
      (result := code.receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (code := code.receipt.body) (compiled := compiled) (function := function)
      (context := body.toContext.context) (types := body.toContext.types)
      (invocation := child) (changed := conditions.changed) (roots := function.body.map NodeId.statement)
      (policy := code.policy) (lowerBody := code.lowerBody) (compilation := code.compilation)
      (readFuel := conditions.readFuel) (bodyFuel := code.fuel) (semanticFaults := semanticFaults)
      (native := some compiled.indexed.ancestry.graph.inputs.callable) (active := code.active)
      choice.packet.receipt := {
  edited := conditions.edited child selected
  avoids := conditions.avoids child selected
  sourceProfile := conditions.sourceProfile child selected
  viewProfile := conditions.viewProfile
  callables := code.callables
  expressionCallback := by
    funext childFuel actualSource current expression reasonAt
    have callbackAt := congrArg
      (fun lower : SourceCoreFunctions.ExpressionLowerer =>
        lower childFuel actualSource current expression reasonAt) choice.callback
    simpa only [FunctionCode.children] using callbackAt
  frame := body.frame
  parameters := body.toContext.extended
  sameSource := stages.source selected
  body := choice.packet.body
  firstSyntax := conditions.firstSyntax
  terminalSyntax := conditions.terminalSyntax
  firstReached := by simpa only [stages.source selected] using first_reached code choice
  terminalReached := by simpa only [stages.source selected] using terminal_reached code choice
  conditions := conditions.original child selected }

/-- Only the certificates issued from this same packet need call authority. -/
def Ready (conditions : Conditions code body choice) : Prop :=
  ∀ child selected, CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
    (static code body choice conditions child selected)

/-- The actual issuer constructs both raw Roots and terminal result equality. -/
def support (conditions : Conditions code body choice)
    (ready : Ready code body choice conditions) :
    DiscardSupport code body.toContext stages choice.packet semanticFaults :=
  CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport.of_static choice.packet
    (static code body choice conditions) ready

section Association
variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled
    (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}
  (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)

/-- Each Association retains the literal Code of its own ordinary or principal branch. -/
def ChoiceFor : Type :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ => Choice actualCode (stages := stages)

/-- The supported discard form is a static input at the actual compiler view. -/
def ShapeFor : Prop :=
  match association with
  | .ordinary _ _ actualCode _ _ _ _ _ _ _ _ =>
      ∃ statement next rest firstExpression terminalExpression,
        function.body = statement :: next :: rest ∧
        Nonempty (CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
          actualCode.view statement firstExpression terminalExpression (next :: rest))
  | .principal _ _ actualCode _ _ _ _ _ _ _ _ =>
      ∃ statement next rest firstExpression terminalExpression,
        function.body = statement :: next :: rest ∧
        Nonempty (CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
          actualCode.view statement firstExpression terminalExpression (next :: rest))

/-- Production provenance supplies a recipe at the same branch Code; body shape
and actual child selection remain separate from that recipe. -/
theorem choose_for (shape : ShapeFor association)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (ChoiceFor association (stages := stages)) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      obtain ⟨statement, next, rest, firstExpression, terminalExpression, bodyShape, acceptedShape⟩ := shape
      obtain ⟨acceptedShape⟩ := acceptedShape
      exact choose actualCode actualSupport.caller.named provenance.body_recipe
        statement next rest firstExpression terminalExpression bodyShape acceptedShape child selected
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      obtain ⟨statement, next, rest, firstExpression, terminalExpression, bodyShape, acceptedShape⟩ := shape
      obtain ⟨acceptedShape⟩ := acceptedShape
      exact choose actualCode actualSupport.principal.named provenance.body_recipe
        statement next rest firstExpression terminalExpression bodyShape acceptedShape child selected

/-- Static conditions use the retained branch's actual BodyWith input context. -/
def ConditionsFor (chosen : ChoiceFor association (stages := stages)) : Type :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Conditions actualCode actualSupport.body chosen

/-- No execution law occurs in the per-issued-root readiness proposition. -/
def ReadyFor (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) : Prop :=
  match association with
  | .ordinary _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions
  | .principal _ _ actualCode _ actualSupport _ _ _ _ _ _ =>
      Ready actualCode actualSupport.body chosen conditions

/-- The same chosen discard packet enters the mixed body sum. -/
def packet_for (chosen : ChoiceFor association (stages := stages)) : PacketFor association stages :=
  match association with
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ => .discard chosen.packet
  | .principal _ _ _ _ _ _ _ _ _ _ _ => .discard chosen.packet

/-- Ordinary and principal support keep their own exact Code and body.toContext.
This constructs support for the explicit chosen packet, without universal coverage. -/
def support_for (chosen : ChoiceFor association (stages := stages))
    (conditions : ConditionsFor association chosen) (ready : ReadyFor association chosen conditions) :
    SupportFor association stages (packet_for association chosen) := by
  cases association with
  | ordinary owner captured actualCode history actualSupport origin prefixContext globals referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
  | principal owner captured actualCode history actualSupport origin globals leading referenceIndex typed provenance =>
      exact support actualCode actualSupport.body chosen conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyRecipeCompilerFactories
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady
/-!
Ordinary selected sidecars can reuse the actual canonical call ports. Both
preparation receipts identify their complete post-local source with the same
closure source. Original checked-program typing and ordinary specialization
origins then derive full guard-frame agreement internally.

The original canonical policy, raw typing, finite Calls path and exact compiler
port are preserved. Genuine ordinary origins and complete raw range formation
remain static inputs. Applied-view source provenance and detached method
origins require their own producers before this endpoint covers those scopes.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady
open Core Frontend SourceInference
open CallableIndexedLambdaValues
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate)

/-- The two actual source preparation receipts discharge the full post-local
source equality required by ordinary stage coherence. No frame equality or
specialization-key equality is supplied. -/
theorem ledger_frame_of_receipts
    {program : CheckedProgram} {plan : SourceCoreStageContracts.Plan}
    {owner : SourceCoreStageContracts.Key}
    {canonical selected : SourceCoreStageContracts.Sidecar}
    {canonicalActive selectedActive : TypeSystem.Substitution}
    {source : TypedSource}
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar plan owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar plan selected.caller.key = .ok selected)
    (canonicalSource : LambdaSourceAlignment.SourceReceipt program plan owner canonicalActive source)
    (selectedSource : LambdaSourceAlignment.SourceReceipt program plan selected.caller.key selectedActive source)
    (canonicalOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program canonical.caller)
    (selectedOrigin : RecursiveNamedPublicSpecializationMeaning.Origin program selected.caller)
    (canonicalRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) canonical.caller.parameterSubstitution)
    (selectedRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) selected.caller.parameterSubstitution) :
    CallableLedger.frame selected = CallableLedger.frame canonical := by
  have samePlan : selected.plan = canonical.plan :=
    (CallContractCertificates.sidecar_of_accepted selectedIssued).1.trans
      (CallContractCertificates.sidecar_of_accepted canonicalIssued).1.symm
  have sameSource : selected.caller.function.typedBody.applySubstitution selectedActive =
      canonical.caller.function.typedBody.applySubstitution canonicalActive :=
    (LambdaSourceAlignment.SourceReceipt.source selectedSource selectedIssued).symm.trans
      (LambdaSourceAlignment.SourceReceipt.source canonicalSource canonicalIssued)
  exact CallableOrdinarySpecializationStageCoherence.ledger_frame_eq_of_origins
    wellFormed samePlan selectedOrigin canonicalOrigin selectedRange canonicalRange sameSource

/-- Construct every call port for an ordinary selected sidecar scope from the
actual canonical producer. The sidecar equations identify its one authentic
canonical sidecar, and each original port is transported by derived coherence. -/
theorem ordinary_calls_ready
    {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : CallableIndexedNamedGeneration.Named}
    {function : Dynamic.Closure} {parameterScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {context : SourceSemantics.Context}
    (code : Code compiled.indexed function parameterScope administrative)
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (metadata : CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      compiled.indexed named function.source)
    (sourceReceipt : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source)
    (unique : NodeOccurrencesUnique function.source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (canonical selected : SourceCoreStageContracts.Sidecar)
    (selectedActive : TypeSystem.Substitution)
    (canonicalIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      code.compilation.owner = .ok canonical)
    (selectedIssued : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan
      selected.caller.key = .ok selected)
    (selectedSource : LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      selected.caller.key selectedActive function.source)
    (canonicalOrigin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram canonical.caller)
    (selectedOrigin : RecursiveNamedPublicSpecializationMeaning.Origin compiled.sourceProgram selected.caller)
    (canonicalRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) canonical.caller.parameterSubstitution)
    (selectedRange : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) selected.caller.parameterSubstitution)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr} {rootType : TypeSystem.Ty}
    (typed : ExpressionHasType function.source context rootId rootType)
    (root : Certificate code.policy code.lowerBody code.compilation compiled.indexed.fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      function.source context code.reasonAt rootScope rootId rootCode)
    (tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax function.source rootId) :
    CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled)
      (invocation := RecursiveStageRegistry.scope selected selectedActive function) root := by
  obtain ⟨actualCanonical, actualIssued, _actualSelected, ready⟩ :=
    CallableIndexedOwnedPreparedStagedCanonicalCallsReady.canonical_calls_ready
      code retained metadata sourceReceipt unique typed root tree
  have same : actualCanonical = canonical :=
    Except.ok.inj (actualIssued.symm.trans canonicalIssued)
  cases same
  have guardFrame :
      (RecursiveStageRegistry.scope selected selectedActive function).guards =
        (RecursiveStageRegistry.scope canonical code.active function).guards :=
    ledger_frame_of_receipts wellFormed canonicalIssued selectedIssued sourceReceipt selectedSource
      canonicalOrigin selectedOrigin canonicalRange selectedRange
  intro callFuel callScope callId callee ids callMetadata lowered compiler path
  obtain ⟨port⟩ := ready compiler path
  exact ⟨{
    prepared := port.prepared
    sidecar := port.sidecar
    caller := port.caller
    view := port.view
    guardFrame := guardFrame.trans port.guardFrame
    originalUnique := port.originalUnique
    sourceParent := port.sourceParent
    calleeNode := port.calleeNode
    calleeFound := port.calleeFound
  }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryScopeCallsReady
end
