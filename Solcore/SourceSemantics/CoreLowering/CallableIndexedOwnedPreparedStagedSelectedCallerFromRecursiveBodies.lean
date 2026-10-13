import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds

/-! An arbitrary admitted caller consumes the closed concrete pool body
  family. Its protocol carrier remains independent of the pool's universe;
  the existing call producers restore its actual reached state around the
  literal returned pool. Every child expression and called-body semantic law
  is constructed internally from static original Source authority.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
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
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Source traces retain every reached caller effect and their original
  admission receipt while recursive body meaning is supplied internally. -/
theorem preserves {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (size : Nat) :
    PreservesAt bridge context model stages invocation
      (Point scope expression lowered) callFaults size := by
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.preserves
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) (closureTerminals := closureTerminals)
      (namedTerminals := namedTerminals) (closureSupport := closureSupport) (namedSupport := namedSupport)
  intro current id child point
  exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.preserves_reached
    bridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
    root.support.covers root.support.unique root.support.actualFunctionType observations
    extension semantic closureTerminals namedTerminals root.support.sameLedger
    root.support.runtimeLedger root.support.uninitialized size
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.closure_preserves_below
      closureTerminals closureSupport (fun smaller _ => bodies smaller) within)
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_preserves_below
      namedTerminals namedSupport (fun smaller _ => bodies smaller) within)
    root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _) point

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
/-- Native completion returns its authentic independently graded Source
  trace, exact nested failure scope and restored caller relation and post. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (size : Nat) :
    ReflectsAt bridge context model stages invocation
      (Point scope expression lowered) callFaults size := by
  have bodies : ∀ childSize,
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize :=
    CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.reflects
      (receiver := receiver) (stagePrepared := stagePrepared) (observations := observations)
      (extension := extension) (semantic := semantic) (closureTerminals := closureTerminals)
      (namedTerminals := namedTerminals) (closureSupport := closureSupport) (namedSupport := namedSupport) stageEq
  intro current id child point
  exact CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.reflects_reached
    bridge receiver stagePrepared profile root.support.wellFormed root.support.runtime
    root.support.covers root.support.unique root.support.actualFunctionType observations
    extension semantic closureTerminals namedTerminals root.support.sameLedger
    root.support.runtimeLedger root.support.uninitialized stageEq size
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.closure_reflects_below
      closureTerminals closureSupport (fun smaller _ => bodies smaller) within)
    (fun childSize within => CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.named_reflects_below
      namedTerminals namedSupport (fun smaller _ => bodies smaller) within)
    root.support.certificate (.root (by simp)) root.support.noMethods root.support.noDirect root.support.noIndexes root.support.callsReady size (Nat.le_refl _) point

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies
