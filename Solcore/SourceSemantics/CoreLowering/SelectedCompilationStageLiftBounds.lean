import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport

/-! Ordinary trace bounds for lifting selected expressions. The preconditions
are the actual physical caller state used by the closed staged preservation
family. A constructed child trace can therefore supply the reached state for
the next ordinary child, including its retained callable origins. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open SelectedCompilationMixedRootSupport (RootAt)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

section Bound
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate)

def LiftsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id outcome after →
    ExpressionLift program registry invocation context environment before id outcome after
end Bound

section Roots
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)

def LiftsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) size
end Roots

section ActualPreservation
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include issued extension in
/-- The already closed physical proof supplies reached states for constructed
staged prefixes. Its input is a finite trace, without an execution callback. -/
theorem preserves_roots (size : Nat) :
    SelectedCompilationMixedRootBounds.PreservesRootsAt (headers := headers) (keys := keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry
        (SelectedCompilationPhysicalProgramSupport.functions support))
      (SelectedCompilationPhysicalProgramSupport.stages compiled)
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) size := by
  exact SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
    issued (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
    support.profile support.bodyTyping support.certificates
    (SelectedCompilationPhysicalProgramSupport.observations support)
    (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
    (SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport
    support.owners support.methods size
end ActualPreservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
