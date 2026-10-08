import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaEntryBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionState
import Solcore.SourceSemantics.CoreLowering.TypedMixedNamedBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInvocationBounds

/-! The original raw lambda parameter receipts determine every operational
body field. The authentic ClosureFrame
is the sole extra field needed to reconstruct a Source call after reflection.
No StaticOrigin, escaped token, or completed body law is stored here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)

/-- The function and input context already come from this exact Code. -/
structure BodyFields
    (code : Code compiled.indexed function scope captured.administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code) : Prop where
  frame : Dynamic.ClosureFrame program function

/-- Complete meaning at one actual Source-produced parameter receipt. The
body callback retains the original exit and the same actual reached pool. -/
def SourceAt
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩)
    (size : Nat) : Prop :=
  ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size function inputs.context
      entry.entry.environment entry.entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.entry.actualBody entry.entry.store
        (code.receipt.body.rename entry.entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.entry.mapping finalMap ∧ WorldExtends entry.entry.world finalWorld ∧
      AdministrativePreserved entry.entry.mapping entry.entry.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions
        finalMap finalWorld captured.administrative program function inputs.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.entry.environment entry.entry.heap after outcome ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, finalStore, entry.entry.canonical⟩

/-- The native prefix is retained at its original strict grade. Source grade
and body outcome are reconstructed independently at that same entry. -/
def NativeAt
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (size : Nat) : Prop :=
  ∀ {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (code.receipt.body.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function inputs.context
        entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit compiled.compatible.checked compiled.indexed.layouts.definitions
        finalMap finalWorld captured.administrative program function inputs.context
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition (protocol headers keys) reached
        ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
          finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- This intermediate contract is supplied by strict same-family body IH in
the final consumer; no uniform completed body law is asserted here. -/
def SourceContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (added : Environment), added.length = code.receipt.loweredParameters.length →
      entry.entry.canonical = added ++ captured.canonical →
  ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.entry.mapping, entry.entry.world, entry.entry.heap, entry.entry.store, entry.entry.canonical⟩,
    RecursiveNamedCatalogInvocationBounds.Below budget
      (SourceAt (faults := faults) captured code history inputs functions owner caller entry reached)

def NativeContinuation (budget : Nat) : Prop :=
  ∀ (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current),
  ∀ reached : State headers keys
      ⟨code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope,
        entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩,
    RecursiveNamedCatalogInvocationBounds.Below budget
      (NativeAt (faults := faults) captured code history inputs functions owner caller entry reached)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaEntryBodyContracts
