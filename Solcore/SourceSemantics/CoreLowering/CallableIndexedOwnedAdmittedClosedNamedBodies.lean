import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedNamedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! Closed named callees have authentic static profiles with no expression
leaves. This bounded grammar supports the original nil, absent-let, block and
return-unit forms accepted by that profile. It supplies no mixed-body closure.
The existing singleton mutual proof consumes each real parameter receipt and
returns its exact reached pool and Source exit; no execution law is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState ProtectedStateTransition

/-- The closed callee profile has no executable expression leaves. -/
def noExpressions (_ : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  fun _ _ _ => False

def noExpressionSyntax (_ : ExpressionId) : Prop := False

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)

/-- All authentic hook, Source, allocation and static profile fields are kept. -/
abbrev Receipt {index : Index} (argumentsPool : State headers keys index)
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (arguments : List Dynamic.Value) :=
  CallableIndexedOwnedAdmittedNamedExpressionHeads.ParameterReceipt
    (owner := owner) (functions := functions) (registry := registry) (faults := faults)
    (certificates := fun _ => noExpressions) (expressionSyntax := fun _ => noExpressionSyntax)
    (diagnosticPolicy := .reachable) (runtime := true) argumentsPool header arguments

variable {index : Index} {argumentsPool : State headers keys index}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program} {arguments : List Dynamic.Value}
  (receipt : Receipt (registry := registry) (faults := faults) functions owner argumentsPool header arguments)
  (wellFormed : ProgramWellFormed program)
  (sameLayout : header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

private def marked : MarkedAllocation.Producer (protocol headers keys)
    header.layouts compiled.indexed.ancestry.layout.frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  sameLayout.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (producer : MarkedAllocation.Producer (protocol headers keys)
      second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    {location : Location} {native : NativeFrame}
    (ready : OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    OrdinaryAllocation.ReadyAt ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout).toOrdinary location native :=
  ready_layout (headers := headers) (keys := keys) (registry := registry) functions sameLayout
    (CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner (headers := headers)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include wellFormed sameLayout extension faithful observations in
/-- The existing measured closer proves the exact computed entry, including
ReachedExit. Only impossible static expression leaves are discharged. -/
theorem parameter_preserves (size : Nat) :
    CallableRuntimeBodyEntryContracts.PreservesAt (registry := registry) (faults := faults)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (fun _ => acquire (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro outcome after trace
  exact meaning (receipt.admitted_entry wellFormed).original trace

include wellFormed sameLayout extension faithful observations functionTypes in
/-- The original native completion retains its own size and returns an
independently measured Source body at the same actual parameter entry. -/
theorem parameter_reflects (size : Nat) :
    CallableRuntimeBodyEntryContracts.ReflectsAt (registry := registry) (faults := faults)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions program (receipt.admitted_entry wellFormed).original size := by
  have meaning := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => CallableRuntimeBodyStaticOrigins.named true receipt.profile receipt.escaped)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => marked (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (fun _ => acquire (headers := headers) (keys := keys) (registry := registry) functions sameLayout)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by intro _ context valid budget child within below scope id lowered impossible; cases impossible)
    size ()
  intro value finalStore completed
  exact meaning (receipt.admitted_entry wellFormed).original completed

include wellFormed sameLayout extension faithful observations in
/-- Every callback is derived at its actual receipt; the original continuation
agreement remains part of the production interface. -/
theorem source_bodies (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.SourceBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt _agreement size _smaller
  exact parameter_preserves functions owner actualReceipt wellFormed sameLayout extension faithful observations size

include wellFormed sameLayout extension faithful observations functionTypes in
/-- The real measured prefix and saved caller write select the same exact
native callback; no comparison to its reflected Source grade is used. -/
theorem native_bodies (budget : Nat) :
    CallableIndexedOwnedAdmittedNamedExpressionHeads.NativeBodiesFor
      (headers := headers) (keys := keys) (owner := owner) (functions := functions)
      (registry := registry) (faults := faults) (certificates := fun _ => noExpressions)
      (expressionSyntax := fun _ => noExpressionSyntax) (diagnosticPolicy := .reachable)
      (runtime := true) wellFormed header budget := by
  intro initial argumentsPool arguments actualReceipt prefixSize bodyStore value finalStore
    _prefixRun _prefixWithin _restored size _smaller
  exact parameter_reflects functions owner actualReceipt wellFormed sameLayout extension faithful observations functionTypes size

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedClosedNamedBodies
