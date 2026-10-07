import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! An authentic builtin method profile closes its actual body and invocation
without semantic callbacks. Its original builtin/data/control/read expression
grammar is proved internally, while lexical and parameter allocations use the
real marked producer and retain their reached ordered pool records. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterMeaning SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallablePreparedMethodRuntimeMeaning

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
  {code : Expr} (generation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code)
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile generation (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) sourceBody dictionary administrative registry faults)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction generation.own.table.escapedReason)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))

/-- Every original static method field and its full independent dictionary
remain in the existing builtin origin factory. -/
abbrev origin := CallableRuntimeBodyStaticOrigins.method_builtin generation profile escaped

include extension faithful observations functionTypes uninitialized missing in
/-- The original shared measured family closes this authentic builtin profile.
Only its proved expression fragment is lifted through administrative effects;
body allocation still consumes the actual marked producer and selected gate. -/
theorem body_preserves_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin generation profile escaped) functions extension program faithful observations
    (protocol headers keys) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
      exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
        (ProtectedExpressionMeaning.preserves_of_typed (ProtectedStateTransition.entry (protocol headers keys))
          (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
            program dictionary valid.ledger valid.runtime profile.body.unique uninitialized missing)) child)
    size ()

include extension faithful observations functionTypes uninitialized missing in
/-- Reflection uses the same exact runtime ledger and original source method
profile. Its source grade is reconstructed from each original native child,
with all actual body pool transitions retained by the shared family. -/
theorem body_reflects_at (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin generation profile escaped) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (registry := registry) (faults := faults)
    (fun _ : Unit => origin generation profile escaped) functions extension program faithful observations functionTypes
    (protocol headers keys) (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => CallableIndexedOwnedMarkedAllocation.producer headers keys
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (by
      intro _ location native gate
      exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) gate)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (by
      intro _ context valid budget child _within _callees
      apply ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ (administrativeTransport headers keys)
      exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
        (ProtectedExpressionMeaning.reflects_of_typed (ProtectedStateTransition.entry (protocol headers keys))
          (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
            program dictionary valid.ledger valid.runtime uninitialized missing)) child)
    size ()

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
  (installed : Installed generation (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (sourceBody := sourceBody) (administrative := administrative)
    functions mapping world before store callerEnvironment)
  (represented : Arguments (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world named.inputs arguments payloads)
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (sameFrame : installed.frameLocation = owner.key.frameLocation)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)

include profile escaped represented owner sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- An original source method outcome runs the actual hook, parameters and
closed builtin body. The exact reached body pool supplies caller restoration;
no expression or body meaning is a premise. -/
theorem invocation_preserves {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.BodyOutcome program size sourceBody dictionary before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (generation.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_preserves_bounded_with generation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin generation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (fun child _strict => body_preserves_at generation profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) trace (Nat.le_refl size)

include profile escaped represented owner sameFrame heaps extension faithful observations functionTypes uninitialized missing in
/-- Completed native method execution reflects its independent source outcome
through the same actual parameter/body/restoration chain and full dictionary.
The returned caller state preserves the reached pool's ordered records. -/
theorem invocation_reflects {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (generation.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyOutcome program sourceSize sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩ := by
  exact CallableIndexedOwnedMethodInvocationBounds.invocation_reflects_bounded_with generation
    (CallablePreparedMethodCatalogHookMeaning.of_builtin generation profile) functions escaped
    (fun valid extended => valid.extend extended) (fun valid => valid)
    installed represented owner caller sameFrame heaps size
    (fun child _strict => body_reflects_at generation profile functions extension faithful observations functionTypes
      escaped uninitialized missing child) completed (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodBuiltinBounds
