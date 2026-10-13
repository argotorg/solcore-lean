import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalRawDirectBounds

/-! Every raw argument and named body comes from the same physical numerical
family. The original call metadata and conversion partition remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SelectedCompilationMixedRootSupport (CoercedDirectRoot RootAt)
open SelectedCompilationMixedRootBounds
open CallableIndexedOwnedAdmittedStagedExpressionBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
  {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {rawType : TypeSystem.Ty}
  (root : CoercedDirectRoot compiled headers stages policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry} (faults : RecursiveStageMeaning.FaultRep)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "callerBridge" => CallableIndexedOwnedPhysicalCanonicalState.ordinaryCaller
  owner compilation.administrativePrefix keyPhysical.locations

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

private theorem argument_types : root.argumentTypes =
    root.port.header.bindings.map (fun binding => binding.1.scheme.body) := by
  obtain ⟨types, _callee, application, typed⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types root.actual root.unique root.typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types
    root.actual root.port.toReady root.shape root.runtime.signatures application
  exact (tree_types root.argumentTree root.unique typed).trans rows.1

include owners in
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → PreservesRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size)
    (namedBodies : ∀ size, size ≤ budget → ∀ {child : Staging.Recursive.Scope},
      stages.Closure root.port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
        (headers := headers) (keys := keys) root.port.header model stages child faults size)
    (size : Nat) (within : size ≤ budget) :
    SelectedCompilationPhysicalRawDirectBounds.RawPreservesAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  have childMeaning : PreservesBelow (callerBridge).forgetSlots context model
      stages invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationPhysicalRawDirectBounds.preserves
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique owners root.certified root.shape root.runtime
    size (argument_types root ▸ root.argumentTree) childMeaning
    (fun selected => namedBodies size within selected)

variable (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named root.port.header.named.signature.key))

include stagePrepared stageEq descriptor in
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → ReflectsRootsAt (headers := headers) (keys := keys)
      model stages semanticFaults faults size)
    (namedBodies : ∀ size, size ≤ budget → ∀ {child : Staging.Recursive.Scope},
      stages.Closure root.port.header.function child →
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
        (headers := headers) (keys := keys) root.port.header model stages child faults size)
    (size : Nat) (within : size ≤ budget) :
    SelectedCompilationPhysicalRawDirectBounds.RawReflectsAt
      (context := context) (receiving := receiving) owner root.actual callerBridge functions faults stages size := by
  subst stages
  have childMeaning : ReflectsBelow (callerBridge).forgetSlots context model
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) invocation root.argumentCertificate faults size := by
    intro smaller strict current id code member
    obtain ⟨type, ⟨supported⟩⟩ := root.argumentRoots member
    exact children smaller (Nat.lt_of_lt_of_le strict within)
      (RootAt.ofRoot supported) owner keyPhysical ⟨rfl, rfl, rfl⟩
  exact SelectedCompilationPhysicalRawDirectBounds.reflects
    owner root.actual root.port.toPort root.port.evidence callerBridge keyPhysical
    (fun state => state.physical) functions faults root.unique root.certified root.shape root.runtime
    stagePrepared descriptor
    size (argument_types root ▸ root.argumentTree) childMeaning
    (fun selected => namedBodies size within selected)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalCoercedDirectRawBounds
