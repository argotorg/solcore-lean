import Solcore.SourceSemantics.CoreLowering.CellAwareScopeGeneralizedReadBounds
import Solcore.SourceSemantics.CoreLowering.CellAwarePhysicalFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopedReadFacts

/-! Actual named generalized reads implement the scoped callee port. Both
execution directions use the original source dictionary and the actual stored
row. The same read-time frame and unchanged caller state remain available to
the subsequent ordered argument and application proofs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {named : SourceCoreGeneralFunctions.Function}
  {bodyRegistry rawRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions

private theorem represented_of_typed
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {function : Dynamic.Closure} {native : Core.Value} {bindings parameter result}
    (member : GeneralizedLocalMaterializedAssociation.Association compiled mapping world function native bindings parameter result)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (framed : member.AtFrame owner.key.frameLocation)
    {sourceType : TypeSystem.Ty} (typed : Dynamic.ValueHasType context heap (.closure function) sourceType) :
    ValueRep compiled.compatible.checked rawRegistry functions mapping world sourceType (.closure function) native
      (CallableContract.functionType parameter result) := by
  induction sourceType with
  | function parameter result _ _ =>
    cases typed
    exact .function (.generalized member owner framed)
  | comptime inner ih =>
    cases typed with
    | comptime innerTyped => exact .compatible (actual := inner) rfl (ih innerTyped)
  | _ => cases typed

include profile in
/-- The reached Source instantiation produces the actual indexed view while
retaining the physical frame required by indirect application. -/
theorem preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (size : Nat) :
    CellAwareScopeGeneralizedReadBounds.PreservesAt bridge context model named registry invocation faults size := by
  intro scope id reasonAt lowered certificate recipe node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted _authority physical owner ownerLocation trace
  have nodeEq := Option.some.inj (certificate.observations.originalFound.symm.trans found)
  cases nodeEq
  obtain ⟨reached⟩ := GeneralizedLocalScopedReadFacts.resolve certificate recipe physical locals
  have originalEq := Option.some.inj (recipe.observations.originalFound.symm.trans certificate.observations.originalFound)
  have binderEq := GeneralizedLocalScopedReadFacts.binder certificate recipe
  have originalForm : certificate.observations.original.form =
      .reference recipe.observations.name (.local certificate.read.binder) := by
    simpa only [originalEq, binderEq] using recipe.observations.originalForm
  obtain ⟨owned, substitution, produced, instantiation, sameOutcome, sameHeap⟩ :=
    GeneralizedLocalSourceRead.invert unique certificate.observations.originalFound originalForm
      certificate.observations.originalCoercions reached.lookup reached.located.sourceRead reached.located.descriptor
      requirementsUnique covers trace
  cases sameHeap
  cases sameOutcome
  have descriptorTyped := ((admitted.heap _ reached.located.sourceRead.member).generalized_inv reached.located.descriptor).2
  have nodeType := GeneralizedLocalSourceRead.raw_type unique certificate.observations.originalFound
    certificate.observations.originalCoercions sourceTyped
  have sourceValueTyped := descriptorTyped.instantiateHasType
    (reached.fields.signatures ▸ catalog) reached.fields covers instantiation
  rw [nodeType] at sourceValueTyped
  have normalized := Option.some.inj (certificate.read.nodeFound.symm.trans certificate.observations.found)
  have rawType : certificate.observations.original.rawType = certificate.read.node.rawType := by
    rw [normalized, certificate.observations.rawType]
  obtain ⟨material, view, _materialFrame, viewFrame, nativeType, evaluated, member, atFrame⟩ :=
    GeneralizedLocalNamedReadFormation.preserves certificate recipe reached.located reached.frames
      reached.caller reached.binder reached.contextExtension environments reached.lookup agrees
      descriptorTyped.code.graph.nodeOccurrencesUnique instantiation reached.scheme rawType profile
      physical.carried rfl (agrees physical.reference) physical.read actualTyped
  refine ⟨.inRight .word view.native, store, mapping, world, evaluated, ?_, ?_, heaps,
    .refl _, .refl _, .refl _ _, Dynamic.HeapMetadataExtend.refl _,
    CellAwareScopeAuthority.Effect.refl _ _ _ _, initial, callerProtocol.refl initial, ?_⟩
  · rw [nativeType]
    exact .value (represented_of_typed profile member owner (by simpa only [ownerLocation] using atFrame) sourceValueTyped)
  · intro value same
    cases same
    exact ⟨_, _, _, _, _, rfl, rfl, member, by simpa only [ownerLocation] using atFrame⟩
  · exact ⟨admitted.rows, by intro value same; cases same; exact ⟨sourceValueTyped, admitted.heap⟩⟩

include profile in
/-- Native completion reconstructs the actual Source dictionary and retained
closure. Determinism compares only the two executions of this same emitted
read; it does not identify different creation or call histories. -/
theorem reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (requirementsUnique : RequirementIdsUnique context)
    (covers : invocation.evidence.Covers context)
    (catalog : SignatureCatalogWellFormed context.signatures)
    (size : Nat) :
    CellAwareScopeGeneralizedReadBounds.ReflectsAt bridge context model named registry invocation faults size := by
  intro scope id reasonAt lowered certificate recipe node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerLocation completed
  have nodeEq := Option.some.inj (certificate.observations.originalFound.symm.trans found)
  cases nodeEq
  obtain ⟨reached⟩ := GeneralizedLocalScopedReadFacts.resolve certificate recipe physical locals
  have originalEq := Option.some.inj (recipe.observations.originalFound.symm.trans certificate.observations.originalFound)
  have binderEq := GeneralizedLocalScopedReadFacts.binder certificate recipe
  have originalForm : certificate.observations.original.form =
      .reference recipe.observations.name (.local certificate.read.binder) := by
    simpa only [originalEq, binderEq] using recipe.observations.originalForm
  obtain ⟨owned, substitution, produced, sourceSize, _instantiation, trace⟩ :=
    GeneralizedLocalSourceRead.trace_of_typed (program := Program.ofChecked compiled.sourceProgram) (registry := registry)
      unique certificate.observations.originalFound originalForm certificate.observations.originalCoercions
      sourceTyped locals reached.lookup reached.located.sourceRead reached.located.descriptor reached.fields
      reached.requirements reached.matched covers
  obtain ⟨native, nativeStore, finalMap, finalWorld, evaluated, represented, strong, finalHeaps,
      maps, worlds, frame, metadata, effect, final, related, post⟩ :=
    preserves bridge profile unique requirementsUnique covers catalog sourceSize certificate recipe
      certificate.observations.originalFound sourceTyped environments heaps locals agrees actualTyped
      initial admitted authority physical owner ownerLocation trace
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  exact ⟨sourceSize, _, before, finalMap, finalWorld, trace, represented, strong, finalHeaps,
    maps, worlds, frame, metadata, effect, final, related, post⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareNamedGeneralizedReadBounds
