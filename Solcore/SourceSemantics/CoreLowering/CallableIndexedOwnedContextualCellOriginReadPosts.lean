import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginExpressionPosts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
import Solcore.SourceSemantics.CoreLowering.ReachedLoweredReadOutcomePorts

/-! Certified local reads use the positive receiving model directly. The
original finite producer covers initialized values, actual uninitialized faults
and real lazy mapping writes. Its result/cells and the actual protocol transport
witness are retained together with Source admission at that same reached state.
Positive callable classification projects this returned payload, including its
compatible raw view. Formation and whole indirect call branches remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginReadPosts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedContextualCellOrigins (CellOrigins PostWithOrigins post_at_same_state)
open CallableIndexedOwnedContextualCalleeOriginReadReceipts (CalleeAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  {fuel : Nat} {reasonAt : ExpressionId → Word}

/-- The static read certificate retains real declaration/occurrence typing;
there is no initialized-cell or positive Member assumption in this certificate. -/
abbrev Reads (context : SourceSemantics.Context) (source : TypedSource)
    (fuel : Nat) (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionReads.LoweredRead fuel (.initial compiled.compatible.checked) source context reasonAt

section Family
variable
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  (policies : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (.initial compiled.compatible.checked)
    source context reasonAt faults)
  (unique : NodeOccurrencesUnique source)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)

include extension policies unique transport wellFormed runtime covers in
/-- One original read producer handles every actual read branch. The positive
heap is returned by that producer, including its real mapped-cell write; frame
transport is used only to construct the actual protocol endpoint. -/
theorem preserves_reads_at (size : Nat) :
    CallableIndexedOwnedContextualCellOriginExpressionPosts.PreservesAt
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source (Reads (compiled := compiled) context source fuel reasonAt) size := by
  intro scope id lowered receipt node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments cells locals agrees _typed initial admitted trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨value, finalStore, evaluated, represented, finalCells, frame, metadata, _faultOrigin⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_preserves certificate
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding
      environments cells locals agrees (policies certificate binding environment before) unique trace.sound
  have actualResult : GenericExpressionMeaning.ResultRepresents
      (CallableIndexedOwnedContextualCellOriginExpressionPosts.model headers keys bodyRegistry registry faults profile)
      mapping world node.type lowered.type faults outcome value := by
    simpa only [nodeEq, typeEq, GenericExpressionMeaning.ResultRepresents,
      CallableIndexedOwnedContextualCellOriginExpressionPosts.model, SourceCoreCompatibleValues.Context.initial]
      using represented
  let reached := transport.extend initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world) frame metadata
  have admittedPost := CallableIndexedOwnedSourceAdmission.after_expression_sized initial reached admitted
    wellFormed runtime covers locals sourceTyped trace frame
  exact ⟨value, finalStore, mapping, world, evaluated, actualResult, finalCells,
    .refl _, .refl _, frame, metadata, reached,
    transport.related initial (.refl _) (.refl _) frame metadata,
    post_at_same_state bridge profile reached admittedPost finalCells actualResult⟩

include extension policies unique transport wellFormed runtime covers in
/-- The actual completed read reconstructs its own independent Source grade.
No Source run is supplied to reflection, and no native evaluation is repeated
for positive classification or Source admission. -/
theorem reflects_reads_at (size : Nat) :
    CallableIndexedOwnedContextualCellOriginExpressionPosts.ReflectsAt
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge profile context evidence source (Reads (compiled := compiled) context source fuel reasonAt) size := by
  intro scope id lowered receipt node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments cells locals agrees _typed initial admitted completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨outcome, after, sourceTrace, represented, finalCells, frame, metadata, _faultOrigin⟩ :=
    ReachedExpressionPrimitiveOutcomeProviders.read_completed certificate
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
      extension (Program.ofChecked compiled.sourceProgram) context evidence binding
      environments cells locals agrees unique (policies certificate binding environment before) completed.sound
  have actualResult : GenericExpressionMeaning.ResultRepresents
      (CallableIndexedOwnedContextualCellOriginExpressionPosts.model headers keys bodyRegistry registry faults profile)
      mapping world node.type lowered.type faults outcome value := by
    simpa only [nodeEq, typeEq, GenericExpressionMeaning.ResultRepresents,
      CallableIndexedOwnedContextualCellOriginExpressionPosts.model, SourceCoreCompatibleValues.Context.initial]
      using represented
  obtain ⟨sourceSize, trace⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size sourceTrace
  let reached := transport.extend initial (LocationMap.Extends.refl mapping) (WorldExtends.refl world) frame metadata
  have admittedPost := CallableIndexedOwnedSourceAdmission.after_expression_sized initial reached admitted
    wellFormed runtime covers locals sourceTyped trace frame
  exact ⟨sourceSize, outcome, after, mapping, world, trace, actualResult, finalCells,
    .refl _, .refl _, frame, metadata, reached,
    transport.related initial (.refl _) (.refl _) frame metadata,
    post_at_same_state bridge profile reached admittedPost finalCells actualResult⟩
end Family

section ActualView
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {reason : Word} {code : Expr}
  (certificate : CompatibleExpressionReads.Certificate fuel (.initial compiled.compatible.checked)
    source scope id reason code)
  (binding : CompatibleExpressionReads.StaticBinding certificate context)

include binding in
/-- The genuine declared scheme fixes the raw cell type. Source occurrence
and declaration typing supply the runtime view used by the original read leaf;
equal native tags are not used to recover this Source fact. -/
theorem initialized_at_binding
    {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {value : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some value, none⟩)
    (cellType : raw = certificate.declared.scheme.body) :
    ∃ target native type,
      CallableIndexedOwnedContextualCalleeOriginReadReceipts.InitializedReadAt
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw value target native type ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        mapping world certificate.node.type value native type := by
  obtain ⟨target, native, type, actualRead⟩ :=
    CallableIndexedOwnedContextualCalleeOriginReadReceipts.initialized_read_at profile cells read
  have view : SourceCoreRawMetadata.runtimeType certificate.node.type = SourceCoreRawMetadata.runtimeType raw :=
    binding.occurrence.trans (congrArg SourceCoreRawMetadata.runtimeType cellType).symm
  exact ⟨target, native, type, actualRead, actualRead.payload_at_view profile view⟩

include binding in
/-- Actual Source local agreement supplies the cell-type equality used above.
Both lookups and reads are aligned by their original finite uniqueness proofs;
no raw type is reconstructed from a native payload. -/
theorem initialized_at_local
    {environment : Dynamic.Environment} {location : Dynamic.Location} {raw : TypeSystem.Ty}
    {value : Dynamic.Value}
    (cells : CellOrigins headers keys bodyRegistry registry faults profile mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads heap location ⟨raw, some value, none⟩) :
    ∃ target native type,
      CallableIndexedOwnedContextualCalleeOriginReadReceipts.InitializedReadAt
        (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
        (registry := registry) (faults := faults) (mapping := mapping) (world := world)
        (heap := heap) (store := store) profile location raw value target native type ∧
      CallableIndexedOwnedContextualCellOrigins.PayloadOrigins headers keys bodyRegistry registry faults profile
        mapping world certificate.node.type value native type := by
  obtain ⟨typedLocation, cell, typedLookup, typedRead, cellType, _storage⟩ := locals.lookup binding.declared
  have sameLocation := lookup.functional typedLookup
  subst typedLocation
  have sameCell := read.functional typedRead
  subst cell
  exact initialized_at_binding profile context source certificate binding cells read cellType
end ActualView

/-- At a successful callable read, classify only the actual returned positive
payload. This keeps the same reached caller, all its rows and cells, genuine raw
typing and the original Member/global/builtin alternative behind its raw view. -/
theorem callee_at_post
    {raw : TypeSystem.Ty} {type : Core.Ty} {value : Dynamic.Value} {native : Core.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile raw type (.value value) (.inRight .word native) reached)
    (callable : IsFunction value) :
    Admission bridge context reached ∧ Dynamic.ValueHasType context index.heap value raw ∧
    CellOrigins headers keys bodyRegistry registry faults profile index.mapping index.world index.heap index.store ∧
    CalleeAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (faults := faults) (mapping := index.mapping) (world := index.world) raw value native type := by
  obtain ⟨admitted, typed, payload⟩ := post.at_value
  exact ⟨admitted, typed, post.cells,
    CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile payload callable⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCellOriginReadPosts
