import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementWrites
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrayMemrefs

/-!
# Cell-aware invocations: the faults of a write to an element

The heads of a write to one element of a local array that fail before the write, preserved: a root not yet
initialized, the index's fault, `0x32` from the array's length on, and a plain write's right side faulting.
Each composes the root's Core cell, the children's meanings in the write's prefixed environments, S7's length
of the array's cell, and the code's runs (`CompatibleElementWrites`). Main declarations:
`CellAwareElementWriteHeads.preserves_uninitialized`, `preserves_index_fault`, `preserves_outOfBounds` and
`preserves_plain_rhs_fault`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning CompatibleRenamedPlace DataPatternValues DataPlaceExecution
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

section Heads
variable {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : Head (.initial compiled.compatible.checked) invocation.source context certificate scope assignment operator rhs)
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (ownerFrame : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)



local notation "acceptedCells" => GeneralizedLocalDescriptorHeap.cellModel
  (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
local notation "acceptedInstances" => GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment

include environments heaps agrees admitted in
/-- A root not yet initialized: the code fails with the site's reason at the root's check, before the index, and
nothing changes. -/
theorem preserves_uninitialized {location : Dynamic.Location} {cell : Dynamic.Cell}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell) (initialValue : Dynamic.RootInitialValue cell none)
    (uninitialized : ∀ location, faults (.semantic (.uninitializedLocation location)) head.invalidProjection)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults (.semantic (.uninitializedLocation location)) token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld before finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before before ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld before
        finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, before, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, reference, coreRead⟩ :=
    CellAwareElementWriteRoots.uninitialized environments heaps agrees head.slotEq lookup read initialValue
  refine ⟨head.invalidProjection, store, mapping, world, ?_, uninitialized location, heaps, .refl _, .refl _,
    .refl mapping store, .refl _, .refl mapping world before store, initial, callerProtocol.refl _, admitted.rows⟩
  simp only [Head.emit]
  rw [CompatibleElementWrites.code_rename]
  exact CompatibleElementWrites.root_empty reference coreRead

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- The index's fault, at a root that holds its array: the root's check passes, and the index's Core run fails as
its Source run does, before the bound. -/
theorem preserves_index_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    {indexSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.fault failure) after)
    (bound : indexSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults failure token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, native, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post⟩ :=
    meaning indexSize bound head.keyChild head.keyFound keyTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [native])
      (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType represented) actualTyped)
      initial admitted authority physical owner ownerFrame indexed
  cases resultRep with
  | fault matched =>
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post.rows⟩
    simp only [Head.emit]
    rw [CompatibleElementWrites.code_rename]
    exact CompatibleElementWrites.index_failure reference coreRead
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil, List.cons_append,
        List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- `0x32` from the array's length on: the root's check and the index pass, and the bound's check fails on both
sides, before the right side. -/
theorem preserves_outOfBounds [RecursiveStageMeaning.FaultTokens faults] (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    (kind : ArrayIndexType head.keyNode.type)
    {indexSize : Nat} {position : Word} {after : Dynamic.Heap} {arrayCell : Dynamic.Cell}
    {elements : List Dynamic.Value}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.value (.word position)) after)
    (bound : indexSize < budget)
    (arrayRead : Dynamic.Heap.Reads after arrayLocation arrayCell)
    (stored : arrayCell.value = some (.arrayObject element elements))
    (beyond : elements.length ≤ position.val) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults (.semantic (.panic 0x32)) token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, native, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨arrayTarget, payloadType, identity, rfl, sameType, _, _, _⟩ :=
    CompatiblePayload.arrayRef_fields represented rfl
  obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, post⟩ :=
    meaning indexSize bound head.keyChild head.keyFound keyTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [_])
      (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType represented) actualTyped)
      initial admitted authority physical owner ownerFrame indexed
  cases resultRep with
  | value indexPayload =>
    obtain ⟨word, same, rfl, _⟩ := CompatiblePayload.index_word_fields kind indexPayload
    cases same
    have arrayPayload := (payloadModel compiled.compatible.checked registry functions).extend represented maps worlds
    obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve finalHeaps (.array arrayRead stored) arrayPayload
      (by rw [sameType]; rfl)
    cases measured with
    | array coreArrayRead =>
      have outside : ¬ position < Word.ofNatModulo elements.length := by
        rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
        omega
      refine ⟨_, finalStore, finalMap, finalWorld, ?_, RecursiveStageMeaning.FaultTokens.panic _, finalHeaps, maps,
        worlds, frame, metadata, effect, reached, related, post.rows⟩
      simp only [Head.emit]
      rw [CompatibleElementWrites.code_rename]
      exact CompatibleElementWrites.outOfBounds reference coreRead
        (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
          List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
        coreArrayRead outside

theorem valueAt_lt {values : List Dynamic.Value} {position : Nat} {selected : Dynamic.Value}
    (selection : Dynamic.ValueAt values position selected) : position < values.length := by
  induction selection with
  | head => simp
  | tail _ ih => simp only [List.length_cons]; omega

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame in
/-- A plain write's right side faulting: the root's check, the index and the bound pass, and the right side's
Core run fails as its Source run does, before the write. -/
theorem preserves_plain_rhs_fault (budget : Nat)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    (plain : operator = .equal)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty} {arrayLocation : Dynamic.Location}
    (lookup : Dynamic.Environment.LooksUp environment assignment.target.root location)
    (read : Dynamic.Heap.Reads before location cell)
    (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
    (keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type)
    (kind : ArrayIndexType head.keyNode.type)
    {indexSize : Nat} {position : Word} {middle : Dynamic.Heap} {arrayCell : Dynamic.Cell}
    {elements : List Dynamic.Value} {selected : Dynamic.Value}
    (indexed : Staging.Recursive.Size.Expression program stages indexSize invocation context environment before
      head.key (.value (.word position)) middle)
    (indexBound : indexSize < budget)
    (arrayRead : Dynamic.Heap.Reads middle arrayLocation arrayCell)
    (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
    (selection : Dynamic.ValueAt elements position.val selected)
    (rhsTyped : ExpressionHasType invocation.source context rhs head.node.type)
    {rhsSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (rhsTrace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment middle rhs
      (.fault failure) after)
    (rhsBound : rhsSize < budget) (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults failure token ∧
      GenericHeap.CellHeapRepresents acceptedCells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect acceptedInstances mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  obtain ⟨target, native, reference, coreRead, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨arrayTarget, payloadType, identity, rfl, sameType, _, _, _⟩ :=
    CompatiblePayload.arrayRef_fields represented rfl
  obtain ⟨_, indexStore, indexMap, indexWorld, indexEval, indexRep, indexHeaps, indexMaps, indexWorlds, indexFrame,
      indexMetadata, indexEffect, indexState, indexRelated, indexPost⟩ :=
    meaning indexSize indexBound head.keyChild head.keyFound keyTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [_])
      (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType represented) actualTyped)
      initial admitted authority physical owner ownerFrame indexed
  cases indexRep with
  | value indexPayload =>
    obtain ⟨word, same, rfl, _⟩ := CompatiblePayload.index_word_fields kind indexPayload
    cases same
    have arrayPayload := (payloadModel compiled.compatible.checked registry functions).extend represented indexMaps
      indexWorlds
    have stored : arrayCell.value = some (.arrayObject element elements) := by cases arrayValue; rfl
    obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve indexHeaps (.array arrayRead stored) arrayPayload
      (by rw [sameType]; rfl)
    cases measured with
    | array coreArrayRead =>
      have within : position < Word.ofNatModulo elements.length := by
        rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
        exact valueAt_lt selection
      obtain ⟨_, finalStore, finalMap, finalWorld, rhsEval, rhsRep, finalHeaps, maps, worlds, frame, metadata,
          effect, reached, related, post⟩ :=
        meaning rhsSize rhsBound head.right head.found rhsTyped (environments.extend indexMaps indexWorlds)
          indexHeaps (locals.mono indexMetadata)
          (DataPlaceChildExpressions.prefix_agrees agrees [.word position, _])
          (.cons .word (.cons ((payloadModel compiled.compatible.checked registry functions).runtime_hasType
            arrayPayload) (actualTyped.weaken indexWorlds)))
          indexState indexPost.at_value.2 (authority.transport indexEffect)
          (physical.transport indexEffect indexFrame) owner ownerFrame rhsTrace
      cases rhsRep with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, indexMaps.trans maps,
          indexWorlds.trans worlds, indexFrame.trans frame, indexMetadata.trans metadata, indexEffect.trans effect,
          reached, callerProtocol.trans indexRelated related, post.rows⟩
        simp only [Head.emit, Head.modifier, CompatibleElementWrites.modifierOf, plain]
        rw [CompatibleElementWrites.code_rename]
        exact CompatibleElementWrites.plain_rhs_failure reference coreRead
          (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
            List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using indexEval)
          coreArrayRead within
          (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
            List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using rhsEval)

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
