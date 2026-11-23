import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationElementWrites
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrayMemrefs

/-!
# Cell-aware invocations: the heads of a write to an element

The heads of a write to one element of a local array, preserved: a root not yet initialized, the index's
fault, `0x32` from the array's length on, a plain write's right side faulting, and a plain write, whose Core
run reaches its continuation with the array's cell taking the value at the index as the Source's write does.
Each composes the root's Core cell, the children's meanings in the write's prefixed environments, S7's length
of the array's cell, and the code's runs (`CompatibleElementWrites`). Main declarations:
`CellAwareElementWriteHeads.preserves_uninitialized`, `preserves_index_fault`, `preserves_outOfBounds`,
`preserves_plain_rhs_fault` and `preserves_plain`.
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

namespace Head
variable {values : SourceCoreCompatibleValues.Context} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- The Core types of a plain write's five binders, innermost first: the cell write's unit, the updated
entries, the stored value, the index's word and the array's cell. -/
def plainSlotTypes (head : Head values source context certificate scope assignment operator rhs) : Core.Context :=
  [.unit, head.layout.type, head.elementType, .word, head.rootType]

end Head

/-- In a well-typed heap, the cell that a reference to an array of `T`s names holds an object of `T`s, and the
reference's element is `T`. -/
theorem object_element {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {element expected other : TypeSystem.Ty} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {elements : List Dynamic.Value}
    (reference : Dynamic.ValueHasType context heap (.arrayRef element location) (TypeSystem.Ty.array expected))
    (heapTyped : Dynamic.HeapWellTyped context heap) (read : Dynamic.Heap.Reads heap location cell)
    (current : cell.value = some (.arrayObject other elements)) :
    other = expected ∧ element = expected := by
  rcases reference.arrayRef_inv with ⟨typeEq, _, typedRead, cellType⟩ | ⟨_, impossible, _⟩
  · have expectedEq : expected = element := by simpa [TypeSystem.Ty.array] using typeEq
    subst expectedEq
    have cellEq := read.functional typedRead
    subst cellEq
    have cellValue := (heapTyped _ read.member).value
    rw [current, cellType] at cellValue
    cases cellValue with
    | some objectTyped =>
      rcases objectTyped.arrayObject_inv with ⟨objectEq, _⟩ | ⟨_, impossible, _⟩
      · exact ⟨by simpa [TypeSystem.Ty.arrayObject] using objectEq.symm, rfl⟩
      · simp [TypeSystem.Ty.arrayObject] at impossible
  · simp [TypeSystem.Ty.array] at impossible

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

include environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame unique
  assignmentTyped in
/-- A plain write to one element of a local array, `a[i] = v`, from its staged Source run: the root's array,
the index's and the right side's meanings, the bound's check and the array's cell taking the right side's
value at the index on both sides. The compiled code runs to its continuation under the five binders. -/
theorem preserves_plain (budget : Nat) (plain : operator = .equal)
    (meaning : PreservesBelow (attachment := attachment) bridge context
      (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults
      budget)
    {targetSize rhsSize : Nat} {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    {targetHeap middle after : Dynamic.Heap}
    (targetTrace : Staging.Recursive.Size.ElementTarget program stages targetSize invocation context environment
      before assignment.target (.resolved target) targetHeap)
    (targetBound : targetSize < budget)
    (trace : Staging.Recursive.Size.Expression program stages rhsSize invocation context environment targetHeap rhs
      (.value right) middle)
    (rhsBound : rhsSize < budget)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement =>
        Dynamic.CompoundAssignmentApplies assignment.target.type operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel
        (payloadModel compiled.compatible.checked registry functions)
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after
        finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 5 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.plainSlotTypes ++ actualContext)
        compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output {result : Value} {final : Store},
        Evaluates (slots ++ actual) finalStore (shift 5 (next.rename ξ)) result final →
        Evaluates actual store ((head.emit next output).rename ξ) result final := by
  subst plain
  -- The Source types: the target's and the right side's are one, and the index is typed at its node's.
  have rhsTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetTyped, sameType⟩ : SourcePlaceHasType invocation.source context assignment.target head.node.type ∧
      assignment.target.type = head.node.type := by
    cases assignmentTyped with
    | equal targetTyped rhsTyped' _ =>
      have same := CellAwareArraySourceInversion.typed_type unique head.found rhsTyped'
      subst same
      exact ⟨targetTyped, targetTyped.type_eq⟩
    | wordCompound kind _ _ _ => cases kind
    | fixedCompound kind _ _ _ => cases kind
    | shiftCompound kind _ _ _ _ _ => cases kind
  obtain ⟨_, _, indexTyped⟩ := Staging.Recursive.SelectedPreservation.element_place_typed (leading := [])
    (index := head.key) targetTyped head.single
  have keyTyped : ExpressionHasType invocation.source context head.key head.keyNode.type :=
    CellAwareArraySourceInversion.typed_type unique head.keyFound indexTyped ▸ indexTyped
  cases ElementAssignmentSourceInversion.single_resolved head.single targetTrace with
  | @intro indexSize _ cell element arrayLocation position _ _ elements _ lookup read initialValue indexed arrayRead
      arrayValue selection =>
  -- The root's Source cell holds a reference to an array of the target's type.
  have cellType : cell.type = TypeSystem.Ty.array assignment.target.type := by
    obtain ⟨_, staticLookup, _, _, bodyEq⟩ := head.writable.scheme
    obtain ⟨_, _, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    cases lookup.functional staticLookupRuntime
    cases read.functional staticRead
    exact staticCellType.trans bodyEq
  have rootValue : cell.value = some (.arrayRef element arrayLocation) := by cases initialValue; rfl
  have referenceBefore : Dynamic.ValueHasType context before (.arrayRef element arrayLocation)
      (TypeSystem.Ty.array assignment.target.type) := by
    have cellTyped := (admitted.heap _ read.member).value
    rw [rootValue, cellType] at cellTyped
    cases cellTyped with
    | some typed => exact typed
  -- The root's Core cell holds the array's cell reference.
  obtain ⟨_, _, reference, full, represented⟩ :=
    CellAwareElementWriteRoots.initialized environments heaps agrees head.slotEq lookup read initialValue
  obtain ⟨arrayTarget, payload, identity, rfl, typeEq, mapped, typed, _⟩ := arrayRef_fields represented rfl
  simp only [Core.Ty.cell.injEq, Core.Ty.product.injEq, Core.Ty.namedData.injEq, true_and] at typeEq
  obtain ⟨rfl, rfl⟩ := typeEq
  -- The index's meaning, under the array's binder.
  obtain ⟨_, _, _, _, keyEval, keyRepresented, keyHeaps, keyMaps, keyWorlds, keyFrame, keyMetadata, keyEffect,
      keyReached, keyRelated, keyPost⟩ :=
    meaning indexSize (Nat.lt_trans (Staging.Recursive.Size.child_lt_stepSize (by simp)) targetBound)
      head.keyChild head.keyFound keyTyped environments heaps locals (agree_prefix agrees _)
      (.cons (.cellRef typed) actualTyped) initial admitted authority physical owner ownerFrame indexed
  rw [rename_prefix] at keyEval
  cases keyRepresented with
  | @value _ _ indexPayload =>
  rw [head.keyType] at indexPayload
  obtain ⟨_, sameWord, rfl⟩ := CompatibleExpressionPrimitives.word_fields indexPayload
  cases sameWord
  -- The bound's check: the index is below the array's length on both sides.
  obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps
    (.array arrayRead arrayValue.arrayObject_value) (represented.extend (.refl _) keyMaps keyWorlds) rfl
  cases measured with
  | array lengthRead =>
  have within : position < Word.ofNatModulo elements.length := by
    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
    exact selection.lt_length
  -- The right side's meaning, under the index's and the array's binders.
  obtain ⟨_, rhsStore, rhsMap, _, rhsEval, rhsRepresented, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata,
      rhsEffect, rhsReached, rhsRelated, rhsPost⟩ :=
    meaning rhsSize rhsBound head.right head.found rhsTyped (environments.extend keyMaps keyWorlds) keyHeaps
      (locals.mono keyMetadata)
      (agree_prefix (agree_prefix agrees
        (.cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget))
        (.word position))
      (.cons .word (.cons (.cellRef (keyWorlds.lookup typed)) (actualTyped.weaken keyWorlds))) keyReached
      keyPost.at_value.2 (authority.transport keyEffect) (physical.transport keyEffect keyFrame) owner ownerFrame
      trace
  rw [rename_prefix, rename_prefix] at rhsEval
  cases rhsRepresented with
  | @value _ coreStored storedPayload =>
  rw [head.rightType] at storedPayload
  -- The Source write: the array's cell takes the right side's value at the index.
  cases write with
  | intro currentRead _ currentInitial update heapWrite =>
  cases update with
  | element _ child replace =>
  cases child with
  | leaf modified =>
  cases modified with
  | primitive _ applies =>
  cases applies
  have objectValue := currentInitial.arrayObject_value
  have referenceMiddle := referenceBefore.mono (keyMetadata.trans rhsMetadata)
  obtain ⟨sameOther, sameElement⟩ :=
    object_element referenceMiddle rhsPost.at_value.2.heap currentRead objectValue
  subst sameOther
  subst sameElement
  have sameRuntime : SourceCoreRawMetadata.runtimeType assignment.target.type =
      SourceCoreRawMetadata.runtimeType head.node.type := by rw [sameType]
  -- The Core write: the array's cell takes the right side's value's entry at the index.
  obtain ⟨length, default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps, futureWorlds,
      storeFrame, storeEffect⟩ :=
    CellAwareArrayReads.store_preserve_at head.prepared rhsHeaps
      (stack := coreStored :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      (context := head.elementType :: .word :: head.rootType :: actualContext)
      (.cons storedPayload.runtime_hasType (.cons .word
        (.cons (.cellRef (rhsWorlds.lookup (keyWorlds.lookup typed)))
          (actualTyped.weaken (keyWorlds.trans rhsWorlds)))))
      currentRead objectValue replace heapWrite (rhsMaps.lookup (keyMaps.lookup mapped))
      (rhsWorlds.lookup (keyWorlds.lookup typed)) storedPayload sameRuntime
      (arrayExpr := .var 2) (keyExpr := .var 1) (fun read => .loadCell (.var rfl) read) (.var rfl)
      (fun _ => .var rfl) (.var rfl) rfl rfl
  -- The array's Core cell after the write, at its world's type: the updated entries are of the layout's type.
  have finalBound : arrayTarget < (rhsStore ++ suffix).length := by
    rw [List.length_append]
    exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp storeRead).1 (Nat.le_add_right _ _)
  obtain ⟨_, cellRead, cellTyped⟩ := finalHeaps.runtime_hasTypes.lookup
    (futureWorlds.lookup (rhsWorlds.lookup (keyWorlds.lookup typed)))
  have newRead := List.getElem?_set_self (a := Core.Value.pair (.word length) (.pair default
    (OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
      coreStored entries)))) finalBound
  have cellEq := Option.some.inj (cellRead.symm.trans newRead)
  subst cellEq
  cases cellTyped with
  | pair _ inner =>
  cases inner with
  | pair _ encodeTyped =>
  have appended' : CompatibleMappingComparison.insertStore head.comparison head.layout
      (coreStored :: .word position ::
        .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget :: actual)
      rhsStore entries (.word position) coreStored = rhsStore ++ suffix := appended
  have modifierNone : head.modifier = none := by
    simp [Head.modifier, CompatibleElementWrites.modifierOf]
  -- The caller's pool after the write.
  let suffixPool : State headers keys ⟨scope, rhsMap, futureWorld, after, _, canonical⟩ :=
    (bridge.pool rhsReached).extend (.refl _) futureWorlds storeFrame (.of_write heapWrite)
  obtain ⟨returned, _, returnedRelated⟩ := bridge.restore rhsReached suffixPool (.refl _) futureWorlds storeFrame
    (.of_write heapWrite) (Relates.of_records_eq rfl)
  refine ⟨_, rhsMap, futureWorld,
    [.unit, OrderedMapping.encode head.layout (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual
        (.word position) coreStored entries), coreStored, .word position,
      .cellRef (.product .word (.product head.elementType (.namedData head.identity))) arrayTarget],
    finalHeaps, keyMaps.trans rhsMaps, (keyWorlds.trans rhsWorlds).trans futureWorlds,
    (keyFrame.trans rhsFrame).trans storeFrame, (keyMetadata.trans rhsMetadata).trans (.of_write heapWrite),
    (keyEffect.trans rhsEffect).trans storeEffect, rfl,
    .cons .unit (.cons encodeTyped (.cons (storedPayload.runtime_hasType.weaken futureWorlds) (.cons .word
      (.cons (.cellRef (futureWorlds.lookup (rhsWorlds.lookup (keyWorlds.lookup typed))))
        (actualTyped.weaken ((keyWorlds.trans rhsWorlds).trans futureWorlds)))))),
    ⟨returned, callerProtocol.trans (callerProtocol.trans keyRelated rhsRelated) returnedRelated,
      referenceMiddle.arrayElementWrite rhsPost.at_value.2.heap currentRead objectValue replace
        (sameType ▸ rhsPost.at_value.1) heapWrite,
      StableRows.after_administrative (bridge.pool initial) (bridge.pool returned) admitted.rows
        ((keyFrame.trans rhsFrame).trans storeFrame)⟩, ?_⟩
  -- The compiled code runs to its continuation.
  intro next output result final nextEval
  rw [Head.emit, CompatibleElementWrites.code_rename, modifierNone]
  exact CompatibleElementWrites.plain_evaluates head.prepared rfl reference full keyEval lengthRead within rhsEval
    storeRead wordKeys (by rw [appended']; exact nextEval)

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareElementWriteHeads
