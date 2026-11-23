import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrayCells

/-!
# Cell-aware invocations: memory arrays' references

The heads of `CanStore.load(lidx(a, i))` and `CanStore.store(lidx(a, i), v)`, the memref made on the spot:
the array's and the index's meanings, then `0x32` from the array's length on, else the element at the index,
read as `a[i]` reads it, or the value's meaning and the array's cell taking it at the index. A memref has no
value relation of its own, so the heads take the array and the index as their children. Main declarations:
`CellAwareInvocationArrayBounds.load_preserves`, `store_preserves` and their `reflects`.
-/

section
/-! `CanStore.store`'s step on the array's cell: Core inserts the value's entry after the insert's Core-only
cells and writes the cell, as the Source replaces the element in its cell. The cell holds no generalized
local, so the write keeps every located one. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

/-- A write to a Source cell that holds no generalized local, at its mapped Core location, keeps every
located generalized local's values: the map is injective, so the located cells are elsewhere on both sides. -/
theorem write_effect {definitions : DataEnvironment}
    {instances : GeneralizedLocalDescriptorHeap.InstanceModel definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap after : Dynamic.Heap} {store finalStore : Store}
    (injective : LocationMap.Injective mapping)
    {location : Dynamic.Location} {cell : Dynamic.Cell} {target : Core.Location}
    (read : Dynamic.Heap.Reads heap location cell) (ordinary : cell.generalized = none)
    (mapped : mapping[location.index]? = some target)
    {sourceValue : Option Dynamic.Value} {nativeValue : Core.Value}
    (written : Dynamic.Heap.Writes heap location sourceValue after)
    (nativeWritten : store.write? target nativeValue = some finalStore) :
    CellAwareScopeAuthority.Effect instances mapping world heap store mapping world after finalStore := by
  have metadata : Dynamic.HeapMetadataExtend heap after := .of_write written
  refine ⟨metadata, .refl _, .refl _, ?_⟩
  intro function binding lexical descriptorLocation located
  have different : descriptorLocation ≠ location := by
    intro same
    subst location
    have cells := located.sourceRead.functional read
    have descriptors := congrArg Dynamic.Cell.generalized cells
    rw [located.descriptor, ordinary] at descriptors
    cases descriptors
  have nativeDifferent : located.target ≠ target := by
    intro same
    have indices := injective (same ▸ located.reference.mapped) mapped
    apply different
    cases descriptorLocation
    cases location
    exact congrArg Dynamic.Location.mk indices
  obtain ⟨cell', sourceRead', _, descriptor'⟩ := metadata descriptorLocation located.cell located.sourceRead
  exact ⟨⟨located.attachment, cell', sourceRead', descriptor'.trans located.descriptor, located.target,
    located.reference, located.values, located.rows,
    (Core.Store.write?_preserves_other nativeWritten nativeDifferent).trans located.nativeRead⟩, rfl⟩

private theorem closed_typed {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) :
    HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

section Stores
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
  (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)
variable {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

include prepared in
/-- `CanStore.store`'s step on its representation, after the memref's and the value's runs: the array's Core
cell takes the value's entry at the position, after the insert's Core-only cells, as the Source replaces the
element in its cell; the cells stay related, and the write keeps every located generalized local. -/
theorem store_preserve (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {outer : Environment} {context : Core.Context}
    (outerTyped : RuntimeEnvironmentHasTypes world outer context ambient.definitions)
    {element valueType : TypeSystem.Ty} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {elements updated : List Dynamic.Value} {position : Word} {stored : Dynamic.Value} {after : Dynamic.Heap}
    (read : Dynamic.Heap.Reads heap location cell) (current : cell.value = some (.arrayObject element elements))
    (replace : Dynamic.ValuesReplaceAt elements position.val stored updated)
    (written : Dynamic.Heap.Writes heap location (some (.arrayObject element updated)) after)
    {target : Location} {payload : Ty} {identity : DataTypeId}
    (mapped : mapping[location.index]? = some target)
    (typed : world[target]? = some (.product .word (.product payload (.namedData identity))))
    {coreStored : Value}
    (storedRep : ValueRep checked registry functions mapping world valueType stored coreStored payload)
    (sameRuntime : SourceCoreRawMetadata.runtimeType element = SourceCoreRawMetadata.runtimeType valueType) :
    ∃ length default entries suffix futureWorld,
      store.read? target = some (.pair (.word length) (.pair default
        (OrderedMapping.encode ⟨.word, payload, identity⟩ entries))) ∧
      (∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) ∧
      CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩
        (coreStored :: .pair (.cellRef (.product .word (.product payload (.namedData identity))) target)
          (.word position) :: outer) store entries (.word position) coreStored = store ++ suffix ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld after
        ((store ++ suffix).set target (.pair (.word length) (.pair default (OrderedMapping.encode
          ⟨.word, payload, identity⟩ (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
            coreStored entries))))) ∧
      WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store mapping
        ((store ++ suffix).set target (.pair (.word length) (.pair default (OrderedMapping.encode
          ⟨.word, payload, identity⟩ (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
            coreStored entries))))) ∧
      CellAwareScopeAuthority.Effect instances mapping world heap store mapping futureWorld after
        ((store ++ suffix).set target (.pair (.word length) (.pair default (OrderedMapping.encode
          ⟨.word, payload, identity⟩ (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
            coreStored entries))))) := by
  obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
  have sameCell := Dynamic.Heap.Reads.functional read sourceRead
  subst sameCell
  cases stands with
  | optional optionalTyped _ =>
    have impossible := optionalTyped.symm.trans typed
    simp [Core.OptionalCell.cellType] at impossible
  | array cellTyped arrayed =>
    obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, typeEq, contents⟩ := arrayed
    subst cellEq
    simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at current
    obtain ⟨sameElement, sameElements⟩ := current
    subst element' elements'
    subst valueEq
    rw [typeEq] at cellTyped
    have sameType := Option.some.inj (cellTyped.symm.trans typed)
    simp only [Ty.product.injEq, Ty.namedData.injEq, true_and] at sameType
    obtain ⟨samePayload, sameIdentity⟩ := sameType
    subst payload' identity'
    have wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word := by
      intro key value member
      obtain ⟨_, _, same⟩ := contents.keys key value member
      exact ⟨_, same⟩
    let stack : Environment :=
      coreStored :: .pair (.cellRef (.product .word (.product payload (.namedData identity))) target) (.word position) ::
        outer
    have inserted : Evaluates stack store
        (OrderedMapping.insert ⟨.word, payload, identity⟩ comparison.expression
          (.second (.second (.loadCell (.first (.var 1))))) (.second (.var 1)) (.var 0))
        (.inRight .word (OrderedMapping.encode ⟨.word, payload, identity⟩
          (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position) coreStored entries)))
        (CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩ stack store entries
          (.word position) coreStored) :=
      OrderedMapping.insert_evaluates (environment := stack)
        (mapping := .second (.second (.loadCell (.first (.var 1))))) (keyExpr := .second (.var 1))
        (valueExpr := .var 0) (keyEqual := comparison.expression) entries (.word position) coreStored
        (CompatibleMappingComparison.comparator comparison stack store) GenericHeap.arrayKeyEqual
        (.second (.second (.loadCell (.first (.var rfl)) coreRead))) (.second (.var rfl)) (.var rfl)
        (CompatibleEquality.prepared_evaluates_exact comparison stack store)
        (word_comparisons prepared rfl stack store wordKeys position _)
    have comparisonTyped : HasType (payload ::
          .product (.cell (.product .word (.product payload (.namedData identity)))) .word :: context)
        comparison.expression (OrderedMapping.Layout.comparisonType ⟨.word, payload, identity⟩)
        ambient.definitions := by
      have closed := closed_typed (comparison.typed.extend_definitions ambient.basePrefix)
        (payload :: .product (.cell (.product .word (.product payload (.namedData identity)))) .word :: context)
      rw [(word_comparison prepared).1] at closed
      simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
        SourceCoreDataEquality.comparatorType] using closed
    have insertTyped : HasType (payload ::
          .product (.cell (.product .word (.product payload (.namedData identity)))) .word :: context)
        (OrderedMapping.insert ⟨.word, payload, identity⟩ comparison.expression
          (.second (.second (.loadCell (.first (.var 1))))) (.second (.var 1)) (.var 0))
        (LanguageResult.resultType (OrderedMapping.Layout.type ⟨.word, payload, identity⟩)) ambient.definitions :=
      OrderedMapping.insert_hasType contents.registered comparisonTyped
        (.second (.second (.loadCell (.first (.var rfl))))) (.second (.var rfl)) (.var rfl)
    have stackTyped : RuntimeEnvironmentHasTypes world stack
        (payload :: .product (.cell (.product .word (.product payload (.namedData identity)))) .word :: context)
        ambient.definitions :=
      .cons storedRep.runtime_hasType (.cons (.pair (.cellRef typed) .word) outerTyped)
    obtain ⟨suffix, appended, _⟩ := CompatibleMappingComparison.helper_store_extension comparison stack store
      (OrderedMapping.Layout.insertParameter ⟨.word, payload, identity⟩)
      (OrderedMapping.Layout.type ⟨.word, payload, identity⟩) (OrderedMapping.insertBody ⟨.word, payload, identity⟩)
      (.pair (OrderedMapping.encode ⟨.word, payload, identity⟩ entries)
        (.pair (.pair (.word position) coreStored) (CompatibleMappingComparison.comparator comparison stack store)))
    have appended' : CompatibleMappingComparison.insertStore comparison ⟨.word, payload, identity⟩ stack store entries
        (.word position) coreStored = store ++ suffix := appended
    obtain ⟨futureWorld, worlds, futureHeaps, _, unchanged⟩ :=
      CellMappingHeap.evaluation_preserves_frame heaps stackTyped insertTyped inserted appended'
    rw [appended'] at futureHeaps unchanged
    have kept := written
    cases kept with
    | @intro previous updatedCells previousRead cellsWritten =>
      have samePrevious := Dynamic.Heap.Reads.functional sourceRead previousRead
      subst samePrevious
      have contents' := (contents.extend (.refl _) worlds).write replace
        (ValueRep.compatible sameRuntime (storedRep.extend (.refl _) (.refl _) worlds))
      rw [ofNatModulo_self] at contents'
      have newCell : GenericHeap.ArrayCellRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
          mapping futureWorld ⟨.arrayObject element, some (.arrayObject element updated), none⟩
          (.pair (.word (Word.ofNatModulo elements.length)) (.pair default (OrderedMapping.encode
            ⟨.word, payload, identity⟩ (OrderedMapping.insertEntries GenericHeap.arrayKeyEqual (.word position)
              coreStored entries))))
          (.product .word (.product payload (.namedData identity))) :=
        ⟨element, updated, payload, identity, default, _, rfl, by rw [replace.length_eq], rfl, contents'⟩
      obtain ⟨final, nativeWritten, finalHeaps⟩ :=
        futureHeaps.replace_array mapped (worlds.lookup typed) cellsWritten newCell
      have finalEq : final = (store ++ suffix).set target (.pair (.word (Word.ofNatModulo elements.length))
          (.pair default (OrderedMapping.encode ⟨.word, payload, identity⟩ (OrderedMapping.insertEntries
            GenericHeap.arrayKeyEqual (.word position) coreStored entries)))) := by
        simp only [Store.write?] at nativeWritten
        split at nativeWritten
        · exact (Option.some.inj nativeWritten).symm
        · cases nativeWritten
      subst finalEq
      exact ⟨Word.ofNatModulo elements.length, default, entries, suffix, futureWorld, coreRead, wordKeys, appended',
        finalHeaps, worlds, unchanged.trans (AdministrativePreserved.write (List.mem_of_getElem? mapped) nativeWritten),
        (CellAwareScopeAuthority.Effect.append (instances := instances) store suffix (.refl _) (.refl _) worlds).trans
          (write_effect futureHeaps.injective sourceRead rfl mapped written nativeWritten)⟩

end Stores

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
end

section
/-! `CanStore.load(lidx(a, i))`: the memref's bounds check against the array's length, then the read. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds CellAwareArraySourceInversion CompatibleArrayEvaluation
open CellAwareArrayCells
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

/-- `CanStore.load(r)` has the element type of its memref. -/
theorem load_source_types {source : TypedSource} {context : SourceSemantics.Context} {id reference : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .memrefLoad reference) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionHasType source context reference (TypeSystem.Ty.memref node.type) := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    cases raw with
    | memrefLoad referenceTyped => exact typeEq ▸ referenceTyped

/-- `lidx(a, i)` of a memref of `T` takes an array of `T`s and an index of `word` or one of the twelve
types. -/
theorem reference_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id base subscript : ExpressionId} {node : ExpressionNode} {element : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .elementRef base subscript) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id (TypeSystem.Ty.memref element)) :
    ExpressionHasType source context base (TypeSystem.Ty.array element) ∧
      ∃ subscriptType, ExpressionHasType source context subscript subscriptType ∧ ArrayIndexType subscriptType := by
  generalize typeEq : TypeSystem.Ty.memref element = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | elementRef baseTyped subscriptTyped kind =>
      have sameType := typeEq.trans resultEq
      simp only [TypeSystem.Ty.memref, TypeSystem.Ty.application.injEq, true_and] at sameType
      subst sameType
      exact ⟨baseTyped, _, subscriptTyped, kind⟩

/-- `lidx(a, i)` is of a memref of `T`, and takes an array of `T`s and an index of `word` or one of the twelve
types. -/
theorem elementRef_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id base subscript : ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .elementRef base subscript) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ element, node.type = TypeSystem.Ty.memref element ∧
      ExpressionHasType source context base (TypeSystem.Ty.array element) ∧
      ∃ subscriptType, ExpressionHasType source context subscript subscriptType ∧ ArrayIndexType subscriptType := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | elementRef baseTyped subscriptTyped kind => exact ⟨_, rfl, baseTyped, _, subscriptTyped, kind⟩

/-- A memref type's runtime view follows its array type's. -/
theorem memref_runtime {type element other : TypeSystem.Ty} (typeEq : type = TypeSystem.Ty.memref element)
    (arrays : SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array other)) :
    SourceCoreRawMetadata.runtimeType type = SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.memref other) := by
  subst typeEq
  simp only [TypeSystem.Ty.memref, TypeSystem.Ty.array, SourceCoreRawMetadata.runtimeType,
    TypeSystem.Ty.application.injEq, true_and] at arrays ⊢
  exact arrays

/-- `CanStore.store(r, v)` is of `()`, and takes a value of its memref's element type. -/
theorem store_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id reference value : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node) (form : node.form = .memrefStore reference value)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    node.type = TypeSystem.Ty.unit ∧ ∃ element,
      ExpressionHasType source context reference (TypeSystem.Ty.memref element) ∧
      ExpressionHasType source context value element := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | memrefStore referenceTyped valueTyped => exact ⟨rfl, _, referenceTyped, valueTyped⟩

/-- A position below a list's length has a replacement. -/
theorem replace_exists : ∀ {elements : List Dynamic.Value} {position : Nat} (stored : Dynamic.Value),
    position < elements.length → ∃ updated, Dynamic.ValuesReplaceAt elements position stored updated
  | [], _, _, bound => by simp at bound
  | _ :: _, 0, _, _ => ⟨_, .head⟩
  | _ :: rest, position + 1, stored, bound => by
    obtain ⟨updated, replaced⟩ := replace_exists (elements := rest) (position := position) stored
      (by simpa using bound)
    exact ⟨_, .tail replaced⟩

theorem memrefStore_split (layout : OrderedMapping.Layout) (comparison reference value : Expr) :
    ∃ tail, SourceCoreDataExpressions.memrefStore layout comparison reference value =
      LanguageResult.bind .unit reference (LanguageResult.bind .unit (value.weakenAt 0) tail) := ⟨_, rfl⟩

theorem memrefLoad_split (layout : OrderedMapping.Layout) (comparison reference : Expr) :
    ∃ tail, SourceCoreDataExpressions.memrefLoad layout comparison reference =
      LanguageResult.bind layout.valueType reference tail := ⟨_, rfl⟩

theorem elementRef_split (layout : OrderedMapping.Layout) (base subscript : Expr) :
    ∃ tail, SourceCoreDataExpressions.elementRef layout base subscript =
      LanguageResult.bind (.product (.cell (.product .word (.product layout.valueType layout.type))) .word) base
        (LanguageResult.bind (.product (.cell (.product .word (.product layout.valueType layout.type))) .word)
          (subscript.weakenAt 0) tail) := ⟨_, rfl⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
  (covers : invocation.evidence.Covers context)
  {scope : SourceCoreLocalCell.Scope} {id base : ExpressionId} {node baseNode : ExpressionNode}
  {first lowered : SourceCoreBasic.LoweredExpr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.load(lidx(a, i))`'s head: the array's and the index's meanings, then `0x32` from the array's
length on, else the element at the index, read as `a[i]` reads it. -/
theorem load_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript : ExpressionId} {referenceNode subscriptNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .memrefLoad reference)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType, SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)⟩)
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority
    physical owner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  have referenceTypedAt := load_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array node.type) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.memrefLoad layout comparison.expression
        (SourceCoreDataExpressions.elementRef layout first.expression second.expression)).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome
        value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [memrefLoad_rename, elementRef_rename, closed_rename comparison.typed]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨referenceSize, referenceSmaller, referenceTrace⟩ := single_fault failed
      cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
      | fault failed referenceChildren =>
        rcases pair_fault failed with ⟨firstSize, firstSmaller, firstTrace⟩ |
          ⟨firstSize, secondSize, baseSource, middle, firstSmaller, secondSmaller, firstTrace, secondTrace⟩
        · obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, memrefLoad_failure (elementRef_base_failure firstEval),
              .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
        · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
            firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | fault matched =>
              rw [rename_prefix] at secondEval
              exact ⟨_, finalStore, finalMap, finalWorld,
                memrefLoad_failure (elementRef_index_failure firstEval secondEval), .fault matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
      | result evaluated result referenceChildren =>
        obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
          firstTrace, secondTrace⟩ := pair_values evaluated
        obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | @value _ coreIndex indexPayload =>
            rw [rename_prefix] at secondEval
            rw [← subscriptTypeEq] at indexPayload
            obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
            have basePayload := payload.extend (.refl _) maps worlds
            cases result with
            | elementRefIndexType notWord _ => exact (notWord trivial).elim
            | elementRefOutOfBounds outside =>
              obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
              obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
              cases outside with
              | @array _ _ cell elements _ read stored beyond =>
                obtain ⟨measured, small⟩ :=
                  CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
                cases measured with
                | array coreRead =>
                  have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    omega
                  exact ⟨_, keyStore, keyMap, keyWorld,
                    memrefLoad_failure (elementRef_outOfBounds firstEval secondEval coreRead outsideCore),
                    .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                    firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨referenceSize, memref, referenceSmaller, rfl, referenceTrace⟩ := single_values evaluated
      cases result with
      | memrefLoad reads =>
        cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
        | result evaluated result referenceChildren =>
          obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
            firstTrace, secondTrace⟩ := pair_values evaluated
          obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
            firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
              owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | @value _ coreIndex indexPayload =>
              rw [rename_prefix] at secondEval
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              cases result with
              | @elementRef _ _ _ _ _ _ count counted within =>
                obtain ⟨target, payloadType, identity, rfl, typeEq, _, _, _⟩ := arrayRef_fields basePayload rfl
                obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
                cases measured with
                | array coreRead =>
                  have below : word < Word.ofNatModulo count := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := layout) firstEval secondEval coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  have readTyped := RuntimeEnvironmentHasTypes.cons pairTyped
                    (actualTyped.weaken (firstWorlds.trans worlds))
                  obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds,
                    suffixFrame, suffixAppend⟩ :=
                    CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime
                      (.array _) shaped word.isLt
                  rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
                  subst suffixAppend
                  let suffixPool : State headers keys
                      ⟨scope, keyMap, futureWorld, after, keyStore ++ suffix, canonical⟩ :=
                    (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
                  obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                    (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
                  exact ⟨_, _, keyMap, futureWorld,
                    memrefLoad_evaluates prepared keyType referenceEval coreReads,
                    .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
                    (firstWorlds.trans worlds).trans suffixWorlds,
                    (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
                    (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                      (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                      (.refl _) (.refl keyMap) suffixWorlds),
                    returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.load(lidx(a, i))`'s head, reflected: the array's and the index's Core runs give their Source
runs, and the load's Core run is the one the Source read, or its position from the array's length on, gives. -/
theorem load_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript : ExpressionId} {referenceNode subscriptNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .memrefLoad reference)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType, SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)⟩)
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted
    authority physical owner ownerFrame evaluated
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  have referenceTypedAt := load_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array node.type) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.memrefLoad reference) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have referenceOccurrence : Staging.Recursive.Occurrence invocation reference (.elementRef base subscript) :=
    ⟨_, lookupExpression?_sound referenceMetadata.found, referenceForm, referenceMetadata.requirements,
      referenceMetadata.coercions⟩
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type layout.valueType faults outcome
        value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.memrefLoad layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression)).rename ξ) value finalStore
      at evaluated
    rw [memrefLoad_rename, elementRef_rename, closed_rename comparison.typed] at evaluated
    have complete := evaluated.sound
    obtain ⟨tail, split⟩ := memrefLoad_split layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout (first.expression.rename ξ) (second.expression.rename ξ))
    rw [split] at evaluated
    obtain ⟨referenceSize, referenceResult, referenceStore, referenceSmaller, referenceEvaluation⟩ :
        ∃ referenceSize referenceResult referenceStore, referenceSize < size ∧
          EvaluationSize referenceSize actual store (SourceCoreDataExpressions.elementRef layout
            (first.expression.rename ξ) (second.expression.rename ξ)) referenceResult referenceStore := by
      cases evaluated with
      | caseLeft head _ => exact ⟨_, _, _, by omega, head⟩
      | caseRight head _ => exact ⟨_, _, _, by omega, head⟩
    obtain ⟨referenceTail, referenceSplit⟩ :=
      elementRef_split layout (first.expression.rename ξ) (second.expression.rename ξ)
    rw [referenceSplit] at referenceEvaluation
    cases referenceEvaluation with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (memrefLoad_failure (elementRef_base_failure firstEvaluation.sound))
        exact ⟨_, _, after, finalMap, finalWorld,
          .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl (.headFault firstTrace))),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps,
        firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        cases branch with
        | caseLeft secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (memrefLoad_failure (elementRef_index_failure firstEvaluation.sound secondEvaluation.sound))
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl
                (.tailFault firstTrace (.headFault secondTrace)))), .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps, worlds,
            frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value subscriptSource coreIndex indexPayload =>
            rw [← subscriptTypeEq] at indexPayload
            obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
            have basePayload := payload.extend (.refl _) maps worlds
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
            obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
            obtain ⟨count, counted⟩ :=
              CellAwareArrayReads.length_cases keyHeaps rfl basePayload baseRuntime baseSourceTyped
            cases counted with
            | @array _ _ cell elements read stored =>
              obtain ⟨measured, small⟩ :=
                CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
              cases measured with
              | array coreRead =>
                by_cases within : word.val < elements.length
                · obtain ⟨element, elementAt⟩ : ∃ element, elements[word.val]? = some element :=
                    ⟨_, List.getElem?_eq_getElem within⟩
                  have reads : Dynamic.ViewReads after (.arrayRef element' location) word.val element :=
                    .array read stored elementAt
                  have below : word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := layout) firstEvaluation.sound
                    secondEvaluation.sound coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  have readTyped := RuntimeEnvironmentHasTypes.cons pairTyped
                    (actualTyped.weaken (firstWorlds.trans worlds))
                  obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds,
                    suffixFrame, suffixAppend⟩ :=
                    CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime
                      (.array _) shaped word.isLt
                  rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
                  subst suffixAppend
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (memrefLoad_evaluates prepared keyType referenceEval coreReads)
                  let suffixPool : State headers keys ⟨scope, keyMap, futureWorld, after, _, canonical⟩ :=
                    (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
                  obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                    (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
                  exact ⟨_, _, after, keyMap, futureWorld,
                    .arrayResult occurrence rfl
                      (.cons (.arrayResult referenceOccurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                        (.elementRef (.array read stored) within)) .nil) (.memrefLoad reads),
                    .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
                    (firstWorlds.trans worlds).trans suffixWorlds,
                    (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
                    (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                      (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                      (.refl _) (.refl keyMap) suffixWorlds),
                    returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
                · have outside : Dynamic.ViewOutOfBounds after (.arrayRef element' location) word.val :=
                    .array read stored (by omega)
                  have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (memrefLoad_failure (elementRef_outOfBounds firstEvaluation.sound secondEvaluation.sound coreRead
                      outsideCore))
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayFault occurrence rfl (.headFault (.arrayResult referenceOccurrence rfl
                      (.cons firstTrace (.cons secondTrace .nil)) (.elementRefOutOfBounds outside))),
                    .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                    firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.store(lidx(a, i), v)`'s head: the array's and the index's meanings, then `0x32` from the
array's length on, else the value's meaning, and the array's cell takes the value at the index on both sides,
which gives `()`. -/
theorem store_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript value : ExpressionId} {referenceNode subscriptNode valueNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second third : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node .unit)
    (form : node.form = .memrefStore reference value)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (valueFound : invocation.source.lookupExpression? value = some valueNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (thirdChild : children scope value third)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (valueType : third.type = layout.valueType)
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨.unit, SourceCoreDataExpressions.memrefStore layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression) third.expression⟩)
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority
    physical owner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨unitType, element, referenceTypedAt, valueTypedAt⟩ :=
    store_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have valueTypeEq := CellAwareArraySourceInversion.typed_type unique valueFound valueTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have valueTyped : ExpressionHasType invocation.source context value valueNode.type := valueTypeEq ▸ valueTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have thirdIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ thirdChild _ valueFound valueTyped
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have unitRep : ValueRep compiled.compatible.checked receiving functions mapping world node.type .unit .unit .unit := by
    rw [unitType]; exact .unit
  have raw : ∃ result finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.memrefStore layout comparison.expression
        (SourceCoreDataExpressions.elementRef layout first.expression second.expression) third.expression).rename ξ)
        result finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type .unit faults outcome result ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [memrefStore_rename, elementRef_rename, closed_rename comparison.typed]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      rcases pair_fault failed with ⟨referenceSize, referenceSmaller, referenceTrace⟩ |
        ⟨referenceSize, valueSize, memref, middle₀, referenceSmaller, valueSmaller, referenceTrace, valueTrace⟩
      · cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
        | fault failed referenceChildren =>
          rcases pair_fault failed with ⟨firstSize, firstSmaller, firstTrace⟩ |
            ⟨firstSize, secondSize, baseSource, middle, firstSmaller, secondSmaller, firstTrace, secondTrace⟩
          · obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority
                physical owner ownerFrame firstTrace
            cases represented with
            | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld,
                memrefStore_reference_failure (elementRef_base_failure firstEval), .fault matched, finalHeaps, maps,
                worlds, frame, heapMetadata, effect, reached, related⟩
          · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps,
              firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
              firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority
                physical owner ownerFrame firstTrace
            cases represented with
            | @value _ coreValue payload =>
              obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
                heapMetadata, effect, reached, related, _⟩ :=
                secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                  (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                  (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                  (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                  secondTrace
              cases represented with
              | fault matched =>
                rw [rename_prefix] at secondEval
                exact ⟨_, finalStore, finalMap, finalWorld,
                  memrefStore_reference_failure (elementRef_index_failure firstEval secondEval), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                  firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                  callerProtocol.trans firstRelated related⟩
        | result evaluated result referenceChildren =>
          obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
            firstTrace, secondTrace⟩ := pair_values evaluated
          obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps,
            firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority
              physical owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | @value _ coreIndex indexPayload =>
              rw [rename_prefix] at secondEval
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              cases result with
              | elementRefIndexType notWord _ => exact (notWord trivial).elim
              | elementRefOutOfBounds outside =>
                obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
                obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
                cases outside with
                | @array _ _ cell elements _ read stored beyond =>
                  obtain ⟨measured, small⟩ :=
                    CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
                  cases measured with
                  | array coreRead =>
                    have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                      rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                      omega
                    exact ⟨_, keyStore, keyMap, keyWorld,
                      memrefStore_reference_failure (elementRef_outOfBounds firstEval secondEval coreRead outsideCore),
                      .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                      firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                      firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
      · cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
        | result evaluated result referenceChildren =>
          obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
            firstTrace, secondTrace⟩ := pair_values evaluated
          obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps,
            firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority
              physical owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, secondPost⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | @value _ coreIndex indexPayload =>
              rw [rename_prefix] at secondEval
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              cases result with
              | @elementRef _ _ _ _ _ _ count counted within =>
                obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
                obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
                cases measured with
                | array coreRead =>
                  have below : word < Word.ofNatModulo count := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := layout) firstEval secondEval coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  obtain ⟨_, finalStore, finalMap, finalWorld, thirdEval, represented, finalHeaps, valueMaps,
                    valueWorlds, valueFrame, valueMetadata, valueEffect, valueReached, valueRelated, _⟩ :=
                    thirdIH valueSize (by omega)
                      (environments.extend (firstMaps.trans maps) (firstWorlds.trans worlds)) keyHeaps
                      (locals.mono (firstMetadata.trans heapMetadata)) (agree_prefix agrees _)
                      (.cons pairTyped (actualTyped.weaken (firstWorlds.trans worlds))) reached secondPost.at_value.2
                      (authority.transport (firstEffect.trans effect))
                      (physical.transport (firstEffect.trans effect) (firstFrame.trans frame)) owner ownerFrame
                      valueTrace
                  cases represented with
                  | fault matched =>
                    rw [rename_prefix] at thirdEval
                    exact ⟨_, finalStore, finalMap, finalWorld, memrefStore_value_failure referenceEval thirdEval,
                      .fault matched, finalHeaps, (firstMaps.trans maps).trans valueMaps,
                      (firstWorlds.trans worlds).trans valueWorlds, (firstFrame.trans frame).trans valueFrame,
                      (firstMetadata.trans heapMetadata).trans valueMetadata,
                      (firstEffect.trans effect).trans valueEffect, valueReached,
                      callerProtocol.trans (callerProtocol.trans firstRelated related) valueRelated⟩
    | result evaluated result smaller =>
      obtain ⟨referenceSize, valueSize, memref, stored, middle₀, referenceSmaller, valueSmaller, rfl, referenceTrace,
        valueTrace⟩ := pair_values evaluated
      cases result with
      | @memrefStore _ _ _ _ element' _ _ _ _ _ _ read current replace written =>
        cases CellAwareArraySourceInversion.children unique referenceMetadata.found referenceForm rfl referenceTrace with
        | result evaluated result referenceChildren =>
          obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
            firstTrace, secondTrace⟩ := pair_values evaluated
          obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps,
            firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
            firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority
              physical owner ownerFrame firstTrace
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, secondPost⟩ :=
              secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
                secondTrace
            cases represented with
            | @value _ coreIndex indexPayload =>
              rw [rename_prefix] at secondEval
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              cases result with
              | @elementRef _ _ _ _ _ _ count counted within =>
                obtain ⟨target, payloadType, identity, rfl, typeEq, mapped, typed, arrayView⟩ :=
                  arrayRef_fields basePayload rfl
                rw [typeEq] at shaped
                simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq, true_and]
                  at shaped
                subst shaped
                obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload
                  (by rw [typeEq]; rfl)
                cases measured with
                | array coreRead =>
                  have below : word < Word.ofNatModulo count := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  have referenceEval := elementRef_evaluates (layout := ⟨.word, payloadType, identity⟩) firstEval
                    secondEval coreRead below
                  have pairTyped : RuntimeValueHasType keyWorld
                      (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                        (.word word)) (.product first.type .word)
                      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                    .pair basePayload.runtime_hasType .word
                  obtain ⟨_, valueStore, valueMap, valueWorld, thirdEval, represented, valueHeaps, valueMaps,
                    valueWorlds, valueFrame, valueMetadata, valueEffect, valueReached, valueRelated, _⟩ :=
                    thirdIH valueSize (by omega)
                      (environments.extend (firstMaps.trans maps) (firstWorlds.trans worlds)) keyHeaps
                      (locals.mono (firstMetadata.trans heapMetadata)) (agree_prefix agrees _)
                      (.cons pairTyped (actualTyped.weaken (firstWorlds.trans worlds))) reached secondPost.at_value.2
                      (authority.transport (firstEffect.trans effect))
                      (physical.transport (firstEffect.trans effect) (firstFrame.trans frame)) owner ownerFrame
                      valueTrace
                  cases represented with
                  | @value _ coreStored storedPayload =>
                    rw [rename_prefix] at thirdEval
                    rw [valueType] at storedPayload
                    have sameRuntime : SourceCoreRawMetadata.runtimeType element' =
                        SourceCoreRawMetadata.runtimeType valueNode.type := by
                      have view := arrayView
                      rw [← baseTypeEq] at view
                      simp only [TypeSystem.Ty.array, SourceCoreRawMetadata.runtimeType,
                        TypeSystem.Ty.application.injEq, true_and] at view
                      rw [← valueTypeEq, view]
                    obtain ⟨length, default, entries, suffix, futureWorld, storeRead, wordKeys, appended, finalHeaps,
                      futureWorlds, storeFrame, storeEffect⟩ :=
                      CellAwareArrayReads.store_preserve prepared valueHeaps
                        (actualTyped.weaken ((firstWorlds.trans worlds).trans valueWorlds)) read current replace
                        written (valueMaps.lookup mapped) (valueWorlds.lookup typed) storedPayload sameRuntime
                    have coreRun := memrefStore_evaluates prepared rfl referenceEval thirdEval storeRead wordKeys
                    rw [appended] at coreRun
                    let suffixPool : State headers keys ⟨scope, valueMap, futureWorld, after, _, canonical⟩ :=
                      (bridge.pool valueReached).extend (.refl _) futureWorlds storeFrame (.of_write written)
                    obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore valueReached suffixPool
                      (.refl _) futureWorlds storeFrame (.of_write written) (Relates.of_records_eq rfl)
                    exact ⟨_, _, valueMap, futureWorld, coreRun,
                      .value ((unitRep.extend (.refl _) ((firstMaps.trans maps).trans valueMaps)
                        (((firstWorlds.trans worlds).trans valueWorlds).trans futureWorlds))), finalHeaps,
                      (firstMaps.trans maps).trans valueMaps,
                      ((firstWorlds.trans worlds).trans valueWorlds).trans futureWorlds,
                      ((firstFrame.trans frame).trans valueFrame).trans storeFrame,
                      ((firstMetadata.trans heapMetadata).trans valueMetadata).trans (.of_write written),
                      ((firstEffect.trans effect).trans valueEffect).trans storeEffect, returned,
                      callerProtocol.trans (callerProtocol.trans (callerProtocol.trans firstRelated related)
                        valueRelated) returnedRelated⟩
  obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `CanStore.store(lidx(a, i), v)`'s head, reflected: the array's, the index's and the value's Core runs
give their Source runs; the array keeps its length while the value runs (`KeepsLengths`), so the Source store
applies at the position the bounds check admitted, and the store's Core run is the one it gives, or the one
`0x32` gives. -/
theorem store_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {reference subscript value : ExpressionId} {referenceNode subscriptNode valueNode : ExpressionNode} {fuel : Nat}
    {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second third : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node .unit)
    (form : node.form = .memrefStore reference value)
    (referenceMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source reference
      referenceNode (.product first.type .word))
    (referenceForm : referenceNode.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (valueFound : invocation.source.lookupExpression? value = some valueNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (thirdChild : children scope value third)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (valueType : third.type = layout.valueType)
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨.unit, SourceCoreDataExpressions.memrefStore layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression) third.expression⟩)
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ result finalStore environments heaps locals agrees actualTyped initial admitted
    authority physical owner ownerFrame evaluated
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨unitType, element, referenceTypedAt, valueTypedAt⟩ :=
    store_source_types unique found form metadata.coercions sourceTyped
  obtain ⟨baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    reference_source_types unique referenceMetadata.found referenceForm referenceMetadata.coercions referenceTypedAt
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have valueTypeEq := CellAwareArraySourceInversion.typed_type unique valueFound valueTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have valueTyped : ExpressionHasType invocation.source context value valueNode.type := valueTypeEq ▸ valueTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) := by rw [← baseTypeEq]
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have thirdIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ thirdChild _ valueFound valueTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.memrefStore reference value) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have referenceOccurrence : Staging.Recursive.Occurrence invocation reference (.elementRef base subscript) :=
    ⟨_, lookupExpression?_sound referenceMetadata.found, referenceForm, referenceMetadata.requirements,
      referenceMetadata.coercions⟩
  have unitRep : ValueRep compiled.compatible.checked receiving functions mapping world node.type .unit .unit .unit := by
    rw [unitType]; exact .unit
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type .unit faults outcome result ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.memrefStore layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout first.expression second.expression) third.expression).rename ξ)
      result finalStore at evaluated
    rw [memrefStore_rename, elementRef_rename, closed_rename comparison.typed] at evaluated
    have complete := evaluated.sound
    obtain ⟨tail, split⟩ := memrefStore_split layout comparison.expression
      (SourceCoreDataExpressions.elementRef layout (first.expression.rename ξ) (second.expression.rename ξ))
      (third.expression.rename ξ)
    obtain ⟨referenceTail, referenceSplit⟩ :=
      elementRef_split layout (first.expression.rename ξ) (second.expression.rename ξ)
    rw [split] at evaluated
    cases evaluated with
    | caseLeft referenceEvaluation _ =>
      have referenceComplete := referenceEvaluation.sound
      rw [referenceSplit] at referenceEvaluation
      cases referenceEvaluation with
      | caseLeft firstEvaluation _ =>
        obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
          frame, heapMetadata, effect, reached, related, _post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
            (memrefStore_reference_failure (elementRef_base_failure firstEvaluation.sound))
          exact ⟨_, _, after, finalMap, finalWorld,
            .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl (.headFault firstTrace))),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight firstEvaluation branch =>
        obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | @value baseSource coreValue payload =>
          cases branch with
          | caseLeft secondEvaluation _ =>
            have shifted := secondEvaluation
            rw [← rename_prefix] at shifted
            obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
            cases represented with
            | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                (memrefStore_reference_failure
                  (elementRef_index_failure firstEvaluation.sound secondEvaluation.sound))
              exact ⟨_, _, after, finalMap, finalWorld,
                .arrayFault occurrence rfl (.headFault (.arrayFault referenceOccurrence rfl
                  (.tailFault firstTrace (.headFault secondTrace)))), .fault matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
          | caseRight secondEvaluation _ =>
            have shifted := secondEvaluation
            rw [← rename_prefix] at shifted
            obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps,
              worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
            cases represented with
            | @value subscriptSource coreIndex indexPayload =>
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
              rw [← baseTypeEq] at baseSourceTyped
              obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
              obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
              obtain ⟨count, counted⟩ :=
                CellAwareArrayReads.length_cases keyHeaps rfl basePayload baseRuntime baseSourceTyped
              cases counted with
              | @array _ _ cell elements read cellStored =>
                obtain ⟨measured, small⟩ :=
                  CellAwareArrayReads.length_preserve keyHeaps (.array read cellStored) basePayload shaped
                cases measured with
                | array coreRead =>
                  by_cases within : word.val < elements.length
                  · have below : word < Word.ofNatModulo elements.length := by
                      rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                      exact within
                    obtain ⟨impossible, _⟩ := evaluation_deterministic referenceComplete
                      (elementRef_evaluates (layout := layout) firstEvaluation.sound secondEvaluation.sound coreRead
                        below)
                    cases impossible
                  · have outside : Dynamic.ViewOutOfBounds after (.arrayRef element' location) word.val :=
                      .array read cellStored (by omega)
                    have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                      rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                      exact within
                    obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                      (memrefStore_reference_failure (elementRef_outOfBounds firstEvaluation.sound
                        secondEvaluation.sound coreRead outsideCore))
                    exact ⟨_, _, after, keyMap, keyWorld,
                      .arrayFault occurrence rfl (.headFault (.arrayResult referenceOccurrence rfl
                        (.cons firstTrace (.cons secondTrace .nil)) (.elementRefOutOfBounds outside))),
                      .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                      firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                      firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
    | caseRight referenceEvaluation branch =>
      have referenceComplete := referenceEvaluation.sound
      rw [referenceSplit] at referenceEvaluation
      cases referenceEvaluation with
      | caseLeft firstEvaluation _ =>
        obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
          frame, heapMetadata, effect, reached, related, _post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | fault matched =>
          obtain ⟨impossible, _⟩ := evaluation_deterministic referenceComplete
            (elementRef_base_failure firstEvaluation.sound)
          cases impossible
      | caseRight firstEvaluation innerBranch =>
        obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | @value baseSource coreValue payload =>
          cases innerBranch with
          | caseLeft secondEvaluation _ =>
            have shifted := secondEvaluation
            rw [← rename_prefix] at shifted
            obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
              secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
            cases represented with
            | fault matched =>
              obtain ⟨impossible, _⟩ := evaluation_deterministic referenceComplete
                (elementRef_index_failure firstEvaluation.sound secondEvaluation.sound)
              cases impossible
          | caseRight secondEvaluation _ =>
            have shifted := secondEvaluation
            rw [← rename_prefix] at shifted
            obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps,
              worlds, frame, heapMetadata, effect, reached, related, secondPost⟩ :=
              secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) (agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
                (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame shifted
            cases represented with
            | @value subscriptSource coreIndex indexPayload =>
              rw [← subscriptTypeEq] at indexPayload
              obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
              have basePayload := payload.extend (.refl _) maps worlds
              have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
              rw [← baseTypeEq] at baseSourceTyped
              obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
              obtain ⟨target, payloadType, identity, rfl, typeEq, mapped, typed, arrayView⟩ :=
                arrayRef_fields basePayload rfl
              rw [typeEq] at shaped
              simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq, true_and] at shaped
              subst shaped
              obtain ⟨count, counted⟩ :=
                CellAwareArrayReads.length_cases keyHeaps rfl basePayload baseRuntime baseSourceTyped
              cases counted with
              | @array _ _ cell elements read cellStored =>
                obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps (.array read cellStored)
                  basePayload (by rw [typeEq]; rfl)
                cases measured with
                | array coreRead =>
                  by_cases within : word.val < elements.length
                  · have below : word < Word.ofNatModulo elements.length := by
                      rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                      exact within
                    have referenceEval := elementRef_evaluates (layout := ⟨.word, payloadType, identity⟩)
                      firstEvaluation.sound secondEvaluation.sound coreRead below
                    obtain ⟨sameValue, rfl⟩ := evaluation_deterministic referenceComplete referenceEval
                    cases sameValue
                    have referenceTrace := Staging.Recursive.Size.Expression.arrayResult referenceOccurrence rfl
                      (.cons firstTrace (.cons secondTrace .nil)) (.elementRef (.array read cellStored) within)
                    have pairTyped : RuntimeValueHasType keyWorld
                        (.pair (.cellRef (.product .word (.product payloadType (.namedData identity))) target)
                          (.word word)) (.product first.type .word)
                        (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                      .pair basePayload.runtime_hasType .word
                    cases branch with
                    | caseLeft valueEvaluation _ =>
                      have shiftedValue := valueEvaluation
                      rw [← rename_prefix] at shiftedValue
                      obtain ⟨thirdSize, thirdOutcome, final, finalMap, finalWorld, thirdTrace, represented,
                        finalHeaps, valueMaps, valueWorlds, valueFrame, valueMetadata, valueEffect, valueReached,
                        valueRelated, _post⟩ :=
                        thirdIH _ (by omega)
                          (environments.extend (firstMaps.trans maps) (firstWorlds.trans worlds)) keyHeaps
                          (locals.mono (firstMetadata.trans heapMetadata)) (agree_prefix agrees _)
                          (.cons pairTyped (actualTyped.weaken (firstWorlds.trans worlds))) reached
                          secondPost.at_value.2 (authority.transport (firstEffect.trans effect))
                          (physical.transport (firstEffect.trans effect) (firstFrame.trans frame)) owner ownerFrame
                          shiftedValue
                      cases represented with
                      | fault matched =>
                        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                          (memrefStore_value_failure referenceEval valueEvaluation.sound)
                        exact ⟨_, _, final, finalMap, finalWorld,
                          .arrayFault occurrence rfl (.tailFault referenceTrace (.headFault thirdTrace)),
                          .fault matched, finalHeaps, (firstMaps.trans maps).trans valueMaps,
                          (firstWorlds.trans worlds).trans valueWorlds, (firstFrame.trans frame).trans valueFrame,
                          (firstMetadata.trans heapMetadata).trans valueMetadata,
                          (firstEffect.trans effect).trans valueEffect, valueReached,
                          callerProtocol.trans (callerProtocol.trans firstRelated related) valueRelated⟩
                    | caseRight valueEvaluation _ =>
                      have shiftedValue := valueEvaluation
                      rw [← rename_prefix] at shiftedValue
                      obtain ⟨thirdSize, thirdOutcome, valueHeap, valueMap, valueWorld, thirdTrace, represented,
                        valueHeaps, valueMaps, valueWorlds, valueFrame, valueMetadata, valueEffect, valueReached,
                        valueRelated, _post⟩ :=
                        thirdIH _ (by omega)
                          (environments.extend (firstMaps.trans maps) (firstWorlds.trans worlds)) keyHeaps
                          (locals.mono (firstMetadata.trans heapMetadata)) (agree_prefix agrees _)
                          (.cons pairTyped (actualTyped.weaken (firstWorlds.trans worlds))) reached
                          secondPost.at_value.2 (authority.transport (firstEffect.trans effect))
                          (physical.transport (firstEffect.trans effect) (firstFrame.trans frame)) owner ownerFrame
                          shiftedValue
                      cases represented with
                      | @value stored coreStored storedPayload =>
                        rw [valueType] at storedPayload
                        have sameRuntime : SourceCoreRawMetadata.runtimeType element' =
                            SourceCoreRawMetadata.runtimeType valueNode.type := by
                          have view := arrayView
                          rw [← baseTypeEq] at view
                          simp only [TypeSystem.Ty.array, SourceCoreRawMetadata.runtimeType,
                            TypeSystem.Ty.application.injEq, true_and] at view
                          rw [← valueTypeEq, view]
                        have preserved := Staging.Recursive.SelectedPreservation.expression selectedBodies runtime
                          covers (locals.mono (firstMetadata.trans heapMetadata)) secondPost.at_value.2.heap
                          valueTyped thirdTrace
                        obtain ⟨kept, keptElements, keptRead, keptStored, keptLength⟩ :=
                          preserved.lengths stored rfl location cell element' elements read cellStored
                        obtain ⟨updated, replace⟩ := replace_exists stored (by rw [keptLength]; exact within)
                        obtain ⟨finalHeap, written⟩ :=
                          CompatibleExpressionReadCompletion.writes_exists keptRead (.arrayObject element' updated)
                        obtain ⟨length, default, entries, suffix, futureWorld, storeRead, wordKeys, appended,
                          finalHeaps, futureWorlds, storeFrame, storeEffect⟩ :=
                          CellAwareArrayReads.store_preserve prepared valueHeaps
                            (actualTyped.weaken ((firstWorlds.trans worlds).trans valueWorlds)) keptRead keptStored
                            replace written (valueMaps.lookup mapped) (valueWorlds.lookup typed) storedPayload
                            sameRuntime
                        have coreRun := memrefStore_evaluates prepared rfl referenceEval valueEvaluation.sound
                          storeRead wordKeys
                        rw [appended] at coreRun
                        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
                        let suffixPool : State headers keys ⟨scope, valueMap, futureWorld, finalHeap, _, canonical⟩ :=
                          (bridge.pool valueReached).extend (.refl _) futureWorlds storeFrame (.of_write written)
                        obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore valueReached suffixPool
                          (.refl _) futureWorlds storeFrame (.of_write written) (Relates.of_records_eq rfl)
                        exact ⟨_, _, finalHeap, valueMap, futureWorld,
                          .arrayResult occurrence rfl (.cons referenceTrace (.cons thirdTrace .nil))
                            (.memrefStore keptRead keptStored replace written),
                          .value ((unitRep.extend (.refl _) ((firstMaps.trans maps).trans valueMaps)
                            (((firstWorlds.trans worlds).trans valueWorlds).trans futureWorlds))), finalHeaps,
                          (firstMaps.trans maps).trans valueMaps,
                          ((firstWorlds.trans worlds).trans valueWorlds).trans futureWorlds,
                          ((firstFrame.trans frame).trans valueFrame).trans storeFrame,
                          ((firstMetadata.trans heapMetadata).trans valueMetadata).trans (.of_write written),
                          ((firstEffect.trans effect).trans valueEffect).trans storeEffect, returned,
                          callerProtocol.trans (callerProtocol.trans (callerProtocol.trans firstRelated related)
                            valueRelated) returnedRelated⟩
                  · have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                      rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                      exact within
                    obtain ⟨impossible, _⟩ := evaluation_deterministic referenceComplete
                      (elementRef_outOfBounds (layout := ⟨.word, payloadType, identity⟩) firstEvaluation.sound
                        secondEvaluation.sound coreRead outsideCore)
                    cases impossible
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `lidx(a, i)`'s head: the array's and the index's meanings, then `0x32` from the array's length on, else the
memref, the pair of the array's Core cell and the index. -/
theorem elementRef_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {subscript : ExpressionId} {subscriptNode : ExpressionNode}
    {layout : OrderedMapping.Layout} {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type .word))
    (form : node.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (code : lowered = ⟨.product first.type .word,
      SourceCoreDataExpressions.elementRef layout first.expression second.expression⟩)
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority
    physical owner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨element, nodeType, baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    elementRef_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) := by rw [← baseTypeEq]
  obtain ⟨firstTypeEq, _⟩ := CellAwareArrayCells.viewShape_zero shaped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.elementRef layout first.expression
        second.expression).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type (.product first.type .word) faults
        outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [elementRef_rename]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      rcases pair_fault failed with ⟨firstSize, firstSmaller, firstTrace⟩ |
        ⟨firstSize, secondSize, baseSource, middle, firstSmaller, secondSmaller, firstTrace, secondTrace⟩
      · obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, _⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, elementRef_base_failure firstEval, firstTypeEq ▸ .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame
              secondTrace
          cases represented with
          | fault matched =>
            rw [rename_prefix] at secondEval
            exact ⟨_, finalStore, finalMap, finalWorld, elementRef_index_failure firstEval secondEval,
              firstTypeEq ▸ .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl,
        firstTrace, secondTrace⟩ := pair_values evaluated
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
        firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, _⟩ :=
          secondIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
            (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | @value _ coreIndex indexPayload =>
          rw [rename_prefix] at secondEval
          rw [← subscriptTypeEq] at indexPayload
          obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
          have basePayload := payload.extend (.refl _) maps worlds
          cases result with
          | elementRefIndexType notWord _ => exact (notWord trivial).elim
          | elementRefOutOfBounds outside =>
            obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
            obtain ⟨target, payloadType, identity, rfl, _, _, _, _⟩ := arrayRef_fields basePayload rfl
            cases outside with
            | @array _ _ cell elements _ read stored beyond =>
              obtain ⟨measured, small⟩ :=
                CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
              cases measured with
              | array coreRead =>
                have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                  rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                  omega
                exact ⟨_, keyStore, keyMap, keyWorld, elementRef_outOfBounds firstEval secondEval coreRead outsideCore,
                  firstTypeEq ▸ .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                  firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                  firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
          | @elementRef _ _ _ _ _ _ count counted within =>
            obtain ⟨target, payloadType, identity, rfl, _, _, _, view⟩ := arrayRef_fields basePayload rfl
            obtain ⟨measured, small⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            cases measured with
            | array coreRead =>
              have below : word < Word.ofNatModulo count := by
                rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                exact within
              have memrefRep := memref_of_arrayRef basePayload rfl word.isLt
              rw [CellAwareArrayReads.ofNatModulo_self] at memrefRep
              exact ⟨_, keyStore, keyMap, keyWorld, elementRef_evaluates firstEval secondEval coreRead below,
                .value (.compatible (memref_runtime nodeType (baseRuntime.symm.trans view)) memrefRep), keyHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `lidx(a, i)`'s head, reflected: the array's and the index's Core runs give their Source runs, and the
check's Core run is the one the Source check gives: the memref below the array's length, else `0x32`. -/
theorem elementRef_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {subscript : ExpressionId} {subscriptNode : ExpressionNode}
    {layout : OrderedMapping.Layout} {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type .word))
    (form : node.form = .elementRef base subscript)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0, layout))
    (code : lowered = ⟨.product first.type .word,
      SourceCoreDataExpressions.elementRef layout first.expression second.expression⟩)
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted
    authority physical owner ownerFrame evaluated
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'; subst code
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨element, nodeType, baseTypedAt, subscriptType, subscriptTypedAt, kind⟩ :=
    elementRef_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  have baseTyped : ExpressionHasType invocation.source context base baseNode.type := baseTypeEq ▸ baseTypedAt
  have subscriptTyped : ExpressionHasType invocation.source context subscript subscriptNode.type :=
    subscriptTypeEq ▸ subscriptTypedAt
  have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) := by rw [← baseTypeEq]
  obtain ⟨firstTypeEq, _⟩ := CellAwareArrayCells.viewShape_zero shaped
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.elementRef base subscript) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type (.product first.type .word) faults
        outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.elementRef layout first.expression
      second.expression).rename ξ) value finalStore at evaluated
    rw [elementRef_rename] at evaluated
    have complete := evaluated.sound
    obtain ⟨tail, split⟩ := elementRef_split layout (first.expression.rename ξ) (second.expression.rename ξ)
    rw [split] at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (elementRef_base_failure firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
          firstTypeEq ▸ .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, firstMaps,
        firstWorlds, firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        cases branch with
        | caseLeft secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (elementRef_index_failure firstEvaluation.sound secondEvaluation.sound)
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.tailFault firstTrace (.headFault secondTrace)), firstTypeEq ▸ .fault matched,
              finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps, worlds,
            frame, heapMetadata, effect, reached, related, _post⟩ :=
            secondIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value subscriptSource coreIndex indexPayload =>
            rw [← subscriptTypeEq] at indexPayload
            obtain ⟨word, rfl, rfl, _⟩ := index_word_fields kind indexPayload
            have basePayload := payload.extend (.refl _) maps worlds
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨element', location, rfl⟩ := array_source basePayload baseRuntime
            obtain ⟨target, payloadType, identity, rfl, _, _, _, view⟩ := arrayRef_fields basePayload rfl
            obtain ⟨count, counted⟩ :=
              CellAwareArrayReads.length_cases keyHeaps rfl basePayload baseRuntime baseSourceTyped
            cases counted with
            | @array _ _ cell elements read stored =>
              obtain ⟨measured, small⟩ :=
                CellAwareArrayReads.length_preserve keyHeaps (.array read stored) basePayload shaped
              cases measured with
              | array coreRead =>
                by_cases within : word.val < elements.length
                · have below : word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (elementRef_evaluates firstEvaluation.sound secondEvaluation.sound coreRead below)
                  have memrefRep := memref_of_arrayRef basePayload rfl word.isLt
                  rw [CellAwareArrayReads.ofNatModulo_self] at memrefRep
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                      (.elementRef (.array read stored) within),
                    .value (.compatible (memref_runtime nodeType (baseRuntime.symm.trans view)) memrefRep), keyHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                    callerProtocol.trans firstRelated related⟩
                · have outside : Dynamic.ViewOutOfBounds after (.arrayRef element' location) word.val :=
                    .array read stored (by omega)
                  have outsideCore : ¬ word < Word.ofNatModulo elements.length := by
                    rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val small]
                    exact within
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                    (elementRef_outOfBounds firstEvaluation.sound secondEvaluation.sound coreRead outsideCore)
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                      (.elementRefOutOfBounds outside),
                    firstTypeEq ▸ .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
                    firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
                    firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end
