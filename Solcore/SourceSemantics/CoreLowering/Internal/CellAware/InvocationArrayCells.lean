import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrays

/-!
# Cell-aware invocations: memory arrays' allocations

The heads of the array forms that allocate a fresh array on both sides, with the array's cell in the
whole-cell heap relation, its Core layout registered (`DefaultLayouts`), and the default element: zero, or
one fresh empty array, the Core default's last cell after the Core-only cells of its own element's default
(`CellAwareArrayCells.default_preserve`). Main declarations: `CellAwareInvocationArrayBounds.new_preserves`,
`literal_preserves`, `copy_preserves` for `toArray(a[s:e])`, and their `reflects`.
-/

section
/-! A default element's code on Core values, typed in the world it extends, and `new T[](n)`'s default on
both sides. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

/-- The layouts that an element type's default allocates are registered: for an array element, its own
array's layout and its element's, down to a scalar. -/
inductive DefaultLayouts (catalog : SourceCoreCompatibleCatalog.Catalog) (definitions : DataEnvironment) :
    TypeSystem.Ty → Prop
  | scalar {element : TypeSystem.Ty} (notArray : ∀ inner, element ≠ TypeSystem.Ty.array inner) :
      DefaultLayouts catalog definitions element
  | array {inner : TypeSystem.Ty}
      (registered : ∀ innerType identity, catalog.project inner = .ok innerType →
        catalog.identity? (.mapping (.constructor (.builtin .word)) inner) = some identity →
        (GenericHeap.arrayLayout innerType identity).Registered definitions)
      (rest : DefaultLayouts catalog definitions inner) :
      DefaultLayouts catalog definitions (TypeSystem.Ty.array inner)

theorem DefaultLayouts.extend {catalog : SourceCoreCompatibleCatalog.Catalog} {initial future : DataEnvironment}
    (extension : initial.Extends future) {element : TypeSystem.Ty}
    (layouts : DefaultLayouts catalog initial element) : DefaultLayouts catalog future element := by
  induction layouts with
  | scalar notArray => exact .scalar notArray
  | array registered _ ih =>
    exact .array (fun innerType identity projected identified =>
      (registered innerType identity projected identified).extend_definitions extension) ih

theorem empty_typed {definitions : DataEnvironment} {world : StoreTyping} {payload : Ty} {identity : DataTypeId}
    (registered : (GenericHeap.arrayLayout payload identity).Registered definitions) :
    RuntimeValueHasType world (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) [])
      (.namedData identity) definitions :=
  OrderedMapping.encode_hasType registered [] fun _ _ member => by cases member

theorem default_parts {catalog : SourceCoreCompatibleCatalog.Catalog} {inner : TypeSystem.Ty} {default : Expr}
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault catalog (TypeSystem.Ty.array inner) = some default) :
    ∃ innerType identity innerDefault, catalog.project inner = .ok innerType ∧
      catalog.identity? (.mapping (.constructor (.builtin .word)) inner) = some identity ∧
      SourceCoreCompatibleDataExpressions.arrayDefault catalog inner = some innerDefault ∧
      default = .newCell (.product .word (.product innerType (.namedData identity)))
        (.pair (.word Word.zero) (.pair innerDefault (OrderedMapping.empty ⟨.word, innerType, identity⟩))) := by
  simp only [TypeSystem.Ty.array, SourceCoreCompatibleDataExpressions.arrayDefault] at defined
  cases innerProjected : catalog.project inner with
  | error => simp [innerProjected, Except.toOption, bind, Option.bind] at defined
  | ok innerType =>
    cases identified : catalog.identity? (.mapping (.constructor (.builtin .word)) inner) <;>
      cases innerDefined : SourceCoreCompatibleDataExpressions.arrayDefault catalog inner <;>
      simp only [innerProjected, identified, innerDefined, Except.toOption, bind, Option.bind, reduceCtorEq,
        Option.some.injEq] at defined
    rename_i identity innerDefault
    exact ⟨innerType, identity, innerDefault, rfl, rfl, rfl, defined.symm⟩

theorem array_projected {catalog : SourceCoreCompatibleCatalog.Catalog} {inner : TypeSystem.Ty}
    {innerType : Ty} {identity : DataTypeId} {payload : Ty}
    (innerProjected : catalog.project inner = .ok innerType)
    (identified : catalog.identity? (.mapping (.constructor (.builtin .word)) inner) = some identity)
    (projected : catalog.project (TypeSystem.Ty.array inner) = .ok payload) :
    payload = .cell (.product .word (.product innerType (.namedData identity))) := by
  simp only [TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreRawMetadata.runtimeType,
    innerProjected, identified, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at projected
  exact projected.symm

/-- A default element's code runs to a value of the element's Core type, after cells the world types. -/
theorem default_runs {catalog : SourceCoreCompatibleCatalog.Catalog} {definitions : DataEnvironment}
    {element : TypeSystem.Ty} {default : Expr} {payload : Ty}
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault catalog element = some default)
    (projected : catalog.project element = .ok payload)
    (layouts : DefaultLayouts catalog definitions element)
    (environment : Environment) {world : StoreTyping} {store : Store}
    (storeTyped : RuntimeStoreHasTypes world store definitions) :
    ∃ value cells futureWorld, Evaluates environment store default value (store ++ cells) ∧
      WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld (store ++ cells) definitions ∧
      RuntimeValueHasType futureWorld value payload definitions := by
  induction element using SourceCoreCompatibleDataExpressions.arrayDefault.induct
    generalizing default payload world store with
  | case1 =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    simp only [SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure, Except.ok.injEq] at projected
    subst payload
    exact ⟨_, [], world, by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store),
      .refl _, by simpa using storeTyped, .word⟩
  | case2 type =>
    simp only [SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    simp only [SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure, Except.ok.injEq] at projected
    subst payload
    exact ⟨_, [], world, by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store),
      .refl _, by simpa using storeTyped, .word⟩
  | case3 inner ih =>
    obtain ⟨innerType, identity, innerDefault, innerProjected, identified, innerDefined, rfl⟩ :=
      default_parts defined
    have payloadEq := array_projected innerProjected identified projected
    subst payloadEq
    cases layouts with
    | scalar notArray => exact absurd rfl (notArray inner)
    | array registeredAll innerLayouts =>
    have registered := registeredAll innerType identity innerProjected identified
    obtain ⟨innerValue, innerCells, innerWorld, innerEvaluated, innerWorlds, innerStoreTyped, innerTyped⟩ :=
      ih innerDefined innerProjected innerLayouts storeTyped
    have cellTyped : RuntimeValueHasType innerWorld
        (.pair (.word Word.zero) (.pair innerValue
          (OrderedMapping.encode (GenericHeap.arrayLayout innerType identity) [])))
        (.product .word (.product innerType (.namedData identity))) definitions :=
      .pair .word (.pair innerTyped (empty_typed registered))
    have allocated := RuntimeStoreHasTypes.allocate innerStoreTyped cellTyped
    refine ⟨.cellRef (.product .word (.product innerType (.namedData identity))) (store ++ innerCells).length,
      innerCells ++ [.pair (.word Word.zero) (.pair innerValue
        (OrderedMapping.encode (GenericHeap.arrayLayout innerType identity) []))],
      innerWorld ++ [.product .word (.product innerType (.namedData identity))], ?_,
      innerWorlds.trans ⟨_, rfl⟩, ?_, ?_⟩
    · rw [← List.append_assoc]
      exact .newCell (.pair .word (.pair innerEvaluated (.construct .unit)))
    · rw [← List.append_assoc]
      exact allocated
    · apply RuntimeValueHasType.cellRef
      rw [List.getElem?_append_right (by rw [innerStoreTyped.length_eq]; exact Nat.le_refl _)]
      simp [innerStoreTyped.length_eq]
  | case4 other notWord notFixed notArray =>
    rw [SourceCoreCompatibleDataExpressions.arrayDefault.eq_def] at defined
    split at defined
    · exact absurd rfl notWord
    · exact absurd rfl (notFixed _)
    · exact absurd rfl (notArray _)
    · cases defined

section Defaults
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

/-- `new T[](n)`'s default element on both sides: zero, or one fresh empty array, the Core default's last
cell, after the Core-only cells of its own element's default. -/
theorem default_preserve {mapping : LocationMap} {world : StoreTyping} {heap defaulted : Dynamic.Heap}
    {store : Store} {element : TypeSystem.Ty} {zero : Dynamic.Value} {default : Expr} {payload : Ty}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (sourceDefault : Dynamic.NewArrayDefault heap element zero defaulted)
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault checked.catalog element = some default)
    (projected : checked.catalog.project element = .ok payload)
    (layouts : DefaultLayouts checked.catalog ambient.definitions element) (environment : Environment) :
    ∃ value suffix futureMap futureWorld,
      Evaluates environment store default value (store ++ suffix) ∧
      ValueRep checked registry functions futureMap futureWorld element zero value payload ∧
      GenericHeap.CellHeapRepresents cells futureMap futureWorld defaulted (store ++ suffix) ∧
      LocationMap.Extends mapping futureMap ∧ WorldExtends world futureWorld ∧
      AdministrativePreserved mapping store futureMap (store ++ suffix) ∧
      Dynamic.HeapMetadataExtend heap defaulted := by
  cases sourceDefault with
  | word =>
    simp only [TypeSystem.Ty.word, SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    simp only [TypeSystem.Ty.word, SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure,
      Except.ok.injEq] at projected
    subst payload
    exact ⟨_, [], mapping, world, by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store),
      .word _, by simpa using heaps, .refl _, .refl _, by simpa using AdministrativePreserved.refl mapping store,
      .refl _⟩
  | fixed type =>
    simp only [TypeSystem.Ty.fixed, SourceCoreCompatibleDataExpressions.arrayDefault, Option.some.injEq] at defined
    subst default
    simp only [TypeSystem.Ty.fixed, SourceCoreCompatibleCatalog.Catalog.project, pure, Except.pure,
      Except.ok.injEq] at projected
    subst payload
    exact ⟨_, [], mapping, world, by simpa using (Evaluates.word : Evaluates environment store (.word Word.zero) _ store),
      .fixed _ (TypeSystem.FixedInteger.canonical_zero type), by simpa using heaps, .refl _, .refl _,
      by simpa using AdministrativePreserved.refl mapping store, .refl _⟩
  | @array after inner location allocates =>
    obtain ⟨innerType, identity, innerDefault, innerProjected, identified, innerDefined, rfl⟩ :=
      default_parts defined
    have payloadEq := array_projected innerProjected identified projected
    subst payloadEq
    cases layouts with
    | scalar notArray => exact absurd rfl (notArray inner)
    | array registeredAll innerLayouts =>
    have registered := registeredAll innerType identity innerProjected identified
    obtain ⟨innerValue, innerCells, innerWorld, innerEvaluated, innerWorlds, innerStoreTyped, innerTyped⟩ :=
      default_runs innerDefined innerProjected innerLayouts environment heaps.runtime_hasTypes
    have innerHeaps := CellMappingHeap.heap_append heaps innerWorlds innerStoreTyped
    have represented : GenericHeap.ArrayCellRepresents (CompatibleAmbientHeap.payloadModel checked registry functions)
        mapping innerWorld ⟨.arrayObject inner, some (.arrayObject inner []), none⟩
        (.pair (.word Word.zero) (.pair innerValue
          (OrderedMapping.encode (GenericHeap.arrayLayout innerType identity) [])))
        (.product .word (.product innerType (.namedData identity))) :=
      ⟨inner, [], innerType, identity, innerValue, [], rfl, rfl, rfl,
        { projection := innerProjected
          registered := registered
          bounded := by simp [wordModulus]
          default_typed := innerTyped
          keys := fun _ _ member => by cases member
          entries_typed := fun _ _ member => by cases member
          represented := fun _ below => by cases below }⟩
    obtain ⟨finalHeaps, mapped, typed⟩ := innerHeaps.allocate_array represented allocates
    refine ⟨.cellRef (.product .word (.product innerType (.namedData identity))) (store ++ innerCells).length,
      innerCells ++ [.pair (.word Word.zero) (.pair innerValue
        (OrderedMapping.encode (GenericHeap.arrayLayout innerType identity) []))],
      mapping ++ [(store ++ innerCells).length],
      innerWorld ++ [.product .word (.product innerType (.namedData identity))], ?_,
      .arrayRef innerProjected identified mapped typed, ?_, ⟨_, rfl⟩, innerWorlds.trans ⟨_, rfl⟩, ?_,
      Dynamic.HeapMetadataExtend.of_allocation allocates⟩
    · rw [← List.append_assoc]
      exact .newCell (.pair .word (.pair innerEvaluated (.construct .unit)))
    · rw [← List.append_assoc]
      exact finalHeaps
    · rw [← List.append_assoc]
      exact (CellMappingHeap.administrative_append mapping store innerCells).trans
        (AdministrativePreserved.allocate mapping (store ++ innerCells) _)

end Defaults

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
end

section
/-! An array type's projection, the default's existence and the length limit's word. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

theorem array_parts {catalog : SourceCoreCompatibleCatalog.Catalog} {element : TypeSystem.Ty} {payload : Ty}
    {identity : DataTypeId}
    (projected : catalog.project (TypeSystem.Ty.array element) =
      .ok (CompatibleExpressionArrays.arrayType payload identity)) :
    catalog.project element = .ok payload ∧
      catalog.identity? (.mapping (.constructor (.builtin .word)) element) = some identity := by
  simp only [TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreRawMetadata.runtimeType,
    bind, Except.bind] at projected
  cases elementProjected : catalog.project element with
  | error => simp [elementProjected] at projected
  | ok elementType =>
    cases identified : catalog.identity? (.mapping (.constructor (.builtin .word)) element) with
    | none => simp [elementProjected, identified, throw, throwThe] at projected
    | some found =>
      simp only [elementProjected, identified, pure, Except.pure, Except.ok.injEq,
        CompatibleExpressionArrays.arrayType, Ty.cell.injEq, Ty.product.injEq, Ty.namedData.injEq,
        true_and] at projected
      obtain ⟨rfl, rfl⟩ := projected
      exact ⟨rfl, rfl⟩

theorem default_exists (heap : Dynamic.Heap) {element : TypeSystem.Ty} (allowed : element.arrayElementAllowed = true) :
    ∃ zero defaulted, Dynamic.NewArrayDefault heap element zero defaulted := by
  unfold TypeSystem.Ty.arrayElementAllowed at allowed
  split at allowed
  · exact ⟨_, _, .word heap⟩
  · exact ⟨_, _, .fixed heap _⟩
  · exact ⟨_, _, .array .append⟩
  · cases allowed

theorem limit_small : SourceCoreDataExpressions.arrayLengthLimit < wordModulus := by
  simp [SourceCoreDataExpressions.arrayLengthLimit, wordModulus]

theorem limit_lt (count : Word) :
    count < Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit ↔ count.val < Dynamic.newArrayLengthLimit := by
  rw [Fin.lt_def, CellAwareArrayReads.ofNatModulo_val limit_small]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
end

section
/-! `new T[](n)`: the length, then `0x41` from `2^251 − 1` on, else the default and the array's cell. -/
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

/-- `new T[](n)` is of `T[]` for an element `T[]` admits, and its length a `uint256`. -/
theorem new_source_types {source : TypedSource} {context : SourceSemantics.Context} {id length : ExpressionId}
    {element : TypeSystem.Ty} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node) (form : node.form = .newArray element length)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    node.type = TypeSystem.Ty.array element ∧ element.arrayElementAllowed = true ∧
      ExpressionHasType source context length (.fixed .uint256) := by
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
    | newArray allowed _ lengthTyped => exact ⟨rfl, allowed, lengthTyped⟩

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
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {first lowered : SourceCoreBasic.LoweredExpr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions faults unique selectedBodies runtime covers in
/-- `new T[](n)`'s head: the length's meaning, then `0x41` from the limit on, else the default element and
one fresh array of the length on both sides. -/
theorem new_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {length : ExpressionId} {lengthNode : ExpressionNode} {payload : Ty}
    {identity : DataTypeId} {default : Expr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (CompatibleExpressionArrays.arrayType payload identity))
    (form : node.form = .newArray element length)
    (lengthFound : invocation.source.lookupExpression? length = some lengthNode)
    (firstChild : children scope length first)
    (projected : compiled.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
      .ok (CompatibleExpressionArrays.arrayType payload identity))
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault compiled.compatible.checked.catalog element = some default)
    (layouts : DefaultLayouts compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (TypeSystem.Ty.array element))
    (code : lowered = ⟨CompatibleExpressionArrays.arrayType payload identity,
      SourceCoreDataExpressions.newArray (CompatibleExpressionArrays.arrayLayout payload identity) default
        first.expression⟩)
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
  obtain ⟨nodeType, allowed, lengthTypedAt⟩ := new_source_types unique found form metadata.coercions sourceTyped
  have lengthTypeEq := CellAwareArraySourceInversion.typed_type unique lengthFound lengthTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have lengthTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change length ∈ [length]; simp) lengthFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ lengthFound lengthTyped
  obtain ⟨elementProjected, identified⟩ := array_parts projected
  cases layouts with
  | scalar notArray => exact absurd rfl (notArray element)
  | array registeredAll elementLayouts =>
  have registered := registeredAll payload identity elementProjected identified
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.newArray (CompatibleExpressionArrays.arrayLayout payload identity)
        default first.expression).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (CompatibleExpressionArrays.arrayType payload identity) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [newArray_rename, arrayDefault_rename defined]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨childSize, childSmaller, childTrace⟩ := single_fault failed
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, newArray_length_failure firstEval, .fault matched, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | result evaluated result smaller =>
      obtain ⟨childSize, lengthSource, childSmaller, rfl, childTrace⟩ := single_values evaluated
      obtain ⟨_, keyStore, keyMap, keyWorld, firstEval, represented, keyHeaps, maps, worlds, frame, heapMetadata,
        effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | @value _ coreLength lengthPayload =>
        rw [← lengthTypeEq] at lengthPayload
        obtain ⟨count, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) lengthPayload
        cases result with
        | @newArray _ _ _ defaulted _ _ zero location fits sourceDefault allocates =>
          obtain ⟨defaultValue, suffix, defaultMap, defaultWorld, defaultEval, zeroRep, defaultHeaps, defaultMaps,
            defaultWorlds, defaultFrame, defaultMetadata⟩ :=
            default_preserve keyHeaps sourceDefault defined elementProjected elementLayouts (.word count :: actual)
          have represented : GenericHeap.ArrayCellRepresents model defaultMap defaultWorld
              ⟨.arrayObject element, some (.arrayObject element (List.replicate count.val zero)), none⟩
              (.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) [])))
              (.product .word (.product payload (.namedData identity))) :=
            ⟨element, List.replicate count.val zero, payload, identity, defaultValue, [], rfl,
              by simp [CellAwareArrayReads.ofNatModulo_self], rfl,
              { projection := elementProjected
                registered := registered
                bounded := by simp
                default_typed := zeroRep.runtime_hasType
                keys := fun _ _ member => by cases member
                entries_typed := fun _ _ member => by cases member
                represented := fun position below => by
                  simp only [List.getElem_replicate, GenericHeap.arrayEntry, OrderedMapping.lookupEntries,
                    Option.getD_none]
                  exact zeroRep }⟩
          obtain ⟨finalHeaps, mapped, typed⟩ := defaultHeaps.allocate_array represented allocates
          have coreRun := newArray_evaluates (layout := CompatibleExpressionArrays.arrayLayout payload identity) firstEval
            ((limit_lt count).mpr fits) (by rw [arrayDefault_weaken defined]; exact defaultEval)
          have extended : (keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) =
              keyStore ++ (suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) := by simp
          have finalFrame : AdministrativePreserved keyMap keyStore (defaultMap ++ [(keyStore ++ suffix).length])
              (keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) :=
            defaultFrame.trans (AdministrativePreserved.allocate defaultMap (keyStore ++ suffix) _)
          have finalMaps : LocationMap.Extends keyMap (defaultMap ++ [(keyStore ++ suffix).length]) :=
            defaultMaps.trans ⟨_, rfl⟩
          have finalWorlds : WorldExtends keyWorld
              (defaultWorld ++ [.product .word (.product payload (.namedData identity))]) :=
            defaultWorlds.trans ⟨_, rfl⟩
          have finalMetadata := defaultMetadata.trans (Dynamic.HeapMetadataExtend.of_allocation allocates)
          let suffixPool : State headers keys ⟨scope, defaultMap ++ [(keyStore ++ suffix).length],
              defaultWorld ++ [.product .word (.product payload (.namedData identity))], _,
              keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))], canonical⟩ :=
            (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
          obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
            finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
          refine ⟨_, _, _, _, coreRun, .value (by rw [nodeType]; exact .arrayRef elementProjected identified mapped typed),
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
            heapMetadata.trans finalMetadata, effect.trans ?_, returned,
            callerProtocol.trans related returnedRelated⟩
          rw [extended]
          exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
        | newArrayLengthType notWord _ => exact (notWord trivial).elim
        | newArrayTooLong tooLong =>
          have beyond : ¬ count < Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit := by
            rw [limit_lt]; omega
          exact ⟨_, keyStore, keyMap, keyWorld,
            newArray_tooLong (layout := CompatibleExpressionArrays.arrayLayout payload identity) firstEval beyond,
            .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, maps, worlds, frame, heapMetadata, effect,
            reached, related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `new T[](n)`'s head, reflected: the length's Core run gives its Source run, and the rest is the Source's
default and allocation, or its `0x41`. -/
theorem new_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {length : ExpressionId} {lengthNode : ExpressionNode} {payload : Ty}
    {identity : DataTypeId} {default : Expr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (CompatibleExpressionArrays.arrayType payload identity))
    (form : node.form = .newArray element length)
    (lengthFound : invocation.source.lookupExpression? length = some lengthNode)
    (firstChild : children scope length first)
    (projected : compiled.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
      .ok (CompatibleExpressionArrays.arrayType payload identity))
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault compiled.compatible.checked.catalog element = some default)
    (layouts : DefaultLayouts compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (TypeSystem.Ty.array element))
    (code : lowered = ⟨CompatibleExpressionArrays.arrayType payload identity,
      SourceCoreDataExpressions.newArray (CompatibleExpressionArrays.arrayLayout payload identity) default
        first.expression⟩)
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
  obtain ⟨nodeType, allowed, lengthTypedAt⟩ := new_source_types unique found form metadata.coercions sourceTyped
  have lengthTypeEq := CellAwareArraySourceInversion.typed_type unique lengthFound lengthTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have lengthTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change length ∈ [length]; simp) lengthFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ lengthFound lengthTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.newArray element length) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  obtain ⟨elementProjected, identified⟩ := array_parts projected
  cases layouts with
  | scalar notArray => exact absurd rfl (notArray element)
  | array registeredAll elementLayouts =>
  have registered := registeredAll payload identity elementProjected identified
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (CompatibleExpressionArrays.arrayType payload identity) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.newArray
      (CompatibleExpressionArrays.arrayLayout payload identity) default first.expression).rename ξ) value finalStore
      at evaluated
    rw [newArray_rename, arrayDefault_rename defined] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.newArray at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (newArray_length_failure (layout := CompatibleExpressionArrays.arrayLayout payload identity)
            (default := default) firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨keyStore, firstRun⟩ : ∃ keyStore, EvaluationSize _ actual store _ _ keyStore := ⟨_, firstEvaluation⟩
      obtain ⟨firstSize, firstOutcome, after, keyMap, keyWorld, firstTrace, represented, keyHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstRun
      cases represented with
      | @value lengthSource coreLength lengthPayload =>
        rw [← lengthTypeEq] at lengthPayload
        obtain ⟨count, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) lengthPayload
        by_cases fits : count.val < Dynamic.newArrayLengthLimit
        · obtain ⟨zero, defaulted, sourceDefault⟩ := default_exists after allowed
          obtain ⟨defaultValue, suffix, defaultMap, defaultWorld, defaultEval, zeroRep, defaultHeaps, defaultMaps,
            defaultWorlds, defaultFrame, defaultMetadata⟩ :=
            default_preserve keyHeaps sourceDefault defined elementProjected elementLayouts (.word count :: actual)
          have represented : GenericHeap.ArrayCellRepresents model defaultMap defaultWorld
              ⟨.arrayObject element, some (.arrayObject element (List.replicate count.val zero)), none⟩
              (.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) [])))
              (.product .word (.product payload (.namedData identity))) :=
            ⟨element, List.replicate count.val zero, payload, identity, defaultValue, [], rfl,
              by simp [CellAwareArrayReads.ofNatModulo_self], rfl,
              { projection := elementProjected
                registered := registered
                bounded := by simp
                default_typed := zeroRep.runtime_hasType
                keys := fun _ _ member => by cases member
                entries_typed := fun _ _ member => by cases member
                represented := fun position below => by
                  simp only [List.getElem_replicate, GenericHeap.arrayEntry, OrderedMapping.lookupEntries,
                    Option.getD_none]
                  exact zeroRep }⟩
          have allocates := Dynamic.Heap.Allocates.append (heap := defaulted)
            (type := TypeSystem.Ty.arrayObject element) (value := some (.arrayObject element (List.replicate count.val zero)))
          obtain ⟨finalHeaps, mapped, typed⟩ := defaultHeaps.allocate_array represented allocates
          have coreRun := newArray_evaluates (layout := CompatibleExpressionArrays.arrayLayout payload identity)
            firstRun.sound ((limit_lt count).mpr fits) (by rw [arrayDefault_weaken defined]; exact defaultEval)
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
          have extended : (keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) =
              keyStore ++ (suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) := by simp
          have finalFrame : AdministrativePreserved keyMap keyStore (defaultMap ++ [(keyStore ++ suffix).length])
              (keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))]) :=
            defaultFrame.trans (AdministrativePreserved.allocate defaultMap (keyStore ++ suffix) _)
          have finalMaps : LocationMap.Extends keyMap (defaultMap ++ [(keyStore ++ suffix).length]) :=
            defaultMaps.trans ⟨_, rfl⟩
          have finalWorlds : WorldExtends keyWorld
              (defaultWorld ++ [.product .word (.product payload (.namedData identity))]) :=
            defaultWorlds.trans ⟨_, rfl⟩
          have finalMetadata := defaultMetadata.trans (Dynamic.HeapMetadataExtend.of_allocation allocates)
          let suffixPool : State headers keys ⟨scope, defaultMap ++ [(keyStore ++ suffix).length],
              defaultWorld ++ [.product .word (.product payload (.namedData identity))], _,
              keyStore ++ suffix ++ [.pair (.word count) (.pair defaultValue
                (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) []))], canonical⟩ :=
            (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
          obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
            finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
          refine ⟨_, _, _, _, _, .arrayResult occurrence rfl (.cons firstTrace .nil) (.newArray fits sourceDefault allocates),
            .value (by rw [nodeType]; exact .arrayRef elementProjected identified mapped typed),
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
            heapMetadata.trans finalMetadata, effect.trans ?_, returned,
            callerProtocol.trans related returnedRelated⟩
          rw [extended]
          exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
        · have beyond : ¬ count < Word.ofNatModulo SourceCoreDataExpressions.arrayLengthLimit := by
            rw [limit_lt]; exact fits
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
            (newArray_tooLong (layout := CompatibleExpressionArrays.arrayLayout payload identity) (default := default)
              firstRun.sound beyond)
          exact ⟨_, _, after, keyMap, keyWorld,
            .arrayResult occurrence rfl (.cons firstTrace .nil) (.newArrayTooLong (by omega)),
            .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, maps, worlds, frame, heapMetadata, effect,
            reached, related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end

section
/-! A literal's entries: each element at its own position, and the elements' values at one type. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

/-- A literal's entries hold each element at its own position. -/
theorem literal_lookup : ∀ (values : List Value) (index position : Nat), index + values.length ≤ wordModulus →
    (below : position < values.length) →
    OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word (Word.ofNatModulo (index + position)))
      (literalEntries index values) = some values[position]
  | [], _, _, _, below => absurd below (Nat.not_lt_zero _)
  | value :: rest, index, 0, _, _ => by
    simp [literalEntries, OrderedMapping.lookupEntries, GenericHeap.arrayKeyEqual]
  | value :: rest, index, position + 1, small, below => by
    simp only [List.length_cons] at small below
    have different : Word.ofNatModulo (index + (position + 1)) ≠ Word.ofNatModulo index := by
      intro same
      have values := congrArg Fin.val same
      rw [CellAwareArrayReads.ofNatModulo_val (by omega), CellAwareArrayReads.ofNatModulo_val (by omega)] at values
      omega
    have rest' := literal_lookup rest (index + 1) position (by omega) (by omega)
    rw [show index + 1 + position = index + (position + 1) by omega] at rest'
    simp only [literalEntries, OrderedMapping.lookupEntries, GenericHeap.arrayKeyEqual, Value.word.injEq, different,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.getElem_cons_succ]
    exact rest'

theorem literal_keys : ∀ (values : List Value) (index : Nat) (key value : Value),
    (key, value) ∈ literalEntries index values →
      ∃ position, position < values.length ∧ key = .word (Word.ofNatModulo (index + position))
  | [], _, _, _, member => by cases member
  | head :: rest, index, key, value, member => by
    simp only [literalEntries, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | member
    · exact ⟨0, by simp, by simp⟩
    · obtain ⟨position, below, rfl⟩ := literal_keys rest (index + 1) key value member
      exact ⟨position + 1, by simp; omega, by rw [show index + (position + 1) = index + 1 + position by omega]⟩

theorem literal_values : ∀ (values : List Value) (index : Nat) (key value : Value),
    (key, value) ∈ literalEntries index values → value ∈ values
  | [], _, _, _, member => by cases member
  | head :: rest, index, key, value, member => by
    simp only [literalEntries, List.mem_cons, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩ | member
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (literal_values rest (index + 1) key value member)

section Values
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions} {mapping : LocationMap} {world : StoreTyping}

/-- Values at one Source and one Core type: each element's representation, and each Core value's type. -/
theorem values_uniform {element : TypeSystem.Ty} {payload : Ty} {sourceTypes : List TypeSystem.Ty} {types : List Ty}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes types sources values)
    (sameSource : ∀ type ∈ sourceTypes, type = element) (sameCore : ∀ type ∈ types, type = payload) :
    sources.length = values.length ∧
      (∀ position (below : position < sources.length) (core : position < values.length),
        model.Represents mapping world element sources[position] values[position] payload) ∧
      ∀ value ∈ values, RuntimeValueHasType world value payload definitions := by
  induction represented with
  | nil => exact ⟨rfl, fun _ below => absurd below (Nat.not_lt_zero _), fun _ member => by cases member⟩
  | @cons sourceType type source value _ _ _ _ head tail ih =>
    have headSource := sameSource sourceType List.mem_cons_self
    have headCore := sameCore type List.mem_cons_self
    subst headSource headCore
    obtain ⟨lengths, rest, typed⟩ :=
      ih (fun other member => sameSource other (List.mem_cons_of_mem _ member))
        (fun other member => sameCore other (List.mem_cons_of_mem _ member))
    refine ⟨by simp [lengths], ?_, ?_⟩
    · intro position below core
      cases position with
      | zero => exact head
      | succ position => exact rest position (by simpa using below) (by simpa using core)
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact model.runtime_hasType head
      · exact typed other member

end Values

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
end

section
/-! A literal: its elements, packed as a call's arguments are, then the default and the array's cell. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds CellAwareArraySourceInversion CompatibleArrayEvaluation
open CellAwareArrayCells DataPatternValues
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

/-- A literal is of `T[]`, and its elements of `T`. -/
theorem literal_source_types {source : TypedSource} {context : SourceSemantics.Context} {id : ExpressionId}
    {element : TypeSystem.Ty} {elements : List ExpressionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .arrayLiteral element elements) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    node.type = TypeSystem.Ty.array element ∧
      ExpressionsHaveTypes source context elements (List.replicate elements.length element) := by
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
    | arrayLiteral _ elementsTyped => exact ⟨rfl, elementsTyped⟩

theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) {element : TypeSystem.Ty}
    (typed : ∀ id ∈ ids, ∀ node, source.lookupExpression? id = some node → node.type = element) :
    ∀ type ∈ types, type = element := by
  induction tree with
  | nil => intro _ member; cases member
  | single found _ =>
    intro type member
    simp only [List.mem_singleton] at member
    subst member
    exact typed _ (by simp) _ found
  | cons found _ _ ih =>
    intro type member
    rcases List.mem_cons.mp member with rfl | member
    · exact typed _ List.mem_cons_self _ found
    · exact ih (fun inner innerMember node innerFound => typed inner (List.mem_cons_of_mem _ innerMember) node innerFound)
        type member

theorem tree_length {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) : ids.length = codes.length := by
  induction tree with
  | nil => rfl
  | single => rfl
  | cons _ _ _ ih => simp [ih]

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
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {lowered : SourceCoreBasic.LoweredExpr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions faults unique selectedBodies runtime covers in
/-- A literal's head: its elements' meanings, packed as a call's arguments are, then the default element and
one fresh array of the elements on both sides. -/
theorem literal_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {elements : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {payload : Ty} {identity : DataTypeId} {default : Expr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (CompatibleExpressionArrays.arrayType payload identity))
    (form : node.form = .arrayLiteral element elements)
    (sequence : DataExpressionSequence.Tree invocation.source children scope elements sourceTypes codes)
    (codeTypes : ∀ code ∈ codes, code.type = payload) (short : elements.length < wordModulus)
    (projected : compiled.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
      .ok (CompatibleExpressionArrays.arrayType payload identity))
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault compiled.compatible.checked.catalog element = some default)
    (layouts : DefaultLayouts compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (TypeSystem.Ty.array element))
    (code : lowered = ⟨CompatibleExpressionArrays.arrayType payload identity,
      SourceCoreDataExpressions.arrayLiteral (CompatibleExpressionArrays.arrayLayout payload identity) default
        (SourceCoreCalls.packArguments codes).expression codes.length⟩)
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
  obtain ⟨nodeType, elementsTyped⟩ := literal_source_types unique found form metadata.coercions sourceTyped
  have sourceTypesEq := tree_types sequence fun element' member node' found' =>
    (CellAwareArraySourceInversion.typed_type unique found' (replicate_typed elementsTyped element' member)).symm
  have coreTypesEq : ∀ type ∈ codes.map (·.type), type = payload := by
    intro type member
    obtain ⟨code, codeMember, rfl⟩ := List.mem_map.mp member
    exact codeTypes code codeMember
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have typing : ExpressionsHaveTypes invocation.source context elements originalTypes := by
    rw [form] at operandTyped
    exact operandTyped
  obtain ⟨elementProjected, identified⟩ := array_parts projected
  cases layouts with
  | scalar notArray => exact absurd rfl (notArray element)
  | array registeredAll elementLayouts =>
  have registered := registeredAll payload identity elementProjected identified
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.arrayLiteral
        (CompatibleExpressionArrays.arrayLayout payload identity) default
        (SourceCoreCalls.packArguments codes).expression codes.length).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (CompatibleExpressionArrays.arrayType payload identity) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [arrayLiteral_rename, arrayDefault_rename defined]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, _⟩ :=
        CellAwareInvocationExpressionSequence.preserves_fault bridge size sequence unique typing childMeaning
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame failed
          (Nat.le_of_lt smaller)
      exact ⟨_, finalStore, finalMap, finalWorld, arrayLiteral_failure evaluated, .fault matched, finalHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related⟩
    | @result _ sources _ _ _ evaluated result smaller =>
      obtain ⟨coreValues, keyStore, keyMap, keyWorld, elementsEval, represented, keyHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, _⟩ :=
        CellAwareInvocationExpressionSequence.preserves_values bridge size sequence unique typing childMeaning
          environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
          (Nat.le_of_lt smaller)
      obtain ⟨lengths, elementReps, coreTyped⟩ := values_uniform represented sourceTypesEq coreTypesEq
      have codesLength : codes.length = coreValues.length := by simpa using represented.length.2
      rw [codesLength]
      cases result with
      | arrayLiteral allocates =>
        obtain ⟨defaultValue, cells, defaultWorld, defaultEval, defaultWorlds, storeTyped, defaultTyped⟩ :=
          default_runs defined elementProjected elementLayouts (packValues coreValues :: actual)
            keyHeaps.runtime_hasTypes
        have defaultHeaps := CellMappingHeap.heap_append keyHeaps defaultWorlds storeTyped
        have contents : GenericHeap.ArrayContents model keyMap defaultWorld element sources payload identity
            defaultValue (literalEntries 0 coreValues) :=
          { projection := elementProjected
            registered := registered
            bounded := by rw [lengths, ← codesLength, ← tree_length sequence]; exact short
            default_typed := defaultTyped
            keys := fun key value member => by
              obtain ⟨position, below, rfl⟩ := literal_keys coreValues 0 key value member
              exact ⟨position, by omega, by simp⟩
            entries_typed := fun key value member =>
              (coreTyped value (literal_values coreValues 0 key value member)).weaken defaultWorlds
            represented := fun position below => by
              have core : position < coreValues.length := by omega
              have entry : GenericHeap.arrayEntry (literalEntries 0 coreValues) defaultValue position =
                  coreValues[position] := by
                unfold GenericHeap.arrayEntry
                have looked := literal_lookup coreValues 0 position (by
                  have bound := short
                  rw [tree_length sequence, codesLength] at bound
                  omega) core
                simp only [Nat.zero_add] at looked
                rw [looked]
                rfl
              rw [entry]
              exact ValueRep.extend (elementReps position below core) (.refl _) (.refl _) defaultWorlds }
        have cellRep : GenericHeap.ArrayCellRepresents model keyMap defaultWorld
            ⟨.arrayObject element, some (.arrayObject element sources), none⟩
            (.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues))))
            (.product .word (.product payload (.namedData identity))) :=
          ⟨element, sources, payload, identity, defaultValue, literalEntries 0 coreValues, rfl, by rw [lengths], rfl,
            contents⟩
        obtain ⟨finalHeaps, mapped, typed⟩ := defaultHeaps.allocate_array cellRep allocates
        have coreRun := arrayLiteral_evaluates (layout := CompatibleExpressionArrays.arrayLayout payload identity)
          elementsEval (by rw [arrayDefault_weaken defined]; exact defaultEval)
        have extended : (keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
            (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) =
            keyStore ++ (cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) := by
          simp
        have finalFrame : AdministrativePreserved keyMap keyStore (keyMap ++ [(keyStore ++ cells).length])
            (keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) :=
          (CellMappingHeap.administrative_append keyMap keyStore cells).trans
            (AdministrativePreserved.allocate keyMap (keyStore ++ cells) _)
        have finalMaps : LocationMap.Extends keyMap (keyMap ++ [(keyStore ++ cells).length]) := ⟨_, rfl⟩
        have finalWorlds : WorldExtends keyWorld
            (defaultWorld ++ [.product .word (.product payload (.namedData identity))]) :=
          defaultWorlds.trans ⟨_, rfl⟩
        have finalMetadata := Dynamic.HeapMetadataExtend.of_allocation allocates
        let suffixPool : State headers keys ⟨scope, keyMap ++ [(keyStore ++ cells).length],
            defaultWorld ++ [.product .word (.product payload (.namedData identity))], _,
            keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))],
            canonical⟩ :=
          (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
        obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
          finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
        refine ⟨_, _, _, _, coreRun,
          .value (by rw [nodeType]; exact .arrayRef elementProjected identified mapped typed),
          finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
          heapMetadata.trans finalMetadata, effect.trans ?_, returned, callerProtocol.trans related returnedRelated⟩
        rw [extended]
        exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- A literal's head, reflected: the packed elements' Core run gives their Source runs, and the rest is the
Source's allocation. -/
theorem literal_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {elements : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {payload : Ty} {identity : DataTypeId} {default : Expr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (CompatibleExpressionArrays.arrayType payload identity))
    (form : node.form = .arrayLiteral element elements)
    (sequence : DataExpressionSequence.Tree invocation.source children scope elements sourceTypes codes)
    (codeTypes : ∀ code ∈ codes, code.type = payload) (short : elements.length < wordModulus)
    (projected : compiled.compatible.checked.catalog.project (TypeSystem.Ty.array element) =
      .ok (CompatibleExpressionArrays.arrayType payload identity))
    (defined : SourceCoreCompatibleDataExpressions.arrayDefault compiled.compatible.checked.catalog element = some default)
    (layouts : DefaultLayouts compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (TypeSystem.Ty.array element))
    (code : lowered = ⟨CompatibleExpressionArrays.arrayType payload identity,
      SourceCoreDataExpressions.arrayLiteral (CompatibleExpressionArrays.arrayLayout payload identity) default
        (SourceCoreCalls.packArguments codes).expression codes.length⟩)
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
  obtain ⟨nodeType, elementsTyped⟩ := literal_source_types unique found form metadata.coercions sourceTyped
  have sourceTypesEq := tree_types sequence fun element' member node' found' =>
    (CellAwareArraySourceInversion.typed_type unique found' (replicate_typed elementsTyped element' member)).symm
  have coreTypesEq : ∀ type ∈ codes.map (·.type), type = payload := by
    intro type member
    obtain ⟨code, codeMember, rfl⟩ := List.mem_map.mp member
    exact codeTypes code codeMember
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have typing : ExpressionsHaveTypes invocation.source context elements originalTypes := by
    rw [form] at operandTyped
    exact operandTyped
  obtain ⟨elementProjected, identified⟩ := array_parts projected
  cases layouts with
  | scalar notArray => exact absurd rfl (notArray element)
  | array registeredAll elementLayouts =>
  have registered := registeredAll payload identity elementProjected identified
  have occurrence : Staging.Recursive.Occurrence invocation id (.arrayLiteral element elements) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (CompatibleExpressionArrays.arrayType payload identity) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.arrayLiteral
      (CompatibleExpressionArrays.arrayLayout payload identity) default
      (SourceCoreCalls.packArguments codes).expression codes.length).rename ξ) value finalStore at evaluated
    rw [arrayLiteral_rename, arrayDefault_rename defined] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.arrayLiteral at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related, _⟩ :=
        CellAwareInvocationExpressionSequence.reflects bridge _ sequence unique typing childMeaning environments
          heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstEvaluation
          (by omega)
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (arrayLiteral_failure (layout := CompatibleExpressionArrays.arrayLayout payload identity) (default := default)
            (count := codes.length) firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl sourceTrace, .fault matched, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨keyStore, firstRun⟩ : ∃ keyStore, EvaluationSize _ actual store _ _ keyStore := ⟨_, firstEvaluation⟩
      obtain ⟨sourceSize, sourceOutcome, after, keyMap, keyWorld, sourceTrace, represented, keyHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related, _⟩ :=
        CellAwareInvocationExpressionSequence.reflects bridge _ sequence unique typing childMeaning environments
          heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame firstRun (by omega)
      cases represented with
      | @values sources coreValues represented =>
        obtain ⟨lengths, elementReps, coreTyped⟩ := values_uniform represented sourceTypesEq coreTypesEq
        have codesLength : codes.length = coreValues.length := by simpa using represented.length.2
        rw [codesLength] at complete
        have elementsEval := firstRun.sound
        have allocates := Dynamic.Heap.Allocates.append (heap := after)
          (type := TypeSystem.Ty.arrayObject element) (value := some (.arrayObject element sources))
        obtain ⟨defaultValue, cells, defaultWorld, defaultEval, defaultWorlds, storeTyped, defaultTyped⟩ :=
          default_runs defined elementProjected elementLayouts (packValues coreValues :: actual)
            keyHeaps.runtime_hasTypes
        have defaultHeaps := CellMappingHeap.heap_append keyHeaps defaultWorlds storeTyped
        have contents : GenericHeap.ArrayContents model keyMap defaultWorld element sources payload identity
            defaultValue (literalEntries 0 coreValues) :=
          { projection := elementProjected
            registered := registered
            bounded := by rw [lengths, ← codesLength, ← tree_length sequence]; exact short
            default_typed := defaultTyped
            keys := fun key value member => by
              obtain ⟨position, below, rfl⟩ := literal_keys coreValues 0 key value member
              exact ⟨position, by omega, by simp⟩
            entries_typed := fun key value member =>
              (coreTyped value (literal_values coreValues 0 key value member)).weaken defaultWorlds
            represented := fun position below => by
              have core : position < coreValues.length := by omega
              have entry : GenericHeap.arrayEntry (literalEntries 0 coreValues) defaultValue position =
                  coreValues[position] := by
                unfold GenericHeap.arrayEntry
                have looked := literal_lookup coreValues 0 position (by
                  have bound := short
                  rw [tree_length sequence, codesLength] at bound
                  omega) core
                simp only [Nat.zero_add] at looked
                rw [looked]
                rfl
              rw [entry]
              exact ValueRep.extend (elementReps position below core) (.refl _) (.refl _) defaultWorlds }
        have cellRep : GenericHeap.ArrayCellRepresents model keyMap defaultWorld
            ⟨.arrayObject element, some (.arrayObject element sources), none⟩
            (.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues))))
            (.product .word (.product payload (.namedData identity))) :=
          ⟨element, sources, payload, identity, defaultValue, literalEntries 0 coreValues, rfl, by rw [lengths], rfl,
            contents⟩
        obtain ⟨finalHeaps, mapped, typed⟩ := defaultHeaps.allocate_array cellRep allocates
        have coreRun := arrayLiteral_evaluates (layout := CompatibleExpressionArrays.arrayLayout payload identity)
          elementsEval (by rw [arrayDefault_weaken defined]; exact defaultEval)
        have extended : (keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
            (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) =
            keyStore ++ (cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) := by
          simp
        have finalFrame : AdministrativePreserved keyMap keyStore (keyMap ++ [(keyStore ++ cells).length])
            (keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))]) :=
          (CellMappingHeap.administrative_append keyMap keyStore cells).trans
            (AdministrativePreserved.allocate keyMap (keyStore ++ cells) _)
        have finalMaps : LocationMap.Extends keyMap (keyMap ++ [(keyStore ++ cells).length]) := ⟨_, rfl⟩
        have finalWorlds : WorldExtends keyWorld
            (defaultWorld ++ [.product .word (.product payload (.namedData identity))]) :=
          defaultWorlds.trans ⟨_, rfl⟩
        have finalMetadata := Dynamic.HeapMetadataExtend.of_allocation allocates
        let suffixPool : State headers keys ⟨scope, keyMap ++ [(keyStore ++ cells).length],
            defaultWorld ++ [.product .word (.product payload (.namedData identity))], _,
            keyStore ++ cells ++ [.pair (.word (Word.ofNatModulo coreValues.length)) (.pair defaultValue
              (OrderedMapping.encode (GenericHeap.arrayLayout payload identity) (literalEntries 0 coreValues)))],
            canonical⟩ :=
          (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
        obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
          finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
        refine ⟨_, _, _, _, _, .arrayResult occurrence rfl sourceTrace (.arrayLiteral allocates),
          .value (by rw [nodeType]; exact .arrayRef elementProjected identified mapped typed),
          finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
          heapMetadata.trans finalMetadata, effect.trans ?_, returned, callerProtocol.trans related returnedRelated⟩
        rw [extended]
        exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end

section
/-! The copy helper's code typed in its own environment, and a Source copy of a slice's elements as the
helper's reads, each through the slice, on a store that keeps the heap's cells. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

theorem viewShape_zero {type : Ty} {layout : OrderedMapping.Layout}
    (shaped : SourceCoreDataExpressions.viewShape? type = some (0, layout)) :
    type = .cell (.product .word (.product layout.valueType layout.type)) ∧ layout.keyType = .word := by
  induction type using SourceCoreDataExpressions.viewShape?.induct generalizing layout with
  | case1 =>
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shaped
    obtain ⟨_, rfl⟩ := shaped
    exact ⟨rfl, rfl⟩
  | case2 base ih =>
    simp only [SourceCoreDataExpressions.viewShape?] at shaped
    cases inner : SourceCoreDataExpressions.viewShape? base <;> simp [inner] at shaped
  | case3 => simp [SourceCoreDataExpressions.viewShape?] at shaped

theorem viewShape_succ {type : Ty} {depth : Nat} {layout : OrderedMapping.Layout}
    (shaped : SourceCoreDataExpressions.viewShape? type = some (depth + 1, layout)) :
    ∃ base, type = .product base (.product .word .word) ∧
      SourceCoreDataExpressions.viewShape? base = some (depth, layout) := by
  induction type using SourceCoreDataExpressions.viewShape?.induct generalizing depth layout with
  | case1 =>
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shaped
    omega
  | case2 base ih =>
    simp only [SourceCoreDataExpressions.viewShape?] at shaped
    cases inner : SourceCoreDataExpressions.viewShape? base with
    | none => simp [inner] at shaped
    | some pair =>
      obtain ⟨innerDepth, innerLayout⟩ := pair
      simp [inner] at shaped
      obtain ⟨rfl, rfl⟩ := shaped
      exact ⟨base, rfl, inner⟩
  | case3 => simp [SourceCoreDataExpressions.viewShape?] at shaped

theorem viewShape_wellFormed {definitions : DataEnvironment} {layout : OrderedMapping.Layout}
    (registered : layout.Registered definitions) :
    ∀ {depth : Nat} {type : Ty}, SourceCoreDataExpressions.viewShape? type = some (depth, layout) →
      Ty.WellFormed definitions type
  | 0, type, shaped => by
    obtain ⟨rfl, _⟩ := viewShape_zero shaped
    exact .cell (.product .word (.product registered.valueWellFormed registered.typeWellFormed))
  | depth + 1, type, shaped => by
    obtain ⟨base, rfl, inner⟩ := viewShape_succ shaped
    exact .product (viewShape_wellFormed registered inner) (.product .word .word)

section Typing
variable {definitions : DataEnvironment} {layout : OrderedMapping.Layout} {comparison : Expr}
  (registered : layout.Registered definitions)

include registered in
theorem arrayIndex_hasType {context : Core.Context} {base index : Expr}
    (comparisonTyped : HasType context comparison layout.comparisonType definitions)
    (baseTyped : HasType context base
      (LanguageResult.resultType (.cell (.product .word (.product layout.valueType layout.type)))) definitions)
    (indexTyped : HasType context index (LanguageResult.resultType .word) definitions)
    (keyType : layout.keyType = .word) :
    HasType context (SourceCoreDataExpressions.arrayIndex layout comparison base index)
      (LanguageResult.resultType layout.valueType) definitions := by
  have first : HasType (.cell (.product .word (.product layout.valueType layout.type)) :: context)
      (comparison.weakenAt 0) layout.comparisonType definitions := by
    simpa [Context.insertAt] using
      comparisonTyped.weakenAt (inserted := .cell (.product .word (.product layout.valueType layout.type))) 0
  have second : HasType (.word :: .cell (.product .word (.product layout.valueType layout.type)) :: context)
      ((comparison.weakenAt 0).weakenAt 0) layout.comparisonType definitions := by
    simpa [Context.insertAt] using first.weakenAt (inserted := .word) 0
  have indexWeak : HasType (.cell (.product .word (.product layout.valueType layout.type)) :: context)
      (index.weakenAt 0) (LanguageResult.resultType .word) definitions := by
    simpa [Context.insertAt] using
      indexTyped.weakenAt (inserted := .cell (.product .word (.product layout.valueType layout.type))) 0
  unfold SourceCoreDataExpressions.arrayIndex
  apply LanguageResult.bind_hasType registered.valueWellFormed baseTyped
  apply LanguageResult.bind_hasType registered.valueWellFormed indexWeak
  apply HasType.ifE (HasType.wordLt (.var rfl) (.first (.loadCell (.var rfl))))
  · apply LanguageResult.bind_hasType registered.valueWellFormed
      (OrderedMapping.lookup_hasType registered second (.second (.second (.loadCell (.var rfl))))
        (by rw [keyType]; exact .var rfl))
    exact .caseE (.var rfl) (LanguageResult.success_hasType (.first (.second (.loadCell (.var rfl)))))
      (LanguageResult.success_hasType (.var rfl))
  · exact LanguageResult.failure_hasType registered.valueWellFormed .word

include registered in
theorem viewRead_hasType {context : Core.Context}
    (comparisonTyped : HasType context comparison layout.comparisonType definitions) :
    ∀ (depth : Nat) {view position : Expr} {viewType : Ty},
      SourceCoreDataExpressions.viewShape? viewType = some (depth, layout) →
      HasType context view viewType definitions → HasType context position .word definitions →
      HasType context (SourceCoreDataExpressions.viewRead layout comparison depth view position)
        (LanguageResult.resultType layout.valueType) definitions
  | 0, view, position, viewType, shaped, viewTyped, positionTyped => by
    obtain ⟨rfl, keyType⟩ := viewShape_zero shaped
    exact arrayIndex_hasType registered comparisonTyped (LanguageResult.success_hasType viewTyped)
      (LanguageResult.success_hasType positionTyped) keyType
  | depth + 1, view, position, viewType, shaped, viewTyped, positionTyped => by
    obtain ⟨base, rfl, inner⟩ := viewShape_succ shaped
    unfold SourceCoreDataExpressions.viewRead
    apply HasType.ifE (HasType.wordLt positionTyped (.second (.second viewTyped)))
    · exact viewRead_hasType comparisonTyped depth inner (.first viewTyped)
        (.binary (.first (.second viewTyped)) positionTyped)
    · exact LanguageResult.failure_hasType registered.valueWellFormed .word

theorem viewLength_hasType {context : Core.Context} :
    ∀ {depth : Nat} {view : Expr} {viewType : Ty},
      SourceCoreDataExpressions.viewShape? viewType = some (depth, layout) →
      HasType context view viewType definitions →
      HasType context (SourceCoreDataExpressions.viewLength depth view) .word definitions
  | 0, view, viewType, shaped, viewTyped => by
    obtain ⟨rfl, _⟩ := viewShape_zero shaped
    exact .first (.loadCell viewTyped)
  | depth + 1, view, viewType, shaped, viewTyped => by
    obtain ⟨base, rfl, _⟩ := viewShape_succ shaped
    exact .second (.second viewTyped)

include registered in
/-- The copy helper's body is typed in its own environment: the slice and the position, and its cell. -/
theorem sliceCopyBody_hasType {depth : Nat} {sliceType : Ty} {context : Core.Context}
    (shaped : SourceCoreDataExpressions.viewShape? sliceType = some (depth, layout)) (keyType : layout.keyType = .word)
    (comparisonTyped : HasType (.product sliceType .word ::
      OptionalCell.referenceType (OrderedMapping.helperType (.product sliceType .word) layout.type) :: context)
      comparison layout.comparisonType definitions) :
    HasType (.product sliceType .word ::
        OptionalCell.referenceType (OrderedMapping.helperType (.product sliceType .word) layout.type) :: context)
      (SourceCoreDataExpressions.sliceCopyBody layout comparison depth sliceType)
      (LanguageResult.resultType layout.type) definitions := by
  have sliceWellFormed := viewShape_wellFormed registered shaped
  unfold SourceCoreDataExpressions.sliceCopyBody
  apply HasType.ifE (HasType.wordLt (.second (.var rfl)) (viewLength_hasType shaped (.first (.var rfl))))
  · apply LanguageResult.bind_hasType registered.typeWellFormed
      (viewRead_hasType registered comparisonTyped depth shaped (.first (.var rfl)) (.second (.var rfl)))
    apply LanguageResult.bind_hasType registered.typeWellFormed
      (OrderedMapping.invoke_hasType (.product sliceWellFormed .word) registered.typeWellFormed (.var rfl)
        (.pair (.first (.var rfl)) (.binary (.second (.var rfl)) .word)))
    exact LanguageResult.success_hasType
      (OrderedMapping.cons_hasType registered (by rw [keyType]; exact .second (.var rfl)) (.var rfl) (.var rfl))
  · exact LanguageResult.success_hasType (OrderedMapping.empty_hasType registered _)

end Typing

section Copies
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked} {layout : OrderedMapping.Layout}

/-- A read through a view runs the same way on a store that keeps its cells, in any environment. -/
theorem ViewReads.transport {environment environment' : Environment} {store store' : Store} {depth : Nat}
    {view : Value} {position : Word} {result : Value} {final : Store}
    (reads : CompatibleArrayEvaluation.ViewReads comparison layout environment store depth view position result final)
    (agree : ∀ location value, store.read? location = some value → store'.read? location = some value) :
    ∃ final', CompatibleArrayEvaluation.ViewReads comparison layout environment' store' depth view position result
      final' := by
  induction reads with
  | array read below wordKeys => exact ⟨_, .array (agree _ _ read) below wordKeys⟩
  | arrayOutside read beyond => exact ⟨_, .arrayOutside (agree _ _ read) beyond⟩
  | slice below _ ih =>
    obtain ⟨final', innerRead⟩ := ih
    exact ⟨final', .slice below innerRead⟩
  | sliceOutside beyond => exact ⟨_, .sliceOutside beyond⟩

/-- A read through a view only appends cells. -/
theorem ViewReads.appends {environment : Environment} {store : Store} {depth : Nat}
    {view : Value} {position : Word} {result : Value} {final : Store}
    (reads : CompatibleArrayEvaluation.ViewReads comparison layout environment store depth view position result final) :
    ∃ suffix, final = store ++ suffix := by
  induction reads with
  | @array type location length position default entries read below wordKeys =>
    obtain ⟨suffix, appended, _⟩ := CompatibleMappingComparison.helper_store_extension comparison
      (.word position :: .cellRef type location :: environment) store layout.lookupParameter layout.lookupResult
      (OrderedMapping.lookupBody layout)
      (.pair (OrderedMapping.encode layout entries) (.pair (.word position)
        (CompatibleMappingComparison.comparator comparison (.word position :: .cellRef type location :: environment)
          store)))
    exact ⟨suffix, appended⟩
  | arrayOutside => exact ⟨[], by simp⟩
  | slice _ _ ih => exact ih
  | sliceOutside => exact ⟨[], by simp⟩

theorem CopyReads.appends {depth : Nat} {sliceValue : Value} {length : Word} {self : Value}
    {captured : Environment} {position : Word} {store : Store} {entries : OrderedMapping.Entries} {final : Store}
    (copies : CompatibleArrayEvaluation.CopyReads comparison layout depth sliceValue length self captured position store
      entries final) :
    ∃ suffix, final = store ++ suffix := by
  induction copies with
  | done => exact ⟨[], by simp⟩
  | next _ reads _ ih =>
    obtain ⟨first, rfl⟩ := ViewReads.appends reads
    obtain ⟨rest, rfl⟩ := ih
    exact ⟨first ++ rest, by simp⟩

variable {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

include prepared in
/-- A Source copy of a view's elements, on its representation: the copy helper's reads from the same position,
on a store that keeps the heap's cells, to the entries of each element at its own position. -/
theorem copies_preserve {environment : Environment} {context : Core.Context}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    {view : Dynamic.Value} {position count : Nat} {values : List Dynamic.Value}
    (copies : Dynamic.ViewCopies heap view position count values) :
    ∀ {repType viewType elementType : TypeSystem.Ty} {coreView : Value} {coreType : Ty} {depth : Nat}
      {self : Value} {captured : Environment} {copyStore : Store} {length : Nat},
      ValueRep checked registry functions mapping world repType view coreView coreType →
      SourceCoreRawMetadata.runtimeType repType = SourceCoreRawMetadata.runtimeType viewType →
      ViewElement viewType elementType →
      SourceCoreDataExpressions.viewShape? coreType = some (depth, layout) →
      position + count = length → length < wordModulus →
      (∀ location value, store.read? location = some value → copyStore.read? location = some value) →
      ∃ coreValues final,
        CompatibleArrayEvaluation.CopyReads comparison layout depth coreView (Word.ofNatModulo length) self captured
          (Word.ofNatModulo position) copyStore (literalEntries position coreValues) final ∧
        coreValues.length = values.length ∧
        (∀ index (below : index < values.length) (core : index < coreValues.length),
          ValueRep checked registry functions mapping world elementType values[index] coreValues[index]
            layout.valueType) ∧
        (∃ suffix, final = copyStore ++ suffix) := by
  induction copies with
  | @nil position =>
    intro repType viewType elementType coreView coreType depth self captured copyStore length rep runtime elementOf
      shape total small agree
    refine ⟨[], copyStore, .done ?_, rfl, fun _ below => absurd below (Nat.not_lt_zero _), ⟨[], by simp⟩⟩
    intro below
    have := (CellAwareArrayReads.ofNatModulo_lt (by omega) small).mp below
    omega
  | @cons position count value values reads rest ih =>
    intro repType viewType elementType coreView coreType depth self captured copyStore length rep runtime elementOf
      shape total small agree
    obtain ⟨result, _, _, _, coreReads, elementRep, _, _, _, _⟩ :=
      CellAwareArrayReads.reads_preserve prepared heaps environmentTyped reads rep runtime elementOf shape (by omega)
    obtain ⟨middle, transported⟩ := ViewReads.transport (environment' := .pair coreView
      (.word (Word.ofNatModulo position)) :: self :: captured) coreReads agree
    obtain ⟨coreValues, final, more, lengths, restReps, appended⟩ :=
      ih rep runtime elementOf shape (by omega) small (fun location value read =>
        transported.keeps (agree location value read))
    rw [← CellAwareArrayReads.ofNatModulo_add] at more
    obtain ⟨first, rfl⟩ := ViewReads.appends transported
    obtain ⟨rest, rfl⟩ := appended
    refine ⟨result :: coreValues, _, .next ((CellAwareArrayReads.ofNatModulo_lt (by omega) small).mpr (by omega))
      transported more, by simp [lengths], ?_, ⟨first ++ rest, by simp⟩⟩
    intro index below core
    cases index with
    | zero => exact elementRep
    | succ index => exact restReps index (by simpa using below) (by simpa using core)

end Copies

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
end

section
/-! A slice within an array copies its elements on the Source side. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

theorem ViewCopies.length {heap : Dynamic.Heap} {view : Dynamic.Value} {position count : Nat}
    {values : List Dynamic.Value} (copies : Dynamic.ViewCopies heap view position count values) :
    values.length = count := by
  induction copies with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- A slice of an array within its length copies: each position below the slice's length reads the array. -/
theorem copies_exist {heap : Dynamic.Heap} {element : TypeSystem.Ty} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {elements : List Dynamic.Value} (read : Dynamic.Heap.Reads heap location cell)
    (stored : cell.value = some (.arrayObject element elements)) {start length : Nat}
    (within : start + length ≤ elements.length) :
    ∀ count position, position + count = length →
      ∃ values, Dynamic.ViewCopies heap (.arraySlice (.arrayRef element location) start length) position count values
  | 0, _, _ => ⟨[], .nil⟩
  | count + 1, position, total => by
    obtain ⟨values, rest⟩ := copies_exist read stored within count (position + 1) (by omega)
    have below : start + position < elements.length := by omega
    exact ⟨_, .cons (.slice (by omega) (.array read stored (List.getElem?_eq_getElem below))) rest⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayCells
end

section
/-! `toArray(a[s:e])`: the slice, whose bounds check gives the copy within the array, then the copy helper
and the array's cell. -/
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

/-- `toArray(s)` is of `T[]`, for a slice of a view of `T`s. -/
theorem copy_source_types {source : TypedSource} {context : SourceSemantics.Context} {id slice : ExpressionId}
    {element : TypeSystem.Ty} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node) (form : node.form = .toArray element slice)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    node.type = TypeSystem.Ty.array element ∧ ∃ baseType,
      ExpressionHasType source context slice (TypeSystem.Ty.arraySlice baseType) ∧ ViewElement baseType element := by
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
    | toArray sliceTyped view => exact ⟨rfl, _, sliceTyped, view⟩

/-- A slice the Source made is within its base: its start and length stay within the base's length. -/
theorem slice_bound {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {slice base : ExpressionId} {start stop : Option ExpressionId} {sliceNode : ExpressionNode}
    {view : Dynamic.Value} {first length : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? slice = some sliceNode)
    (form : sliceNode.form = .arraySlice base start stop)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment before slice
      (.value (.arraySlice view first length)) after) :
    ∃ count, Dynamic.ViewLength after view count ∧ first + length ≤ count := by
  cases CellAwareArraySourceInversion.children unique found form rfl trace with
  | result _ result _ =>
    cases result with
    | arraySlice counted _ ordered within => exact ⟨_, counted, by omega⟩

theorem base_runtime {sliceType baseRepType baseType : TypeSystem.Ty}
    (sliceRuntime : SourceCoreRawMetadata.runtimeType sliceType =
      SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.arraySlice baseRepType))
    (sliceTypeEq : TypeSystem.Ty.arraySlice baseType = sliceType) :
    SourceCoreRawMetadata.runtimeType baseRepType = SourceCoreRawMetadata.runtimeType baseType := by
  subst sliceTypeEq
  have same := sliceRuntime.symm
  simp only [TypeSystem.Ty.arraySlice, SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.application.injEq,
    true_and] at same
  exact same

private theorem closedTyped {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) :
    HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

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
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
  {first lowered : SourceCoreBasic.LoweredExpr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge functions faults unique selectedBodies runtime covers in
/-- `toArray(a[s:e])`'s head: the slice's meaning, then its elements' copy through the helper and one fresh
array of the slice's length on both sides. -/
theorem copy_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {slice : ExpressionId} {sliceNode : ExpressionNode} {valueType : Ty}
    {dataType : DataTypeId} {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {fuel : Nat}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.cell (.product .word (.product valueType (.namedData dataType)))))
    (form : node.form = .toArray element slice)
    (sliceFound : invocation.source.lookupExpression? slice = some sliceNode)
    (firstChild : children scope slice first)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0 + 1, ⟨.word, valueType, dataType⟩))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨.cell (.product .word (.product valueType (.namedData dataType))),
      SourceCoreDataExpressions.sliceCopy ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1) first.type
        first.expression⟩)
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
  obtain ⟨nodeType, baseType, sliceTypedAt, sliceView⟩ :=
    copy_source_types unique found form metadata.coercions sourceTyped
  have sliceTypeEq := CellAwareArraySourceInversion.typed_type unique sliceFound sliceTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have sliceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change slice ∈ [slice]; simp) sliceFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ sliceFound sliceTyped
  have projected := metadata.projected
  rw [nodeType] at projected
  obtain ⟨elementProjected, identified⟩ := array_parts (payload := valueType) (identity := dataType) projected
  obtain ⟨sliceBase, sliceTypeShape, baseShape⟩ := viewShape_succ shaped
  obtain ⟨baseEq, _⟩ := viewShape_zero baseShape
  have comparisonTyped : ∀ context : Core.Context, HasType context comparison.expression
      (OrderedMapping.Layout.comparisonType ⟨.word, valueType, dataType⟩)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
    intro context
    have closed := closedTyped (comparison.typed.extend_definitions
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).basePrefix) context
    rw [(word_comparison prepared).1] at closed
    simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.sliceCopy ⟨.word, valueType, dataType⟩
        comparison.expression (0 + 1) first.type first.expression).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.cell (.product .word (.product valueType (.namedData dataType)))) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [sliceCopy_rename, closed_rename comparison.typed]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨childSize, childSmaller, childTrace⟩ := single_fault failed
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, sliceCopy_failure firstEval, .fault matched, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | result evaluated result smaller =>
      obtain ⟨childSize, sliceSource, childSmaller, rfl, childTrace⟩ := single_values evaluated
      obtain ⟨_, keyStore, keyMap, keyWorld, firstEval, represented, keyHeaps, maps, worlds, frame, heapMetadata,
        effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | @value _ coreSlice payload =>
        cases result with
        | @toArray _ _ _ _ view start length values location copies allocates =>
          obtain ⟨baseRepType, baseValue, baseCore, rfl, coreTypeEq, baseRep, bounded, _, sliceRuntime⟩ :=
            arraySlice_fields payload rfl
          rw [sliceTypeShape] at coreTypeEq
          obtain ⟨baseCoreEq, -⟩ := Ty.product.inj coreTypeEq
          subst baseCoreEq
          subst baseEq
          cases sliceView with
          | slice innerView =>
            obtain ⟨_, _, _, rfl⟩ := slice_source baseRep (base_runtime sliceRuntime sliceTypeEq)
            obtain ⟨_, _, _, _, impossible, _⟩ := arraySlice_fields baseRep rfl
            cases impossible
          | array =>
            obtain ⟨arrayElement, arrayLocation, rfl⟩ := array_source baseRep (base_runtime sliceRuntime sliceTypeEq)
            obtain ⟨target, payloadT, identityT, rfl, cellTypeEq, mapped, typed, _⟩ := arrayRef_fields baseRep rfl
            simp only [OrderedMapping.Layout.type, Ty.cell.injEq, Ty.product.injEq, Ty.namedData.injEq,
              true_and] at cellTypeEq
            obtain ⟨samePayload, sameIdentity⟩ := cellTypeEq
            subst payloadT identityT
            obtain ⟨arrayCell, arrayValue, arraySourceRead, arrayRead, stands⟩ := keyHeaps.cells mapped
            cases stands with
            | optional optionalTyped _ =>
              have impossible := optionalTyped.symm.trans typed
              simp [Core.OptionalCell.cellType] at impossible
            | array cellTyped arrayed =>
              obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, typeEq', contents⟩ :=
                arrayed
              subst cellEq valueEq
              rw [typeEq'] at cellTyped
              have sameType := Option.some.inj (cellTyped.symm.trans typed)
              simp only [Ty.product.injEq, Ty.namedData.injEq, true_and] at sameType
              obtain ⟨samePayload', sameIdentity'⟩ := sameType
              subst payload' identity'
              have registered := contents.registered
              have sliceWellFormed := viewShape_wellFormed registered shaped
              have agree : ∀ location value, keyStore.read? location = some value →
                  (WordMapping.installedStore keyStore (.product first.type .word)
                    (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                    (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                      first.type)
                    (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero))
                    (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual)).read?
                    location = some value := by
                intro location value read
                simp only [WordMapping.installedStore, Store.read?] at read ⊢
                rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
                exact read
              obtain ⟨coreValues, final, copiesCore, lengths, elementReps, appended⟩ :=
                copies_preserve prepared keyHeaps (actualTyped.weaken worlds) copies payload
                  (viewType := TypeSystem.Ty.arraySlice (TypeSystem.Ty.array element)) (by rw [← sliceTypeEq])
                  (.slice (.array element)) shaped (Nat.zero_add _) (by omega) agree
              rw [← CellAwareArrayReads.zero_ofNatModulo] at copiesCore
              have coreRun := sliceCopy_evaluates (layout := ⟨.word, valueType, dataType⟩) prepared rfl (depth := 0)
                firstEval .array arrayRead copiesCore
              have installed : WordMapping.Installed
                  (WordMapping.installedStore keyStore (.product first.type .word)
                    (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                    (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                      first.type)
                    (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero))
                    (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual))
                  (.product first.type .word) (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                  (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                    first.type) keyStore.length
                  (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero) ::
                    .pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual) := by
                simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]
              have helperEval := runHelper_evaluates (.pair (Evaluates.var (index := 0) rfl) .word)
                (sliceCopyBody_evaluates prepared rfl copiesCore installed)
              obtain ⟨suffix, appendedEq⟩ := appended
              have helperTyped : HasType (first.type :: actualContext)
                  (OrderedMapping.runHelper (.product first.type .word)
                    (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                    (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                      first.type) (.pair (.var 0) (.word Word.zero)))
                  (LanguageResult.resultType (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩))
                  (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
                OrderedMapping.runHelper_hasType (.product sliceWellFormed .word) registered.typeWellFormed
                  (.pair (.var rfl) .word) (sliceCopyBody_hasType registered shaped rfl (comparisonTyped _))
              have finalAppended : final = keyStore ++ ([.inRight .unit (WordMapping.closure (.product first.type .word)
                  (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                  (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                    first.type) keyStore.length
                  (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero) ::
                    .pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                      (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual))] ++
                  suffix) := by
                rw [appendedEq]
                simp [WordMapping.installedStore]
              obtain ⟨futureWorld, frameWorlds, futureHeaps, _, helperFrame⟩ :=
                CellMappingHeap.evaluation_preserves_frame keyHeaps (.cons payload.runtime_hasType
                  (actualTyped.weaken worlds)) helperTyped helperEval finalAppended
              have valuesLength := ViewCopies.length copies
              have cellRep : GenericHeap.ArrayCellRepresents model keyMap futureWorld
                  ⟨.arrayObject element, some (.arrayObject element values), none⟩
                  (.pair (.word (Word.ofNatModulo length)) (.pair default
                    (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType) (literalEntries 0 coreValues))))
                  (.product .word (.product valueType (.namedData dataType))) :=
                ⟨element, values, valueType, dataType, default, literalEntries 0 coreValues, rfl,
                  by rw [valuesLength], rfl,
                  { projection := elementProjected
                    registered := registered
                    bounded := by rw [valuesLength]; omega
                    default_typed := contents.default_typed.weaken frameWorlds
                    keys := fun key value member => by
                      obtain ⟨position, below, rfl⟩ := literal_keys coreValues 0 key value member
                      exact ⟨position, by omega, by simp⟩
                    entries_typed := fun key value member => by
                      obtain ⟨index, below, rfl⟩ := List.mem_iff_getElem.mp
                        (literal_values coreValues 0 key value member)
                      exact ((elementReps index (by omega) below).runtime_hasType).weaken frameWorlds
                    represented := fun position below => by
                      have core : position < coreValues.length := by omega
                      have entry : GenericHeap.arrayEntry (literalEntries 0 coreValues) default position =
                          coreValues[position] := by
                        unfold GenericHeap.arrayEntry
                        have looked := literal_lookup coreValues 0 position (by omega) core
                        simp only [Nat.zero_add] at looked
                        rw [looked]
                        rfl
                      rw [entry]
                      exact ValueRep.extend (elementReps position below core) (.refl _) (.refl _) frameWorlds }⟩
              obtain ⟨finalHeaps, mappedNew, typedNew⟩ := futureHeaps.allocate_array cellRep allocates
              have finalFrame := helperFrame.trans (AdministrativePreserved.allocate keyMap final
                (.pair (.word (Word.ofNatModulo length)) (.pair default
                  (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType) (literalEntries 0 coreValues)))))
              have finalMaps : LocationMap.Extends keyMap (keyMap ++ [final.length]) := ⟨_, rfl⟩
              have finalWorlds : WorldExtends keyWorld
                  (futureWorld ++ [.product .word (.product valueType (.namedData dataType))]) :=
                frameWorlds.trans ⟨_, rfl⟩
              have finalMetadata := Dynamic.HeapMetadataExtend.of_allocation allocates
              let suffixPool : State headers keys ⟨scope, keyMap ++ [final.length],
                  futureWorld ++ [.product .word (.product valueType (.namedData dataType))], _,
                  (final.allocate (.pair (.word (Word.ofNatModulo length)) (.pair default
                    (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType)
                      (literalEntries 0 coreValues))))).1, canonical⟩ :=
                (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
              obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
              refine ⟨_, _, _, _, coreRun,
                .value (by rw [nodeType]; exact .arrayRef elementProjected identified mappedNew typedNew),
                finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
                heapMetadata.trans finalMetadata, effect.trans ?_, returned,
                callerProtocol.trans related returnedRelated⟩
              subst finalAppended
              rw [List.append_assoc]
              exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `toArray(a[s:e])`'s head, reflected: the slice's Core run gives its Source run, whose bounds check gives
the copy within the array, and the rest is the Source's copy and allocation. -/
theorem copy_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {element : TypeSystem.Ty} {slice : ExpressionId} {sliceNode : ExpressionNode} {valueType : Ty}
    {dataType : DataTypeId} {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {fuel : Nat}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.cell (.product .word (.product valueType (.namedData dataType)))))
    (form : node.form = .toArray element slice)
    (sliceFound : invocation.source.lookupExpression? slice = some sliceNode)
    {sliceBase : ExpressionId} {sliceStart sliceStop : Option ExpressionId}
    (sliceForm : sliceNode.form = .arraySlice sliceBase sliceStart sliceStop)
    (firstChild : children scope slice first)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (0 + 1, ⟨.word, valueType, dataType⟩))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨.cell (.product .word (.product valueType (.namedData dataType))),
      SourceCoreDataExpressions.sliceCopy ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1) first.type
        first.expression⟩)
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
  obtain ⟨nodeType, baseType, sliceTypedAt, sliceView⟩ :=
    copy_source_types unique found form metadata.coercions sourceTyped
  have sliceTypeEq := CellAwareArraySourceInversion.typed_type unique sliceFound sliceTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have sliceTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change slice ∈ [slice]; simp) sliceFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ sliceFound sliceTyped
  have projected := metadata.projected
  rw [nodeType] at projected
  obtain ⟨elementProjected, identified⟩ := array_parts (payload := valueType) (identity := dataType) projected
  obtain ⟨sliceBase, sliceTypeShape, baseShape⟩ := viewShape_succ shaped
  obtain ⟨baseEq, _⟩ := viewShape_zero baseShape
  have comparisonTyped : ∀ context : Core.Context, HasType context comparison.expression
      (OrderedMapping.Layout.comparisonType ⟨.word, valueType, dataType⟩)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
    intro context
    have closed := closedTyped (comparison.typed.extend_definitions
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).basePrefix) context
    rw [(word_comparison prepared).1] at closed
    simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
      SourceCoreDataEquality.comparatorType] using closed
  have occurrence : Staging.Recursive.Occurrence invocation id (.toArray element slice) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.cell (.product .word (.product valueType (.namedData dataType)))) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.sliceCopy ⟨.word, valueType, dataType⟩
      comparison.expression (0 + 1) first.type first.expression).rename ξ) value finalStore at evaluated
    rw [sliceCopy_rename, closed_rename comparison.typed] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.sliceCopy at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (sliceCopy_failure (layout := ⟨.word, valueType, dataType⟩) (comparison := comparison) (depth := 0 + 1)
            (sliceType := first.type) firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨keyStore, firstRun⟩ : ∃ keyStore, EvaluationSize _ actual store _ _ keyStore := ⟨_, firstEvaluation⟩
      obtain ⟨firstSize, firstOutcome, after, keyMap, keyWorld, firstTrace, represented, keyHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstRun
      have firstEval := firstRun.sound
      cases represented with
      | @value sliceSource coreSlice payload =>
        obtain ⟨view, start, length, rfl⟩ := slice_source payload (by rw [← sliceTypeEq])
        obtain ⟨count, counted, inside⟩ := slice_bound unique sliceFound sliceForm firstTrace
        obtain ⟨baseRepType, baseValue, baseCore, rfl, coreTypeEq, baseRep, bounded, _, sliceRuntime⟩ :=
          arraySlice_fields payload rfl
        rw [sliceTypeShape] at coreTypeEq
        obtain ⟨baseCoreEq, -⟩ := Ty.product.inj coreTypeEq
        subst baseCoreEq
        subst baseEq
        cases sliceView with
        | slice innerView =>
          obtain ⟨_, _, _, rfl⟩ := slice_source baseRep (base_runtime sliceRuntime sliceTypeEq)
          obtain ⟨_, _, _, _, impossible, _⟩ := arraySlice_fields baseRep rfl
          cases impossible
        | array =>
          obtain ⟨arrayElement, arrayLocation, rfl⟩ := array_source baseRep (base_runtime sliceRuntime sliceTypeEq)
          obtain ⟨target, payloadT, identityT, rfl, cellTypeEq, mapped, typed, _⟩ := arrayRef_fields baseRep rfl
          simp only [OrderedMapping.Layout.type, Ty.cell.injEq, Ty.product.injEq, Ty.namedData.injEq,
            true_and] at cellTypeEq
          obtain ⟨samePayload, sameIdentity⟩ := cellTypeEq
          subst payloadT identityT
          obtain ⟨arrayCell, arrayValue, arraySourceRead, arrayRead, stands⟩ := keyHeaps.cells mapped
          cases stands with
          | optional optionalTyped _ =>
            have impossible := optionalTyped.symm.trans typed
            simp [Core.OptionalCell.cellType] at impossible
          | array cellTyped arrayed =>
            obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, typeEq', contents⟩ :=
              arrayed
            subst cellEq valueEq
            rw [typeEq'] at cellTyped
            have sameType := Option.some.inj (cellTyped.symm.trans typed)
            simp only [Ty.product.injEq, Ty.namedData.injEq, true_and] at sameType
            obtain ⟨samePayload', sameIdentity'⟩ := sameType
            subst payload' identity'
            cases counted with
            | @array _ _ countCell countElements countRead countStored =>
            have sameCell := Dynamic.Heap.Reads.functional countRead arraySourceRead
            subst sameCell
            simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at countStored
            obtain ⟨sameElement, sameElements⟩ := countStored
            subst element' countElements
            obtain ⟨values, copies⟩ := copies_exist arraySourceRead rfl (start := start) (length := length)
              (by omega) length 0 (by omega)
            have allocates := Dynamic.Heap.Allocates.append (heap := after)
              (type := TypeSystem.Ty.arrayObject element) (value := some (.arrayObject element values))
            have registered := contents.registered
            have sliceWellFormed := viewShape_wellFormed registered shaped
            have agree : ∀ location value, keyStore.read? location = some value →
                (WordMapping.installedStore keyStore (.product first.type .word)
                  (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                  (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                    first.type)
                  (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero))
                  (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual)).read?
                  location = some value := by
              intro location value read
              simp only [WordMapping.installedStore, Store.read?] at read ⊢
              rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp read).1]
              exact read
            obtain ⟨coreValues, final, copiesCore, lengths, elementReps, appended⟩ :=
              copies_preserve prepared keyHeaps (actualTyped.weaken worlds) copies payload
                (viewType := TypeSystem.Ty.arraySlice (TypeSystem.Ty.array element)) (by rw [← sliceTypeEq])
                (.slice (.array element)) shaped (Nat.zero_add _) (by omega) agree
            rw [← CellAwareArrayReads.zero_ofNatModulo] at copiesCore
            have coreRun := sliceCopy_evaluates (layout := ⟨.word, valueType, dataType⟩) prepared rfl (depth := 0)
              firstEval .array arrayRead copiesCore
            have installed : WordMapping.Installed
                (WordMapping.installedStore keyStore (.product first.type .word)
                  (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                  (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                    first.type)
                  (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero))
                  (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual))
                (.product first.type .word) (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                  first.type) keyStore.length
                (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero) ::
                  .pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual) := by
              simp [WordMapping.Installed, WordMapping.installedStore, Store.read?]
            have helperEval := runHelper_evaluates (.pair (Evaluates.var (index := 0) rfl) .word)
              (sliceCopyBody_evaluates prepared rfl copiesCore installed)
            obtain ⟨suffix, appendedEq⟩ := appended
            have helperTyped : HasType (first.type :: actualContext)
                (OrderedMapping.runHelper (.product first.type .word)
                  (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                  (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                    first.type) (.pair (.var 0) (.word Word.zero)))
                (LanguageResult.resultType (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩))
                (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
              OrderedMapping.runHelper_hasType (.product sliceWellFormed .word) registered.typeWellFormed
                (.pair (.var rfl) .word) (sliceCopyBody_hasType registered shaped rfl (comparisonTyped _))
            have finalAppended : final = keyStore ++ ([.inRight .unit (WordMapping.closure (.product first.type .word)
                (OrderedMapping.Layout.type ⟨.word, valueType, dataType⟩)
                (SourceCoreDataExpressions.sliceCopyBody ⟨.word, valueType, dataType⟩ comparison.expression (0 + 1)
                  first.type) keyStore.length
                (.pair (.pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length)))) (.word Word.zero) ::
                  .pair (.cellRef (.product .word (.product valueType (.namedData dataType))) target)
                    (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) :: actual))] ++
                suffix) := by
              rw [appendedEq]
              simp [WordMapping.installedStore]
            obtain ⟨futureWorld, frameWorlds, futureHeaps, _, helperFrame⟩ :=
              CellMappingHeap.evaluation_preserves_frame keyHeaps (.cons payload.runtime_hasType
                (actualTyped.weaken worlds)) helperTyped helperEval finalAppended
            have valuesLength := ViewCopies.length copies
            have cellRep : GenericHeap.ArrayCellRepresents model keyMap futureWorld
                ⟨.arrayObject element, some (.arrayObject element values), none⟩
                (.pair (.word (Word.ofNatModulo length)) (.pair default
                  (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType) (literalEntries 0 coreValues))))
                (.product .word (.product valueType (.namedData dataType))) :=
              ⟨element, values, valueType, dataType, default, literalEntries 0 coreValues, rfl,
                by rw [valuesLength], rfl,
                { projection := elementProjected
                  registered := registered
                  bounded := by rw [valuesLength]; omega
                  default_typed := contents.default_typed.weaken frameWorlds
                  keys := fun key value member => by
                    obtain ⟨position, below, rfl⟩ := literal_keys coreValues 0 key value member
                    exact ⟨position, by omega, by simp⟩
                  entries_typed := fun key value member => by
                    obtain ⟨index, below, rfl⟩ := List.mem_iff_getElem.mp
                      (literal_values coreValues 0 key value member)
                    exact ((elementReps index (by omega) below).runtime_hasType).weaken frameWorlds
                  represented := fun position below => by
                    have core : position < coreValues.length := by omega
                    have entry : GenericHeap.arrayEntry (literalEntries 0 coreValues) default position =
                        coreValues[position] := by
                      unfold GenericHeap.arrayEntry
                      have looked := literal_lookup coreValues 0 position (by omega) core
                      simp only [Nat.zero_add] at looked
                      rw [looked]
                      rfl
                    rw [entry]
                    exact ValueRep.extend (elementReps position below core) (.refl _) (.refl _) frameWorlds }⟩
            obtain ⟨finalHeaps, mappedNew, typedNew⟩ := futureHeaps.allocate_array cellRep allocates
            have finalFrame := helperFrame.trans (AdministrativePreserved.allocate keyMap final
              (.pair (.word (Word.ofNatModulo length)) (.pair default
                (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType) (literalEntries 0 coreValues)))))
            have finalMaps : LocationMap.Extends keyMap (keyMap ++ [final.length]) := ⟨_, rfl⟩
            have finalWorlds : WorldExtends keyWorld
                (futureWorld ++ [.product .word (.product valueType (.namedData dataType))]) :=
              frameWorlds.trans ⟨_, rfl⟩
            have finalMetadata := Dynamic.HeapMetadataExtend.of_allocation allocates
            let suffixPool : State headers keys ⟨scope, keyMap ++ [final.length],
                futureWorld ++ [.product .word (.product valueType (.namedData dataType))], _,
                (final.allocate (.pair (.word (Word.ofNatModulo length)) (.pair default
                  (OrderedMapping.encode (GenericHeap.arrayLayout valueType dataType)
                    (literalEntries 0 coreValues))))).1, canonical⟩ :=
              (bridge.pool reached).extend finalMaps finalWorlds finalFrame finalMetadata
            obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
              finalMaps finalWorlds finalFrame finalMetadata (Relates.of_records_eq rfl)
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
            refine ⟨_, _, _, _, _, .arrayResult occurrence rfl (.cons firstTrace .nil) (.toArray copies allocates),
              .value (by rw [nodeType]; exact .arrayRef elementProjected identified mappedNew typedNew),
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame,
              heapMetadata.trans finalMetadata, effect.trans ?_, returned,
              callerProtocol.trans related returnedRelated⟩
            subst finalAppended
            rw [List.append_assoc]
            exact CellAwareScopeAuthority.Effect.append _ _ finalMetadata finalMaps finalWorlds
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end
