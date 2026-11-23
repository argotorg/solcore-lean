import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationArrays

/-!
# Cell-aware invocations: memory arrays' allocations

The heads of the array forms that allocate a fresh array on both sides, with the array's cell in the
whole-cell heap relation, its Core layout registered (`DefaultLayouts`), and the default element: zero, or
one fresh empty array, the Core default's last cell after the Core-only cells of its own element's default
(`CellAwareArrayCells.default_preserve`). Main declarations: `CellAwareInvocationArrayBounds.new_preserves`
and `new_reflects`.
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
