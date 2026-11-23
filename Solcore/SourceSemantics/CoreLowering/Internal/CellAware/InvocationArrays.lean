import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ArrayEvaluation

/-!
# Cell-aware invocations: memory arrays

The heads of the memory array forms in one actual body invocation: each form's staged trace, its
children's meanings and its Core run (`CompatibleArrayEvaluation`), with the arrays' cells in the whole-cell
heap relation. Main declarations: `CellAwareInvocationArrayBounds.length_preserves` and
`length_reflects`.
-/

section
/-! A reference to an array object is its Core cell's reference, and a slice its base's representation with
its start and length; a staged array form runs its children in its order, then its step. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend SourceInference GeneralHeap

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

/-- A reference to an array object is a reference to its Core cell, which the map and the world give. -/
theorem arrayRef_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {element : TypeSystem.Ty} {location : Dynamic.Location}, source = .arrayRef element location →
      ∃ target payload identity,
        value = .cellRef (.product .word (.product payload (.namedData identity))) target ∧
        type = .cell (.product .word (.product payload (.namedData identity))) ∧
        mapping[location.index]? = some target ∧
        world[target]? = some (.product .word (.product payload (.namedData identity))) := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arrayRef _ _ mapped typed =>
    intro _ _ same
    cases same
    exact ⟨_, _, _, rfl, rfl, mapped, typed⟩
  | compatible _ _ ih => intro _ _ same; exact ih same
  | function related =>
    intro _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue | arraySlice =>
    intro _ _ impossible
    cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- A slice is its base's representation with the words of its start and its length. -/
theorem arraySlice_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {base : Dynamic.Value} {start length : Nat}, source = .arraySlice base start length →
      ∃ baseType baseValue baseCore,
        value = .pair baseValue (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) ∧
        type = .product baseCore (.product .word .word) ∧
        ValueRep checked registry functions mapping world baseType base baseValue baseCore ∧
        start + length < wordModulus ∧ ViewCarrier baseCore := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arraySlice baseRep bounded baseView _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, rfl, rfl, baseRep, bounded, baseView⟩
  | compatible _ _ ih => intro _ _ _ same; exact ih same
  | function related =>
    intro _ _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue | arrayRef =>
    intro _ _ _ impossible
    cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- A value at an array type is a reference to an array object. -/
theorem array_source {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {element : TypeSystem.Ty},
      SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) →
      ∃ element' location, source = .arrayRef element' location := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arrayRef => intro _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
    intro element view
    have arrayed : checked.catalog.project (TypeSystem.Ty.array element) = .ok (.namedData tag.owner) := by
      rw [← checked.catalog.project_runtimeType, ← view, checked.catalog.project_runtimeType]
      exact projected
    simp only [TypeSystem.Ty.array, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreRawMetadata.runtimeType]
      at arrayed
    cases elementProjected : checked.catalog.project element <;>
      simp [elementProjected, bind, Except.bind] at arrayed
    split at arrayed <;> simp [pure, Except.pure, throw, throwThe] at arrayed
  | unit | bool | word | integer | fixed | product | function | proxy | mappingValue | arraySlice =>
    intro _ view
    simp [TypeSystem.Ty.array, TypeSystem.Ty.arraySlice, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word,
      TypeSystem.Ty.integer, TypeSystem.Ty.fixed, SourceCoreRawMetadata.runtimeType] at view
  | nil | cons | empty | entry | absent | present => trivial

/-- A value at a slice type is a slice. -/
theorem slice_source {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {base : TypeSystem.Ty},
      SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.arraySlice base) →
      ∃ inner start length, source = .arraySlice inner start length := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arraySlice => intro _ _; exact ⟨_, _, _, rfl⟩
  | compatible same _ ih => intro _ view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
    intro base view
    have sliced : checked.catalog.project (TypeSystem.Ty.arraySlice base) = .ok (.namedData tag.owner) := by
      rw [← checked.catalog.project_runtimeType, ← view, checked.catalog.project_runtimeType]
      exact projected
    simp only [TypeSystem.Ty.arraySlice, SourceCoreCompatibleCatalog.Catalog.project, SourceCoreRawMetadata.runtimeType]
      at sliced
    cases baseProjected : checked.catalog.project base <;>
      simp [baseProjected, bind, Except.bind, pure, Except.pure] at sliced
  | unit | bool | word | integer | fixed | product | function | proxy | mappingValue | arrayRef =>
    intro _ view
    simp [TypeSystem.Ty.array, TypeSystem.Ty.arraySlice, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word,
      TypeSystem.Ty.integer, TypeSystem.Ty.fixed, SourceCoreRawMetadata.runtimeType] at view
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArraySourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

/-- An array form's staged trace: its children fault first, in its order, or they evaluate and its step
follows, each with a smaller grade. -/
inductive Children (program : Program) (registry : Registry) (size : Nat) (invocation : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (form : ExpressionForm) (children : List ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | fault {childrenSize : Nat} {failure : Failure} {after : Dynamic.Heap}
      (failed : Size.Expressions program registry childrenSize invocation context environment before children
        (.fault failure) after)
      (smaller : childrenSize < size) :
      Children program registry size invocation context environment before form children (.fault failure) after
  | result {childrenSize : Nat} {values : List Dynamic.Value} {middle after : Dynamic.Heap} {outcome : Outcome}
      (evaluated : Size.Expressions program registry childrenSize invocation context environment before children
        (.values values) middle)
      (result : ArrayOutcome form values middle outcome after) (smaller : childrenSize < size) :
      Children program registry size invocation context environment before form children outcome after

theorem children {form : ExpressionForm} {ids : List ExpressionId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (formed : node.form = form) (array : arrayChildren form = some ids)
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    Children program registry size invocation context environment before form ids outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = form :=
    fun occurrence => (occurrence_form unique found occurrence).trans formed
  have notArray : ∀ {other : ExpressionForm}, arrayChildren other = none → other = form → False := by
    intro other none same
    subst same
    rw [none] at array
    cases array
  cases trace with
  | arrayFault occurrence shape failed =>
    cases actual occurrence
    rw [array] at shape
    cases shape
    exact .fault failed (Size.child_lt_stepSize (by simp))
  | arrayResult occurrence shape evaluated result =>
    cases actual occurrence
    rw [array] at shape
    cases shape
    exact .result evaluated result (Size.child_lt_stepSize (by simp))
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact (notArray rfl (actualForm.symm.trans formed)).elim
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
    rw [same, formed] at shape
    rcases shape with atomic | ⟨_, _, _, impossible⟩
    · cases form <;> cases atomic <;> simp [arrayChildren] at array
    · subst impossible; simp [arrayChildren] at array
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    rw [same, formed] at atomic
    cases form <;> cases atomic <;> simp [arrayChildren] at array
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _ | constructorMetadataFault occurrence _
  | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _
  | directApplied occurrence _ _ _ _ _
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleValue occurrence _ _ | tupleFault occurrence _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _
  | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _
  | unaryInvalid occurrence _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _
  | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _ | conditional occurrence _ _
  | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _
  | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ =>
    exact (notArray rfl (actual occurrence)).elim

/-- A typing judgment of an occurrence is at its node's own type. -/
theorem typed_type {context : Context} {child : ExpressionId} {childNode : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (childFound : invocation.source.lookupExpression? child = some childNode)
    (typed : ExpressionHasType invocation.source context child type) : type = childNode.type := by
  cases typed with
  | @intro _ _ actualNode _ _ contains _ _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans childFound)
    rw [same]

/-- One child's list: it faults, or it evaluates. -/
theorem single_fault {childrenSize : Nat} {child : ExpressionId} {failure : Failure} {after : Dynamic.Heap}
    (failed : Size.Expressions program registry childrenSize invocation context environment before [child]
      (.fault failure) after) :
    ∃ childSize, childSize < childrenSize ∧
      Size.Expression program registry childSize invocation context environment before child (.fault failure) after := by
  cases failed with
  | headFault head => exact ⟨_, Size.child_lt_stepSize (by simp), head⟩
  | tailFault _ tail => cases tail

theorem single_values {childrenSize : Nat} {child : ExpressionId} {values : List Dynamic.Value}
    {after : Dynamic.Heap}
    (evaluated : Size.Expressions program registry childrenSize invocation context environment before [child]
      (.values values) after) :
    ∃ childSize value, childSize < childrenSize ∧ values = [value] ∧
      Size.Expression program registry childSize invocation context environment before child (.value value) after := by
  cases evaluated with
  | cons head tail =>
    cases tail
    exact ⟨_, _, Size.child_lt_stepSize (by simp), rfl, head⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareArraySourceInversion
end

section
/-! The length of an array or of a slice: the base's run, then the first component of its array's cell,
which the whole-cell heap relation gives, or the slice's own length. Neither heap changes after the base. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds CellAwareArraySourceInversion CompatibleArrayEvaluation
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

/-- A length is a `uint256`, of a view. -/
theorem length_source_types {source : TypedSource} {context : SourceSemantics.Context} {id base : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .arrayLength base) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    node.type = .fixed .uint256 ∧
      ∃ baseType element, ExpressionHasType source context base baseType ∧ ViewElement baseType element := by
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
    | arrayLength baseTyped view => exact ⟨rfl, _, _, baseTyped, view⟩

theorem uint256_canonical (value : Word) : TypeSystem.FixedInteger.uint256.canonical value.val = true := by
  have bound : value.val < 2 ^ 256 := value.isLt
  simp [TypeSystem.FixedInteger.canonical, TypeSystem.FixedInteger.uint256, TypeSystem.IntegerWidth.bits, bound]

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
/-- A length's head: the base's meaning, then its array's cell's first component or the slice's length. -/
theorem length_preserves {children : GenericExpressionMeaning.Certificate}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node .word)
    (form : node.form = .arrayLength base) (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (firstChild : children scope base first)
    (code : (∃ rest, first.type = .cell (.product .word rest) ∧
        lowered = ⟨.word, SourceCoreDataExpressions.arrayLength first.expression⟩) ∨
      (∃ view, first.type = .product view (.product .word .word) ∧
        lowered = ⟨.word, SourceCoreDataExpressions.sliceLength first.expression⟩))
    (size : Nat)
    (childMeaning : PreservesBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    PreservesAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ outcome after environments heaps locals agrees actualTyped initial admitted authority
    physical owner ownerFrame trace
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'
  cases Option.some.inj (found.symm.trans metadata.found)
  have nodeType := (length_source_types unique found form metadata.coercions sourceTyped).1
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base]; simp) baseFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨childSize, childSmaller, childTrace⟩ := single_fault failed
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame, heapMetadata,
        effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps, maps, worlds, frame, heapMetadata,
          effect, reached, related⟩
        rcases code with ⟨rest, _, rfl⟩ | ⟨view, _, rfl⟩
        · rw [arrayLength_rename]; exact arrayLength_failure firstEval
        · rw [sliceLength_rename]; exact sliceLength_failure firstEval
    | result evaluated result smaller =>
      obtain ⟨childSize, value, childSmaller, rfl, childTrace⟩ := single_values evaluated
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame, heapMetadata,
        effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | value payload =>
        cases result with
        | @arrayLength _ _ _ count counted =>
          refine ⟨.inRight .word (.word (Word.ofNatModulo count)), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
            maps, worlds, frame, heapMetadata, effect, reached, related⟩
          rotate_left
          · have loweredType : lowered.type = .word := by
              rcases code with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
            rw [nodeType, loweredType]
            exact .value (.fixed _ (uint256_canonical _))
          cases counted with
          | @array element location cell elements read stored =>
            obtain ⟨target, payloadType, identity, rfl, typeEq, mapped, typed⟩ := arrayRef_fields payload rfl
            rcases code with ⟨rest, _, rfl⟩ | ⟨view, viewType, _⟩
            · obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := finalHeaps.cells mapped
              have sameCell := Dynamic.Heap.Reads.functional read sourceRead
              subst actualCell
              cases stands with
              | optional optionalTyped _ =>
                have impossible := optionalTyped.symm.trans typed
                simp [Core.OptionalCell.cellType] at impossible
              | array _ arrayed =>
                obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, _, _⟩ := arrayed
                subst cellEq
                simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at stored
                obtain ⟨rfl, rfl⟩ := stored
                subst valueEq
                rw [arrayLength_rename]
                exact arrayLength_evaluates firstEval coreRead
            · rw [typeEq] at viewType
              cases viewType
          | @slice baseValue start length =>
            obtain ⟨baseType, baseCore, baseCoreType, rfl, typeEq, _, _, _⟩ := arraySlice_fields payload rfl
            rcases code with ⟨rest, restType, _⟩ | ⟨view, _, rfl⟩
            · rw [typeEq] at restType
              cases restType
            · rw [sliceLength_rename]
              exact sliceLength_evaluates firstEval
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩


include bridge functions faults unique selectedBodies runtime covers in
/-- A length's head, reflected: the base's Core run gives its Source run, and the cell's first component
is the array's length. -/
theorem length_reflects {children : GenericExpressionMeaning.Certificate}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node .word)
    (form : node.form = .arrayLength base) (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (firstChild : children scope base first)
    (code : (∃ rest, first.type = .cell (.product .word rest) ∧
        lowered = ⟨.word, SourceCoreDataExpressions.arrayLength first.expression⟩) ∨
      (∃ view, first.type = .product view (.product .word .word) ∧
        lowered = ⟨.word, SourceCoreDataExpressions.sliceLength first.expression⟩))
    (size : Nat)
    (childMeaning : ReflectsBelow (attachment := attachment) bridge context model index registry invocation
      children faults size) :
    ReflectsAt (attachment := attachment) bridge context model index registry invocation (Point scope id lowered)
      faults size := by
  intro current child code' point root found sourceTyped mapping world administrative environment canonical actual
    actualContext before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted
    authority physical owner ownerFrame evaluated
  obtain ⟨sameScope, sameId, sameCode⟩ := point
  subst current; subst child; subst code'
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨nodeType, baseType, element, baseTypedAt, view⟩ :=
    length_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base]; simp) baseFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arrayLength base) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have loweredType : lowered.type = .word := by rcases code with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [loweredType, nodeType]
    rcases code with ⟨rest, restType, rfl⟩ | ⟨viewCore, viewType, rfl⟩
    · change EvaluationSize size actual store ((SourceCoreDataExpressions.arrayLength first.expression).rename ξ)
        value finalStore at evaluated
      rw [arrayLength_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft firstEvaluation branch =>
        obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
          frame, heapMetadata, effect, reached, related, _post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (arrayLength_failure firstEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight firstEvaluation branch =>
        obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, maps,
          worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | @value baseSource coreValue payload =>
          cases view with
          | array element =>
            rw [← baseTypeEq] at payload
            obtain ⟨element', location, rfl⟩ := array_source payload rfl
            obtain ⟨target, payloadType, identity, rfl, _, mapped, typed⟩ := arrayRef_fields payload rfl
            obtain ⟨cell, cellValue, sourceRead, coreRead, stands⟩ := middleHeaps.cells mapped
            cases stands with
            | optional optionalTyped _ =>
              have impossible := optionalTyped.symm.trans typed
              simp [Core.OptionalCell.cellType] at impossible
            | array _ arrayed =>
              obtain ⟨element'', elements, payload', identity', default, entries, cellEq, valueEq, _, _⟩ := arrayed
              subst cellEq
              subst valueEq
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                (arrayLength_evaluates firstEvaluation.sound coreRead)
              have sourceTypedValue := post.at_value.1
              rcases sourceTypedValue.arrayRef_inv with ⟨_, typedCell, typedRead, cellType⟩ | ⟨_, impossible, _⟩
              · have sameCell := Dynamic.Heap.Reads.functional sourceRead typedRead
                subst sameCell
                simp only [TypeSystem.Ty.arrayObject, TypeSystem.Ty.application.injEq, true_and] at cellType
                subst cellType
                exact ⟨_, _, middle, middleMap, middleWorld,
                  .arrayResult occurrence rfl (.cons firstTrace .nil) (.arrayLength (.array sourceRead rfl)),
                  .value (.fixed _ (uint256_canonical _)), middleHeaps, maps, worlds, frame, heapMetadata, effect,
                  reached, related⟩
              · rw [← baseTypeEq] at impossible
                simp [TypeSystem.Ty.array] at impossible
          | slice inner =>
            rw [← baseTypeEq] at payload
            obtain ⟨inner', start, length, rfl⟩ := slice_source payload rfl
            obtain ⟨_, _, baseCore, _, typeEq, _⟩ := arraySlice_fields payload rfl
            rw [typeEq] at restType
            cases restType
    · change EvaluationSize size actual store ((SourceCoreDataExpressions.sliceLength first.expression).rename ξ)
        value finalStore at evaluated
      rw [sliceLength_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft firstEvaluation branch =>
        obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
          frame, heapMetadata, effect, reached, related, _post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (sliceLength_failure firstEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
      | caseRight firstEvaluation branch =>
        obtain ⟨firstSize, firstOutcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps, maps,
          worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
          firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
            ownerFrame firstEvaluation
        cases represented with
        | @value baseSource coreValue payload =>
          cases view with
          | array element =>
            rw [← baseTypeEq] at payload
            obtain ⟨element', location, rfl⟩ := array_source payload rfl
            obtain ⟨_, _, _, _, typeEq, _⟩ := arrayRef_fields payload rfl
            rw [typeEq] at viewType
            cases viewType
          | slice inner =>
            rw [← baseTypeEq] at payload
            obtain ⟨inner', start, length, rfl⟩ := slice_source payload rfl
            obtain ⟨_, _, baseCore, rfl, _, _⟩ := arraySlice_fields payload rfl
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (sliceLength_evaluates firstEvaluation.sound)
            exact ⟨_, _, middle, middleMap, middleWorld,
              .arrayResult occurrence rfl (.cons firstTrace .nil) (.arrayLength .slice),
              .value (.fixed _ (uint256_canonical _)), middleHeaps, maps, worlds, frame, heapMetadata, effect,
              reached, related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end
