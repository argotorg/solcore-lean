import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.InvocationExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ArrayEvaluation

/-!
# Cell-aware invocations: memory arrays

The heads of the memory array forms in one actual body invocation: each form's staged trace, its
children's meanings and its Core run (`CompatibleArrayEvaluation`), with the arrays' cells in the whole-cell
heap relation. Main declarations: `CellAwareInvocationArrayBounds.length_preserves`, `index_preserves`
and, for the four shapes of a slice's bounds, `slice_range_preserves` to `slice_whole_preserves`, each with its
`reflects`.
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

/-- A reference to an array object is a reference to its Core cell, which the map and the world give, at a
type of an array of its element's runtime type. -/
theorem arrayRef_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {element : TypeSystem.Ty} {location : Dynamic.Location}, source = .arrayRef element location →
      ∃ target payload identity,
        value = .cellRef (.product .word (.product payload (.namedData identity))) target ∧
        type = .cell (.product .word (.product payload (.namedData identity))) ∧
        mapping[location.index]? = some target ∧
        world[target]? = some (.product .word (.product payload (.namedData identity))) ∧
        SourceCoreRawMetadata.runtimeType sourceType =
          SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.array element) := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arrayRef _ _ mapped typed =>
    intro _ _ same
    cases same
    exact ⟨_, _, _, rfl, rfl, mapped, typed, rfl⟩
  | compatible same _ ih =>
    intro _ _ sameSource
    obtain ⟨target, payload, identity, valueEq, typeEq, mapped, typed, view⟩ := ih sameSource
    exact ⟨target, payload, identity, valueEq, typeEq, mapped, typed, same.trans view⟩
  | function related =>
    intro _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | unit | bool | word | integer | fixed | product | proxy | constructed | mappingValue | arraySlice =>
    intro _ _ impossible
    cases impossible
  | nil | cons | empty | entry | absent | present => trivial

/-- A slice is its base's representation with the words of its start and its length, at a type of a slice of
its base's runtime type. -/
theorem arraySlice_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {base : Dynamic.Value} {start length : Nat}, source = .arraySlice base start length →
      ∃ baseType baseValue baseCore,
        value = .pair baseValue (.pair (.word (Word.ofNatModulo start)) (.word (Word.ofNatModulo length))) ∧
        type = .product baseCore (.product .word .word) ∧
        ValueRep checked registry functions mapping world baseType base baseValue baseCore ∧
        start + length < wordModulus ∧ ViewCarrier baseCore ∧
        SourceCoreRawMetadata.runtimeType sourceType =
          SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.arraySlice baseType) := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | arraySlice baseRep bounded baseView _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, rfl, rfl, baseRep, bounded, baseView, rfl⟩
  | compatible same _ ih =>
    intro _ _ _ sameSource
    obtain ⟨baseType, baseValue, baseCore, valueEq, typeEq, baseRep, bounded, baseView, view⟩ := ih sameSource
    exact ⟨baseType, baseValue, baseCore, valueEq, typeEq, baseRep, bounded, baseView, same.trans view⟩
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

/-- An array index's value is a word, at Core type `word`. -/
theorem index_word_fields {indexType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (kind : ArrayIndexType indexType)
    (related : ValueRep checked registry functions mapping world indexType source value type) :
    ∃ word, source = .word word ∧ value = .word word ∧ type = .word := by
  have view : SourceCoreRawMetadata.runtimeType indexType = .word ∨
      ∃ fixed, SourceCoreRawMetadata.runtimeType indexType = .fixed fixed := by
    cases kind with
    | word => exact .inl rfl
    | fixed type => exact .inr ⟨type, rfl⟩
  clear kind
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | word word => intro _; exact ⟨word, rfl, rfl, rfl⟩
  | @fixed actual word _ => intro _; exact ⟨word, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; rw [same] at view; exact ih view
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
    intro view
    have scalar : checked.catalog.project metadata.resultType = .ok .word := by
      rcases view with view | ⟨fixed, view⟩
      · rw [← checked.catalog.project_runtimeType, view]; rfl
      · rw [← checked.catalog.project_runtimeType, view]; rfl
    cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | integer | product | function | proxy | mappingValue | arrayRef | arraySlice =>
    intro view
    rcases view with view | ⟨_, view⟩ <;> cases view
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

/-- Two children's list: the first faults, or it evaluates and the second faults. -/
theorem pair_fault {childrenSize : Nat} {first second : ExpressionId} {failure : Failure}
    (failed : Size.Expressions program registry childrenSize invocation context environment before [first, second]
      (.fault failure) after) :
    (∃ firstSize, firstSize < childrenSize ∧
      Size.Expression program registry firstSize invocation context environment before first (.fault failure) after) ∨
    ∃ firstSize secondSize value middle, firstSize < childrenSize ∧ secondSize < childrenSize ∧
      Size.Expression program registry firstSize invocation context environment before first (.value value) middle ∧
      Size.Expression program registry secondSize invocation context environment middle second (.fault failure) after := by
  cases failed with
  | headFault head => exact .inl ⟨_, Size.child_lt_stepSize (by simp), head⟩
  | tailFault head tail =>
    cases tail with
    | headFault second =>
      refine .inr ⟨_, _, _, _, Size.child_lt_stepSize (by simp), ?_, head, second⟩
      exact Nat.lt_trans (Size.child_lt_stepSize (List.Mem.head [])) (Size.child_lt_stepSize (by simp))
    | tailFault _ rest => cases rest

/-- Two children's list: both evaluate, in order. -/
theorem pair_values {childrenSize : Nat} {first second : ExpressionId} {values : List Dynamic.Value}
    (evaluated : Size.Expressions program registry childrenSize invocation context environment before [first, second]
      (.values values) after) :
    ∃ firstSize secondSize firstValue secondValue middle, firstSize < childrenSize ∧ secondSize < childrenSize ∧
      values = [firstValue, secondValue] ∧
      Size.Expression program registry firstSize invocation context environment before first (.value firstValue) middle ∧
      Size.Expression program registry secondSize invocation context environment middle second (.value secondValue)
        after := by
  cases evaluated with
  | cons head tail =>
    cases tail with
    | cons second rest =>
      cases rest
      refine ⟨_, _, _, _, _, Size.child_lt_stepSize (by simp), ?_, rfl, head, second⟩
      exact Nat.lt_trans (Size.child_lt_stepSize (List.Mem.head [Size.stepSize []])) (Size.child_lt_stepSize (by simp))

private theorem lt_tail {child tail head : Nat} (inner : child < tail) : child < Size.stepSize [head, tail] :=
  Nat.lt_trans inner (Size.child_lt_stepSize (by simp))

/-- Three children's list: the first faults, or it evaluates and the second faults, or both evaluate and the
third faults. -/
theorem triple_fault {childrenSize : Nat} {first second third : ExpressionId} {failure : Failure}
    (failed : Size.Expressions program registry childrenSize invocation context environment before
      [first, second, third] (.fault failure) after) :
    (∃ firstSize, firstSize < childrenSize ∧
      Size.Expression program registry firstSize invocation context environment before first (.fault failure) after) ∨
    (∃ firstSize secondSize value middle, firstSize < childrenSize ∧ secondSize < childrenSize ∧
      Size.Expression program registry firstSize invocation context environment before first (.value value) middle ∧
      Size.Expression program registry secondSize invocation context environment middle second (.fault failure)
        after) ∨
    ∃ firstSize secondSize thirdSize firstValue secondValue firstHeap secondHeap,
      firstSize < childrenSize ∧ secondSize < childrenSize ∧ thirdSize < childrenSize ∧
      Size.Expression program registry firstSize invocation context environment before first (.value firstValue)
        firstHeap ∧
      Size.Expression program registry secondSize invocation context environment firstHeap second
        (.value secondValue) secondHeap ∧
      Size.Expression program registry thirdSize invocation context environment secondHeap third (.fault failure)
        after := by
  cases failed with
  | headFault head => exact .inl ⟨_, Size.child_lt_stepSize (by simp), head⟩
  | tailFault head tail =>
    cases tail with
    | headFault second =>
      exact .inr (.inl ⟨_, _, _, _, Size.child_lt_stepSize (by simp),
        lt_tail (Size.child_lt_stepSize (List.Mem.head [])), head, second⟩)
    | tailFault second rest =>
      cases rest with
      | headFault third =>
        exact .inr (.inr ⟨_, _, _, _, _, _, _, Size.child_lt_stepSize (by simp),
          lt_tail (Size.child_lt_stepSize (by simp)), lt_tail (lt_tail (Size.child_lt_stepSize (List.Mem.head []))),
          head, second, third⟩)
      | tailFault _ last => cases last

/-- Three children's list: all evaluate, in order. -/
theorem triple_values {childrenSize : Nat} {first second third : ExpressionId} {values : List Dynamic.Value}
    (evaluated : Size.Expressions program registry childrenSize invocation context environment before
      [first, second, third] (.values values) after) :
    ∃ firstSize secondSize thirdSize firstValue secondValue thirdValue firstHeap secondHeap,
      firstSize < childrenSize ∧ secondSize < childrenSize ∧ thirdSize < childrenSize ∧
      values = [firstValue, secondValue, thirdValue] ∧
      Size.Expression program registry firstSize invocation context environment before first (.value firstValue)
        firstHeap ∧
      Size.Expression program registry secondSize invocation context environment firstHeap second
        (.value secondValue) secondHeap ∧
      Size.Expression program registry thirdSize invocation context environment secondHeap third
        (.value thirdValue) after := by
  cases evaluated with
  | cons head tail =>
    cases tail with
    | cons second rest =>
      cases rest with
      | cons third last =>
        cases last
        exact ⟨_, _, _, _, _, _, _, _, Size.child_lt_stepSize (by simp), lt_tail (Size.child_lt_stepSize (by simp)),
          lt_tail (lt_tail (Size.child_lt_stepSize (List.Mem.head [Size.stepSize []]))), rfl, head, second, third⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareArraySourceInversion
end

section
/-! A read through a view on Core values runs as its Source read does: through each slice to the array's
cell, whose entry or default at the position represents the Source element, or `0x32` at a position the view
has no element at. The read appends only its lookup's cells. A view's length is its Source length's word, and a
slice's bounds check is the Source's on the words of its bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleArrayEvaluation

theorem ofNatModulo_val {value : Nat} (small : value < wordModulus) : (Word.ofNatModulo value).val = value :=
  Nat.mod_eq_of_lt small

theorem ofNatModulo_self (word : Word) : Word.ofNatModulo word.val = word :=
  Fin.ext (Nat.mod_eq_of_lt word.isLt)

theorem ofNatModulo_lt {left right : Nat} (leftSmall : left < wordModulus) (rightSmall : right < wordModulus) :
    Word.ofNatModulo left < Word.ofNatModulo right ↔ left < right := by
  rw [Fin.lt_def, ofNatModulo_val leftSmall, ofNatModulo_val rightSmall]

theorem ofNatModulo_add (left right : Nat) :
    (Word.ofNatModulo left).add (Word.ofNatModulo right) = Word.ofNatModulo (left + right) := by
  apply Fin.ext
  simp only [Word.add, Word.ofNatModulo, Fin.val_add]
  exact (Nat.add_mod _ _ _).symm

theorem viewShape_keyType {type : Ty} {depth : Nat} {layout : OrderedMapping.Layout}
    (shaped : SourceCoreDataExpressions.viewShape? type = some (depth, layout)) : layout.keyType = .word := by
  induction type using SourceCoreDataExpressions.viewShape?.induct generalizing depth layout with
  | case1 =>
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shaped
    obtain ⟨_, rfl⟩ := shaped
    rfl
  | case2 base ih =>
    simp only [SourceCoreDataExpressions.viewShape?] at shaped
    cases inner : SourceCoreDataExpressions.viewShape? base with
    | none => simp [inner] at shaped
    | some pair =>
      obtain ⟨innerDepth, innerLayout⟩ := pair
      simp [inner] at shaped
      obtain ⟨_, rfl⟩ := shaped
      exact ih inner
  | case3 =>
    simp [SourceCoreDataExpressions.viewShape?] at shaped

private theorem closed_hasType {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (context : Core.Context) :
    HasType context expression type definitions := by
  have extended := typed.rename (mapping := Renaming.id) (target := context) (by intro index type found; cases found)
  simpa using extended

/-- The environment a read through `depth` slices runs in: the head's for an array, else the view's and the
index's words in front of it, as `viewIndex` binds them. -/
def readEnvironment : Nat → Word → Value → Environment → Environment
  | 0, _, _, environment => environment
  | _ + 1, position, view, environment => .word position :: view :: environment

theorem readEnvironment_typed {world : StoreTyping} {environment : Environment} {context : Core.Context}
    {definitions : DataEnvironment} {view : Value} {viewType : Ty}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (viewTyped : RuntimeValueHasType world view viewType definitions) (depth : Nat) (position : Word) :
    ∃ readContext, RuntimeEnvironmentHasTypes world (readEnvironment depth position view environment) readContext
      definitions := by
  cases depth with
  | zero => exact ⟨context, typed⟩
  | succ _ => exact ⟨.word :: viewType :: context, .cons .word (.cons viewTyped typed)⟩

section Reads
variable {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat}
  {comparison : SourceCoreCompatibleDataEquality.Prepared checked} {layout : OrderedMapping.Layout}
  (prepared : SourceCoreCompatibleDataEquality.prepare fuel checked (.constructor (.builtin .word)) = .ok comparison)

include prepared in
/-- An array's entry lookup, as `arrayIndex` runs it below the length. -/
theorem lookup_evaluates (keyType : layout.keyType = .word) {environment : Environment} {store : Store}
    {type : Ty} {location : Location} {length position : Word} {default : Value} {entries : OrderedMapping.Entries}
    (read : store.read? location = some (.pair (.word length) (.pair default (OrderedMapping.encode layout entries))))
    (wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word) :
    Evaluates (.word position :: .cellRef type location :: environment) store
      (OrderedMapping.lookup layout comparison.expression (.second (.second (.loadCell (.var 1)))) (.var 0))
      (.inRight .word (OrderedMapping.optionValue layout.valueType
        (OrderedMapping.lookupEntries GenericHeap.arrayKeyEqual (.word position) entries)))
      (CompatibleMappingComparison.lookupStore comparison layout
        (.word position :: .cellRef type location :: environment) store entries (.word position)) :=
  OrderedMapping.lookup_evaluates entries (.word position)
    (CompatibleMappingComparison.comparator comparison (.word position :: .cellRef type location :: environment) store)
    GenericHeap.arrayKeyEqual (.second (.second (.loadCell (.var rfl) read))) (.var rfl)
    (CompatibleEquality.prepared_evaluates_exact comparison _ store)
    (word_comparisons prepared keyType _ store wordKeys position _)

include prepared in
/-- `a[i]` on a view inside `depth` slices, from the view's and the index's runs and the read in the
environment that `viewIndex` binds. -/
theorem viewIndex_reads (keyType : layout.keyType = .word) {environment : Environment} {before middle after : Store}
    {depth : Nat} {base index : Expr} {viewValue : Value} {position : Word} {result : Value} {final : Store}
    (evaluated : Evaluates environment before base (.inRight .word viewValue) middle)
    (indexed : Evaluates (viewValue :: environment) middle (index.weakenAt 0) (.inRight .word (.word position)) after)
    (reads : ViewReads comparison layout (readEnvironment depth position viewValue environment) after depth viewValue
      position result final) :
    Evaluates environment before
      (SourceCoreDataExpressions.viewIndex layout comparison.expression depth base index) result final := by
  cases depth with
  | zero =>
    cases reads with
    | array read below wordKeys => exact arrayIndex_evaluates prepared keyType evaluated indexed read below wordKeys
    | arrayOutside read beyond => exact arrayIndex_outOfBounds evaluated indexed read beyond
  | succ depth => exact viewIndex_evaluates prepared keyType evaluated indexed reads

variable {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

include prepared in
/-- A Source read through a view, on its representation: the Core read through as many slices, at an
element that represents the Source's in the world it starts from; it appends only the lookup's cells. -/
theorem reads_preserve {environment : Environment} {context : Core.Context}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    {view : Dynamic.Value} {position : Nat} {element : Dynamic.Value}
    (reads : Dynamic.ViewReads heap view position element) :
    ∀ {repType viewType elementType : TypeSystem.Ty} {coreView : Value} {coreType : Ty} {depth : Nat},
      ValueRep checked registry functions mapping world repType view coreView coreType →
      SourceCoreRawMetadata.runtimeType repType = SourceCoreRawMetadata.runtimeType viewType →
      ViewElement viewType elementType →
      SourceCoreDataExpressions.viewShape? coreType = some (depth, layout) →
      position < wordModulus →
      ∃ result final futureWorld suffix,
        ViewReads comparison layout environment store depth coreView (Word.ofNatModulo position)
          (.inRight .word result) final ∧
        ValueRep checked registry functions mapping world elementType element result layout.valueType ∧
        GenericHeap.CellHeapRepresents cells mapping futureWorld heap final ∧
        WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping final ∧
        final = store ++ suffix := by
  induction reads with
  | @array arrayElement location cell elements position value read stored elementAt =>
    intro repType viewType elementType coreView coreType depth rep runtime elementOf shape small
    obtain ⟨target, payload, identity, rfl, rfl, mapped, typed, arrayView⟩ := arrayRef_fields rep rfl
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shape
    obtain ⟨rfl, rfl⟩ := shape
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
      simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at stored
      obtain ⟨sameElement, sameElements⟩ := stored
      subst element' elements'
      subst valueEq
      rw [typeEq] at cellTyped
      have sameType := Option.some.inj (cellTyped.symm.trans typed)
      simp only [Ty.product.injEq, Ty.namedData.injEq, true_and] at sameType
      obtain ⟨samePayload, sameIdentity⟩ := sameType
      subst payload' identity'
      obtain ⟨below, elementEq⟩ := List.getElem?_eq_some_iff.mp elementAt
      have wordBelow : Word.ofNatModulo position < Word.ofNatModulo elements.length :=
        (ofNatModulo_lt small contents.bounded).mpr below
      have wordKeys : ∀ key value, (key, value) ∈ entries → ∃ word, key = .word word := by
        intro key value member
        obtain ⟨_, _, same⟩ := contents.keys key value member
        exact ⟨_, same⟩
      have evaluated := lookup_evaluates prepared (layout := ⟨.word, payload, identity⟩) rfl
        (environment := environment) (type := .product .word (.product payload (.namedData identity)))
        (position := Word.ofNatModulo position) coreRead wordKeys
      have comparisonTyped : HasType (.word :: .cell (.product .word (.product payload (.namedData identity))) :: context)
          comparison.expression (OrderedMapping.Layout.comparisonType ⟨.word, payload, identity⟩) ambient.definitions := by
        have closed := closed_hasType (comparison.typed.extend_definitions ambient.basePrefix)
          (.word :: .cell (.product .word (.product payload (.namedData identity))) :: context)
        rw [(word_comparison prepared).1] at closed
        simpa only [Core.OrderedMapping.Layout.comparisonType, SourceCoreCompatibleDataEquality.comparatorType,
          SourceCoreDataEquality.comparatorType] using closed
      have lookupTyped : HasType (.word :: .cell (.product .word (.product payload (.namedData identity))) :: context)
          (OrderedMapping.lookup ⟨.word, payload, identity⟩ comparison.expression
            (.second (.second (.loadCell (.var 1)))) (.var 0))
          (LanguageResult.resultType (OrderedMapping.Layout.lookupResult ⟨.word, payload, identity⟩))
          ambient.definitions :=
        OrderedMapping.lookup_hasType contents.registered comparisonTyped
          (.second (.second (.loadCell (.var rfl)))) (.var rfl)
      have lookupEnvironment : RuntimeEnvironmentHasTypes world
          (.word (Word.ofNatModulo position) ::
            .cellRef (.product .word (.product payload (.namedData identity))) target :: environment)
          (.word :: .cell (.product .word (.product payload (.namedData identity))) :: context) ambient.definitions :=
        .cons .word (.cons (.cellRef typed) environmentTyped)
      obtain ⟨suffix, appended, _⟩ := CompatibleMappingComparison.helper_store_extension comparison
        (.word (Word.ofNatModulo position) ::
          .cellRef (.product .word (.product payload (.namedData identity))) target :: environment) store
        (OrderedMapping.Layout.lookupParameter ⟨.word, payload, identity⟩)
        (OrderedMapping.Layout.lookupResult ⟨.word, payload, identity⟩)
        (OrderedMapping.lookupBody ⟨.word, payload, identity⟩)
        (.pair (OrderedMapping.encode ⟨.word, payload, identity⟩ entries)
          (.pair (.word (Word.ofNatModulo position)) (CompatibleMappingComparison.comparator comparison
            (.word (Word.ofNatModulo position) ::
              .cellRef (.product .word (.product payload (.namedData identity))) target :: environment) store)))
      obtain ⟨futureWorld, worlds, futureHeaps, _, unchanged⟩ :=
        CellMappingHeap.evaluation_preserves_frame heaps lookupEnvironment lookupTyped evaluated appended
      have elementRep := contents.represented position below
      rw [elementEq] at elementRep
      cases elementOf with
      | array staticElement =>
        have sameRuntime : SourceCoreRawMetadata.runtimeType elementType =
            SourceCoreRawMetadata.runtimeType arrayElement := by
          have same := runtime.symm.trans arrayView
          simpa [TypeSystem.Ty.array, SourceCoreRawMetadata.runtimeType] using same
        exact ⟨_, _, futureWorld, suffix, .array coreRead wordBelow wordKeys,
          ValueRep.compatible sameRuntime elementRep, futureHeaps, worlds,
          unchanged, appended⟩
      | slice _ =>
        have impossible := runtime.symm.trans arrayView
        simp [TypeSystem.Ty.array, TypeSystem.Ty.arraySlice, SourceCoreRawMetadata.runtimeType] at impossible
  | @slice base start length position value within inner ih =>
    intro repType viewType elementType coreView coreType depth rep runtime elementOf shape small
    obtain ⟨baseType, baseValue, baseCore, rfl, rfl, baseRep, bounded, _, sliceView⟩ := arraySlice_fields rep rfl
    cases elementOf with
    | array _ =>
      have impossible := runtime.symm.trans sliceView
      simp [TypeSystem.Ty.array, TypeSystem.Ty.arraySlice, SourceCoreRawMetadata.runtimeType] at impossible
    | @slice innerType _ innerElement =>
      have baseRuntime : SourceCoreRawMetadata.runtimeType baseType = SourceCoreRawMetadata.runtimeType innerType := by
        have same := sliceView.symm.trans runtime
        simpa [TypeSystem.Ty.arraySlice, SourceCoreRawMetadata.runtimeType] using same
      cases depth with
      | zero =>
        cases innerShape : SourceCoreDataExpressions.viewShape? baseCore <;>
          simp [SourceCoreDataExpressions.viewShape?, innerShape] at shape
      | succ depth =>
        have innerShape : SourceCoreDataExpressions.viewShape? baseCore = some (depth, layout) := by
          cases innerEq : SourceCoreDataExpressions.viewShape? baseCore with
          | none => simp [SourceCoreDataExpressions.viewShape?, innerEq] at shape
          | some pair =>
            obtain ⟨innerDepth, innerLayout⟩ := pair
            simp [SourceCoreDataExpressions.viewShape?, innerEq] at shape
            obtain ⟨rfl, rfl⟩ := shape
            rfl
        obtain ⟨result, final, futureWorld, suffix, innerRead, elementRep, futureHeaps, worlds, unchanged, appended⟩ :=
          ih baseRep baseRuntime innerElement innerShape (by omega)
        refine ⟨result, final, futureWorld, suffix, .slice ((ofNatModulo_lt small (by omega)).mpr within) ?_,
          elementRep, futureHeaps, worlds, unchanged, appended⟩
        rw [ofNatModulo_add]
        exact innerRead

/-- A position a view has no element at, on its representation: the Core read panics with `0x32`, and
keeps the store. -/
theorem outside_preserve {environment : Environment}
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {view : Dynamic.Value} {position : Nat}
    (outside : Dynamic.ViewOutOfBounds heap view position) :
    ∀ {repType : TypeSystem.Ty} {coreView : Value} {coreType : Ty} {depth : Nat},
      ValueRep checked registry functions mapping world repType view coreView coreType →
      SourceCoreDataExpressions.viewShape? coreType = some (depth, layout) →
      position < wordModulus →
      ViewReads comparison layout environment store depth coreView (Word.ofNatModulo position)
        (.inLeft layout.valueType (.word outOfBounds)) store := by
  induction outside with
  | @array arrayElement location cell elements position read stored beyond =>
    intro repType coreView coreType depth rep shape small
    obtain ⟨target, payload, identity, rfl, rfl, mapped, typed, _⟩ := arrayRef_fields rep rfl
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shape
    obtain ⟨rfl, rfl⟩ := shape
    obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
    have sameCell := Dynamic.Heap.Reads.functional read sourceRead
    subst sameCell
    cases stands with
    | optional optionalTyped _ =>
      have impossible := optionalTyped.symm.trans typed
      simp [Core.OptionalCell.cellType] at impossible
    | array _ arrayed =>
      obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, _, contents⟩ := arrayed
      subst cellEq
      simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at stored
      obtain ⟨sameElement, sameElements⟩ := stored
      subst element' elements'
      subst valueEq
      exact .arrayOutside coreRead fun below => by
        have := (ofNatModulo_lt small contents.bounded).mp below
        omega
  | @slice base start length position beyond =>
    intro repType coreView coreType depth rep shape small
    obtain ⟨baseType, baseValue, baseCore, rfl, rfl, _, bounded, _, _⟩ := arraySlice_fields rep rfl
    cases depth with
    | zero =>
      cases innerShape : SourceCoreDataExpressions.viewShape? baseCore <;>
        simp [SourceCoreDataExpressions.viewShape?, innerShape] at shape
    | succ depth =>
      exact .sliceOutside fun below => by
        have := (ofNatModulo_lt small (by omega)).mp below
        omega
  | @inner base start length position within inner ih =>
    intro repType coreView coreType depth rep shape small
    obtain ⟨baseType, baseValue, baseCore, rfl, rfl, baseRep, bounded, _, _⟩ := arraySlice_fields rep rfl
    cases depth with
    | zero =>
      cases innerShape : SourceCoreDataExpressions.viewShape? baseCore <;>
        simp [SourceCoreDataExpressions.viewShape?, innerShape] at shape
    | succ depth =>
      have innerShape : SourceCoreDataExpressions.viewShape? baseCore = some (depth, layout) := by
        cases innerEq : SourceCoreDataExpressions.viewShape? baseCore with
        | none => simp [SourceCoreDataExpressions.viewShape?, innerEq] at shape
        | some pair =>
          obtain ⟨innerDepth, innerLayout⟩ := pair
          simp [SourceCoreDataExpressions.viewShape?, innerEq] at shape
          obtain ⟨rfl, rfl⟩ := shape
          rfl
      have innerRead := ih baseRep innerShape (by omega)
      refine .slice ((ofNatModulo_lt small (by omega)).mpr within) ?_
      rw [ofNatModulo_add]
      exact innerRead

/-- A view the heap types reads at a position, or has no element there. -/
theorem reads_cases (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {sourceContext : SourceSemantics.Context} {viewType elementType : TypeSystem.Ty}
    (elementOf : ViewElement viewType elementType) :
    ∀ {repType : TypeSystem.Ty} {view : Dynamic.Value} {coreView : Value} {coreType : Ty},
      ValueRep checked registry functions mapping world repType view coreView coreType →
      SourceCoreRawMetadata.runtimeType repType = SourceCoreRawMetadata.runtimeType viewType →
      Dynamic.ValueHasType sourceContext heap view viewType →
      ∀ position, (∃ element, Dynamic.ViewReads heap view position element) ∨
        Dynamic.ViewOutOfBounds heap view position := by
  induction elementOf with
  | array element =>
    intro repType view coreView coreType rep runtime typed position
    obtain ⟨element', location, rfl⟩ := array_source rep runtime
    obtain ⟨target, payload, identity, rfl, rfl, mapped, typedTarget, _⟩ := arrayRef_fields rep rfl
    rcases typed.arrayRef_inv with ⟨_, cell, read, cellType⟩ | ⟨_, impossible, _⟩
    · obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
      have sameCell := Dynamic.Heap.Reads.functional read sourceRead
      subst sameCell
      cases stands with
      | optional optionalTyped _ =>
        have impossible := optionalTyped.symm.trans typedTarget
        simp [Core.OptionalCell.cellType] at impossible
      | array _ arrayed =>
        obtain ⟨element'', elements, _, _, _, _, cellEq, _, _, _⟩ := arrayed
        subst cellEq
        simp only [TypeSystem.Ty.arrayObject, TypeSystem.Ty.application.injEq, true_and] at cellType
        subst cellType
        cases found : elements[position]? with
        | some value => exact .inl ⟨value, .array read rfl found⟩
        | none => exact .inr (.array read rfl (List.getElem?_eq_none_iff.mp found))
    · simp [TypeSystem.Ty.array] at impossible
  | @slice innerType element inner ih =>
    intro repType view coreView coreType rep runtime typed position
    obtain ⟨base, start, length, rfl⟩ := slice_source rep runtime
    obtain ⟨baseType, baseValue, baseCore, rfl, rfl, baseRep, _, _, sliceView⟩ := arraySlice_fields rep rfl
    rcases typed.arraySlice_inv with ⟨typedBase, sameType, baseTyped, _⟩ | ⟨_, impossible, _⟩
    · simp only [TypeSystem.Ty.arraySlice, TypeSystem.Ty.application.injEq, true_and] at sameType
      subst sameType
      have baseRuntime : SourceCoreRawMetadata.runtimeType baseType = SourceCoreRawMetadata.runtimeType innerType := by
        have same := sliceView.symm.trans runtime
        simpa [TypeSystem.Ty.arraySlice, SourceCoreRawMetadata.runtimeType] using same
      by_cases within : position < length
      · rcases ih baseRep baseRuntime baseTyped (start + position) with ⟨value, reads⟩ | outside
        · exact .inl ⟨value, .slice within reads⟩
        · exact .inr (.inner within outside)
      · exact .inr (.slice (by omega))
    · simp [TypeSystem.Ty.arraySlice] at impossible

end Reads

theorem ofNatModulo_sub {first last : Nat} (ordered : first ≤ last) (small : last < wordModulus) :
    (Word.ofNatModulo last).sub (Word.ofNatModulo first) = Word.ofNatModulo (last - first) := by
  have firstSmall : first < wordModulus := by omega
  apply Fin.ext
  have le : Word.ofNatModulo first ≤ Word.ofNatModulo last := by
    rw [Fin.le_def, ofNatModulo_val firstSmall, ofNatModulo_val small]
    exact ordered
  rw [Word.sub, Fin.sub_val_of_le le, ofNatModulo_val small, ofNatModulo_val firstSmall,
    ofNatModulo_val (by omega)]

theorem zero_ofNatModulo : Word.zero = Word.ofNatModulo 0 := rfl

/-- The bounds check of a slice inside its base: the base, the start and the length. -/
theorem sliced_within {sliceType : Ty} {view : Value} {first last count : Nat}
    (lastSmall : last < wordModulus) (countSmall : count < wordModulus) (ordered : first ≤ last)
    (within : last ≤ count) :
    sliced sliceType view (Word.ofNatModulo first) (Word.ofNatModulo last) (Word.ofNatModulo count) =
      .inRight .word (.pair view (.pair (.word (Word.ofNatModulo first)) (.word (Word.ofNatModulo (last - first))))) := by
  have firstSmall : first < wordModulus := by omega
  have notAbove : ¬ Word.ofNatModulo first > Word.ofNatModulo last := by
    intro above
    have := (ofNatModulo_lt lastSmall firstSmall).mp above
    omega
  have notBeyond : ¬ Word.ofNatModulo last > Word.ofNatModulo count := by
    intro above
    have := (ofNatModulo_lt countSmall lastSmall).mp above
    omega
  unfold sliced
  rw [if_pos ⟨notAbove, notBeyond⟩, ofNatModulo_sub ordered lastSmall]

/-- A slice that is not inside its base panics with `0x32`. -/
theorem sliced_outside {sliceType : Ty} {view : Value} {first last count : Nat}
    (firstSmall : first < wordModulus) (lastSmall : last < wordModulus) (countSmall : count < wordModulus)
    (outside : last < first ∨ count < last) :
    sliced sliceType view (Word.ofNatModulo first) (Word.ofNatModulo last) (Word.ofNatModulo count) =
      .inLeft sliceType (.word outOfBounds) := by
  have bad : ¬ (¬ Word.ofNatModulo first > Word.ofNatModulo last ∧
      ¬ Word.ofNatModulo last > Word.ofNatModulo count) := by
    rintro ⟨notAbove, notBeyond⟩
    rcases outside with below | beyond
    · exact notAbove ((ofNatModulo_lt lastSmall firstSmall).mpr below)
    · exact notBeyond ((ofNatModulo_lt countSmall lastSmall).mpr beyond)
  unfold sliced
  rw [if_neg bad]

theorem viewShape_carrier {type : Ty} {depth : Nat} {layout : OrderedMapping.Layout}
    (shaped : SourceCoreDataExpressions.viewShape? type = some (depth, layout)) : ViewCarrier type := by
  induction type using SourceCoreDataExpressions.viewShape?.induct generalizing depth layout with
  | case1 => exact .cell _
  | case2 base ih =>
    simp only [SourceCoreDataExpressions.viewShape?] at shaped
    cases inner : SourceCoreDataExpressions.viewShape? base with
    | none => simp [inner] at shaped
    | some pair =>
      obtain ⟨innerDepth, innerLayout⟩ := pair
      exact .slice (ih inner)
  | case3 => simp [SourceCoreDataExpressions.viewShape?] at shaped

theorem allowed_cases {type : TypeSystem.Ty} (allowed : type.arraySliceBaseAllowed = true) :
    (∃ element, type = TypeSystem.Ty.array element) ∨ ∃ base, type = TypeSystem.Ty.arraySlice base := by
  unfold TypeSystem.Ty.arraySliceBaseAllowed at allowed
  split at allowed
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, rfl⟩
  · cases allowed

section Lengths
variable {checked : SourceCoreCompatibleCatalog.Checked} {layout : OrderedMapping.Layout}
  {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel checked registry functions) instances

/-- A view's Source length, on its representation: the Core length, within a word. -/
theorem length_preserve (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {view : Dynamic.Value} {count : Nat} (counted : Dynamic.ViewLength heap view count)
    {repType : TypeSystem.Ty} {coreView : Value} {coreType : Ty} {depth : Nat}
    (rep : ValueRep checked registry functions mapping world repType view coreView coreType)
    (shape : SourceCoreDataExpressions.viewShape? coreType = some (depth, layout)) :
    CompatibleArrayEvaluation.ViewLength store depth coreView (Word.ofNatModulo count) ∧ count < wordModulus := by
  cases counted with
  | @array arrayElement location cell elements read stored =>
    obtain ⟨target, payload, identity, rfl, rfl, mapped, typed, _⟩ := arrayRef_fields rep rfl
    simp only [SourceCoreDataExpressions.viewShape?, Option.some.injEq, Prod.mk.injEq] at shape
    obtain ⟨rfl, rfl⟩ := shape
    obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
    have sameCell := Dynamic.Heap.Reads.functional read sourceRead
    subst sameCell
    cases stands with
    | optional optionalTyped _ =>
      have impossible := optionalTyped.symm.trans typed
      simp [Core.OptionalCell.cellType] at impossible
    | array _ arrayed =>
      obtain ⟨element', elements', payload', identity', default, entries, cellEq, valueEq, _, contents⟩ := arrayed
      subst cellEq
      simp only [Option.some.injEq, Dynamic.Value.arrayObject.injEq] at stored
      obtain ⟨sameElement, sameElements⟩ := stored
      subst element' elements'
      subst valueEq
      exact ⟨.array coreRead, contents.bounded⟩
  | @slice base start length =>
    obtain ⟨baseType, baseValue, baseCore, rfl, rfl, _, bounded, _, _⟩ := arraySlice_fields rep rfl
    cases depth with
    | zero =>
      cases innerShape : SourceCoreDataExpressions.viewShape? baseCore <;>
        simp [SourceCoreDataExpressions.viewShape?, innerShape] at shape
    | succ depth => exact ⟨.slice, by omega⟩

/-- A view the heap types at a type a slice may be taken of has a length. -/
theorem length_cases (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    {sourceContext : SourceSemantics.Context} {viewType repType : TypeSystem.Ty} {view : Dynamic.Value}
    {coreView : Value} {coreType : Ty} (allowed : viewType.arraySliceBaseAllowed = true)
    (rep : ValueRep checked registry functions mapping world repType view coreView coreType)
    (runtime : SourceCoreRawMetadata.runtimeType repType = SourceCoreRawMetadata.runtimeType viewType)
    (typed : Dynamic.ValueHasType sourceContext heap view viewType) :
    ∃ count, Dynamic.ViewLength heap view count := by
  rcases allowed_cases allowed with ⟨element, rfl⟩ | ⟨base, rfl⟩
  · obtain ⟨element', location, rfl⟩ := array_source rep runtime
    obtain ⟨target, payload, identity, rfl, rfl, mapped, typedTarget, _⟩ := arrayRef_fields rep rfl
    rcases typed.arrayRef_inv with ⟨_, cell, read, cellType⟩ | ⟨_, impossible, _⟩
    · obtain ⟨actualCell, coreValue, sourceRead, coreRead, stands⟩ := heaps.cells mapped
      have sameCell := Dynamic.Heap.Reads.functional read sourceRead
      subst sameCell
      cases stands with
      | optional optionalTyped _ =>
        have impossible := optionalTyped.symm.trans typedTarget
        simp [Core.OptionalCell.cellType] at impossible
      | array _ arrayed =>
        obtain ⟨element'', elements, _, _, _, _, cellEq, _, _, _⟩ := arrayed
        subst cellEq
        simp only [TypeSystem.Ty.arrayObject, TypeSystem.Ty.application.injEq, true_and] at cellType
        subst cellType
        exact ⟨_, .array read rfl⟩
    · simp [TypeSystem.Ty.array] at impossible
  · obtain ⟨inner, start, length, rfl⟩ := slice_source rep runtime
    exact ⟨_, .slice⟩

end Lengths

end Solcore.SourceSemantics.CoreLowering.CellAwareArrayReads
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
open GenericExpressionMeaning (agree_prefix rename_prefix)
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

/-- A read has its view's element type, and takes an index of `word` or one of the twelve types. -/
theorem index_source_types {source : TypedSource} {context : SourceSemantics.Context} {id base subscript : ExpressionId}
    {node : ExpressionNode} (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .arrayIndex base subscript) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ baseType subscriptType, ExpressionHasType source context base baseType ∧ ViewElement baseType node.type ∧
      ExpressionHasType source context subscript subscriptType ∧ ArrayIndexType subscriptType := by
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
    | arrayIndex baseTyped view subscriptTyped kind =>
      exact ⟨_, _, baseTyped, view, subscriptTyped, kind⟩

theorem viewIndex_split (layout : OrderedMapping.Layout) (comparison : Expr) (depth : Nat) (base subscript : Expr) :
    ∃ tail, SourceCoreDataExpressions.viewIndex layout comparison depth base subscript =
      LanguageResult.bind layout.valueType base (LanguageResult.bind layout.valueType (subscript.weakenAt 0) tail) := by
  cases depth with
  | zero => exact ⟨_, rfl⟩
  | succ depth => exact ⟨_, rfl⟩

/-- A slice is of its base's type, a type a slice may be taken of, and its present bounds are `uint256`s. -/
theorem slice_source_types {source : TypedSource} {context : SourceSemantics.Context} {id base : ExpressionId}
    {start stop : Option ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node) (form : node.form = .arraySlice base start stop)
    (coercions : node.coercions = []) (typed : ExpressionHasType source context id node.type) :
    ∃ baseType, node.type = TypeSystem.Ty.arraySlice baseType ∧ baseType.arraySliceBaseAllowed = true ∧
      ExpressionHasType source context base baseType ∧
      ExpressionsHaveTypes source context (start.toList ++ stop.toList)
        (List.replicate (start.toList ++ stop.toList).length (.fixed .uint256)) := by
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
    | arraySlice allowed baseTyped boundsTyped => exact ⟨_, rfl, allowed, baseTyped, boundsTyped⟩

theorem replicate_typed {source : TypedSource} {context : SourceSemantics.Context} {ids : List ExpressionId}
    {type : TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids (List.replicate ids.length type)) :
    ∀ id ∈ ids, ExpressionHasType source context id type := by
  induction ids with
  | nil => intro _ member; cases member
  | cons head rest ih =>
    cases typed with
    | cons headTyped restTyped =>
      intro id member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact headTyped
      · exact ih restTyped id inRest

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
            obtain ⟨target, payloadType, identity, rfl, typeEq, mapped, typed, _⟩ := arrayRef_fields payload rfl
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
            obtain ⟨target, payloadType, identity, rfl, _, mapped, typed, _⟩ := arrayRef_fields payload rfl
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


include bridge functions faults unique selectedBodies runtime covers in
/-- A read's head: the view's and the index's meanings, then the read through the view's slices, the
array's entry or default at the position, or `0x32`. -/
theorem index_preserves [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {subscript : ExpressionId} {subscriptNode : ExpressionNode} {depth fuel : Nat} {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .arrayIndex base subscript) (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType,
      SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression second.expression⟩)
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
  obtain ⟨baseType, subscriptType, baseTypedAt, view, subscriptTypedAt, kind⟩ :=
    index_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, subscript]; simp) baseFound
  have subscriptTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change subscript ∈ [base, subscript]; simp) subscriptFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have keyType := CellAwareArrayReads.viewShape_keyType shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression
        second.expression).rename ξ) value finalStore ∧
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
    rw [viewIndex_rename, closed_rename comparison.typed]
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
          exact ⟨_, finalStore, finalMap, finalWorld, viewIndex_base_failure firstEval, .fault matched, finalHeaps,
            maps, worlds, frame, heapMetadata, effect, reached, related⟩
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
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | fault matched =>
            rw [rename_prefix] at secondEval
            exact ⟨_, finalStore, finalMap, finalWorld, viewIndex_index_failure firstEval secondEval, .fault matched,
              finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨firstSize, secondSize, baseSource, subscriptSource, middle, firstSmaller, secondSmaller, rfl, firstTrace,
        secondTrace⟩ := pair_values evaluated
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
          have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
              SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
          obtain ⟨readContext, readTyped⟩ := CellAwareArrayReads.readEnvironment_typed
            (actualTyped.weaken (firstWorlds.trans worlds)) basePayload.runtime_hasType depth word
          cases result with
          | arrayIndex reads =>
            obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds, suffixFrame,
              suffixAppend⟩ :=
              CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime view shaped
                word.isLt
            rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
            subst suffixAppend
            let suffixPool : State headers keys ⟨scope, keyMap, futureWorld, after, keyStore ++ suffix, canonical⟩ :=
              (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
            obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
              (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
            exact ⟨_, _, keyMap, futureWorld,
              CellAwareArrayReads.viewIndex_reads prepared keyType firstEval secondEval coreReads,
              .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
              (firstWorlds.trans worlds).trans suffixWorlds,
              (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
              (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                (.refl _) (.refl keyMap) suffixWorlds),
              returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
          | arrayIndexType notWord _ => exact (notWord trivial).elim
          | arrayIndexOutOfBounds outside =>
            have coreReads := CellAwareArrayReads.outside_preserve (comparison := comparison)
              (environment := CellAwareArrayReads.readEnvironment depth word coreValue actual) keyHeaps outside
              basePayload shaped word.isLt
            rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
            exact ⟨_, keyStore, keyMap, keyWorld,
              CellAwareArrayReads.viewIndex_reads prepared keyType firstEval secondEval coreReads,
              .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps, firstMaps.trans maps,
              firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- A read's head, reflected: the view's and the index's Core runs give their Source runs, and the read's
Core run is the one the Source read, or its position outside the view, gives. -/
theorem index_reflects [RecursiveStageMeaning.FaultTokens faults] {children : GenericExpressionMeaning.Certificate}
    {subscript : ExpressionId} {subscriptNode : ExpressionNode} {depth fuel : Nat} {layout : OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked}
    {second : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node layout.valueType)
    (form : node.form = .arrayIndex base subscript) (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (subscriptFound : invocation.source.lookupExpression? subscript = some subscriptNode)
    (firstChild : children scope base first) (secondChild : children scope subscript second)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (prepared : SourceCoreCompatibleDataEquality.prepare fuel compiled.compatible.checked
      (.constructor (.builtin .word)) = .ok comparison)
    (code : lowered = ⟨layout.valueType,
      SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression second.expression⟩)
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
  obtain ⟨baseType, subscriptType, baseTypedAt, view, subscriptTypedAt, kind⟩ :=
    index_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have subscriptTypeEq := CellAwareArraySourceInversion.typed_type unique subscriptFound subscriptTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, subscript]; simp) baseFound
  have subscriptTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change subscript ∈ [base, subscript]; simp) subscriptFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have secondIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ secondChild _ subscriptFound subscriptTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arrayIndex base subscript) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
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
    change EvaluationSize size actual store ((SourceCoreDataExpressions.viewIndex layout comparison.expression depth
      first.expression second.expression).rename ξ) value finalStore at evaluated
    rw [viewIndex_rename, closed_rename comparison.typed] at evaluated
    have complete := evaluated.sound
    obtain ⟨tail, split⟩ := viewIndex_split layout comparison.expression depth (first.expression.rename ξ)
      (second.expression.rename ξ)
    rw [split] at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (viewIndex_base_failure firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
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
              (viewIndex_index_failure firstEvaluation.sound secondEvaluation.sound)
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.tailFault firstTrace (.headFault secondTrace)), .fault matched, finalHeaps,
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
            have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
                SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨readContext, readTyped⟩ := CellAwareArrayReads.readEnvironment_typed
              (actualTyped.weaken (firstWorlds.trans worlds)) basePayload.runtime_hasType depth word
            rcases CellAwareArrayReads.reads_cases keyHeaps view basePayload baseRuntime baseSourceTyped word.val with
              ⟨element, reads⟩ | outside
            · obtain ⟨result, final, futureWorld, suffix, coreReads, elementRep, finalHeaps, suffixWorlds, suffixFrame,
                suffixAppend⟩ :=
                CellAwareArrayReads.reads_preserve prepared keyHeaps readTyped reads basePayload baseRuntime view shaped
                  word.isLt
              rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
              subst suffixAppend
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                (CellAwareArrayReads.viewIndex_reads prepared keyType firstEvaluation.sound secondEvaluation.sound
                  coreReads)
              let suffixPool : State headers keys ⟨scope, keyMap, futureWorld, after, _, canonical⟩ :=
                (bridge.pool reached).extend (.refl _) suffixWorlds suffixFrame (.refl _)
              obtain ⟨returned, _returnedPool, returnedRelated⟩ := bridge.restore reached suffixPool
                (.refl _) suffixWorlds suffixFrame (.refl _) (Relates.of_records_eq rfl)
              exact ⟨_, _, after, keyMap, futureWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil)) (.arrayIndex reads),
                .value (elementRep.extend (.refl _) (.refl _) suffixWorlds), finalHeaps, firstMaps.trans maps,
                (firstWorlds.trans worlds).trans suffixWorlds,
                (firstFrame.trans frame).trans suffixFrame, firstMetadata.trans heapMetadata,
                (firstEffect.trans effect).trans (CellAwareScopeAuthority.Effect.append
                  (instances := GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) _ suffix
                  (.refl _) (.refl keyMap) suffixWorlds),
                returned, callerProtocol.trans (callerProtocol.trans firstRelated related) returnedRelated⟩
            · have coreReads := fun (environment : Environment) => CellAwareArrayReads.outside_preserve
                (comparison := comparison) (environment := environment) keyHeaps outside basePayload shaped word.isLt
              rw [CellAwareArrayReads.ofNatModulo_self] at coreReads
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                (CellAwareArrayReads.viewIndex_reads prepared keyType firstEvaluation.sound secondEvaluation.sound
                  (coreReads _))
              exact ⟨_, _, after, keyMap, keyWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil)) (.arrayIndexOutOfBounds outside),
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
/-- `a[s:e]`'s head: the base's, the start's and the stop's meanings, then the bounds check against the
view's length. -/
theorem slice_range_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {start stop : ExpressionId} {startNode stopNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {startCode stopCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base (some start) (some stop))
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (startFound : invocation.source.lookupExpression? start = some startNode)
    (stopFound : invocation.source.lookupExpression? stop = some stopNode)
    (firstChild : children scope base first) (startChild : children scope start startCode)
    (stopChild : children scope stop stopCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression (some startCode.expression)
        (some stopCode.expression)⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have startTypeEq := CellAwareArraySourceInversion.typed_type unique startFound
    (replicate_typed boundsTyped start (by simp))
  have stopTypeEq := CellAwareArraySourceInversion.typed_type unique stopFound
    (replicate_typed boundsTyped stop (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, start, stop]; simp) baseFound
  have startTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change start ∈ [base, start, stop]; simp) startFound
  have stopTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change stop ∈ [base, start, stop]; simp) stopFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have startIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ startChild _ startFound startTyped
  have stopIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ stopChild _ stopFound stopTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
        (some startCode.expression) (some stopCode.expression)).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [arraySlice_rename]
    simp only [Option.map_some]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      rcases triple_fault failed with ⟨firstSize, firstSmaller, firstTrace⟩ |
        ⟨firstSize, secondSize, baseSource, middle, firstSmaller, secondSmaller, firstTrace, secondTrace⟩ |
        ⟨firstSize, secondSize, thirdSize, baseSource, startSource, firstHeap, secondHeap, firstSmaller,
          secondSmaller, thirdSmaller, firstTrace, secondTrace, thirdTrace⟩
      · obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, _⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_base_failure firstEval, .fault matched, finalHeaps,
            maps, worlds, frame, heapMetadata, effect, reached, related⟩
      · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            startIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | fault matched =>
            rw [rename_prefix] at secondEval
            exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_both_start_failure firstEval secondEval,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
      · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, startStore, startMap, startWorld, secondEval, represented, startHeaps, secondMaps, secondWorlds,
            secondFrame, secondMetadata, secondEffect, startState, secondRelated, secondPost⟩ :=
            startIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | @value _ coreStart startPayload =>
            rw [rename_prefix] at secondEval
            rw [← startTypeEq] at startPayload
            obtain ⟨startWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) startPayload
            obtain ⟨_, finalStore, finalMap, finalWorld, thirdEval, represented, finalHeaps, maps, worlds, frame,
              heapMetadata, effect, reached, related, _⟩ :=
              stopIH thirdSize (by omega) ((environments.extend firstMaps firstWorlds).extend secondMaps secondWorlds)
                startHeaps ((locals.mono firstMetadata).mono secondMetadata)
                (agree_prefix (agree_prefix agrees coreValue) (.word startWord))
                (.cons .word (.cons (payload.extend (.refl _) secondMaps secondWorlds).runtime_hasType
                  (actualTyped.weaken (firstWorlds.trans secondWorlds))))
                startState secondPost.at_value.2 ((authority.transport firstEffect).transport secondEffect)
                ((physical.transport firstEffect firstFrame).transport secondEffect secondFrame) owner ownerFrame
                thirdTrace
            cases represented with
            | fault matched =>
              rw [rename_prefix, rename_prefix] at thirdEval
              exact ⟨_, finalStore, finalMap, finalWorld,
                arraySlice_both_stop_failure firstEval secondEval thirdEval, .fault matched, finalHeaps,
                (firstMaps.trans secondMaps).trans maps, (firstWorlds.trans secondWorlds).trans worlds,
                (firstFrame.trans secondFrame).trans frame, (firstMetadata.trans secondMetadata).trans heapMetadata,
                (firstEffect.trans secondEffect).trans effect, reached,
                callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
    | result evaluated result smaller =>
      obtain ⟨firstSize, secondSize, thirdSize, baseSource, startSource, stopSource, firstHeap, secondHeap,
        firstSmaller, secondSmaller, thirdSmaller, rfl, firstTrace, secondTrace, thirdTrace⟩ := triple_values evaluated
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
        firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, startStore, startMap, startWorld, secondEval, represented, startHeaps, secondMaps, secondWorlds,
          secondFrame, secondMetadata, secondEffect, startState, secondRelated, secondPost⟩ :=
          startIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
            (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | @value _ coreStart startPayload =>
          rw [rename_prefix] at secondEval
          rw [← startTypeEq] at startPayload
          obtain ⟨startWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) startPayload
          obtain ⟨_, keyStore, keyMap, keyWorld, thirdEval, represented, keyHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            stopIH thirdSize (by omega) ((environments.extend firstMaps firstWorlds).extend secondMaps secondWorlds)
              startHeaps ((locals.mono firstMetadata).mono secondMetadata)
              (agree_prefix (agree_prefix agrees coreValue) (.word startWord))
              (.cons .word (.cons (payload.extend (.refl _) secondMaps secondWorlds).runtime_hasType
                (actualTyped.weaken (firstWorlds.trans secondWorlds))))
              startState secondPost.at_value.2 ((authority.transport firstEffect).transport secondEffect)
              ((physical.transport firstEffect firstFrame).transport secondEffect secondFrame) owner ownerFrame
              thirdTrace
          cases represented with
          | @value _ coreStop stopPayload =>
            rw [rename_prefix, rename_prefix] at thirdEval
            rw [← stopTypeEq] at stopPayload
            obtain ⟨stopWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) stopPayload
            have basePayload := payload.extend (.refl _) (secondMaps.trans maps) (secondWorlds.trans worlds)
            have startEq := CellAwareArrayReads.ofNatModulo_self startWord
            have stopEq := CellAwareArrayReads.ofNatModulo_self stopWord
            cases result with
            | arraySlice counted chosen ordered within =>
              cases chosen
              obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
              have coreRun := arraySlice_both (baseType := first.type) firstEval secondEval thirdEval measured
              rw [← startEq, ← stopEq, CellAwareArrayReads.sliced_within stopWord.isLt countSmall ordered within]
                at coreRun
              exact ⟨_, keyStore, keyMap, keyWorld, coreRun,
                .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
                (firstMaps.trans secondMaps).trans maps, (firstWorlds.trans secondWorlds).trans worlds,
                (firstFrame.trans secondFrame).trans frame, (firstMetadata.trans secondMetadata).trans heapMetadata,
                (firstEffect.trans secondEffect).trans effect, reached,
                callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
            | arraySliceBoundType member notWord _ =>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> exact (notWord trivial).elim
            | arraySliceOutOfBounds counted chosen outside =>
              cases chosen
              obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
              have coreRun := arraySlice_both (baseType := first.type) firstEval secondEval thirdEval measured
              rw [← startEq, ← stopEq,
                CellAwareArrayReads.sliced_outside startWord.isLt stopWord.isLt countSmall outside] at coreRun
              exact ⟨_, keyStore, keyMap, keyWorld, coreRun, .fault (RecursiveStageMeaning.FaultTokens.panic _),
                keyHeaps, (firstMaps.trans secondMaps).trans maps, (firstWorlds.trans secondWorlds).trans worlds,
                (firstFrame.trans secondFrame).trans frame, (firstMetadata.trans secondMetadata).trans heapMetadata,
                (firstEffect.trans secondEffect).trans effect, reached,
                callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[s:e]`'s head, reflected: the children's Core runs give their Source runs, and the bounds check is the
Source's against the view's length. -/
theorem slice_range_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {start stop : ExpressionId} {startNode stopNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {startCode stopCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base (some start) (some stop))
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (startFound : invocation.source.lookupExpression? start = some startNode)
    (stopFound : invocation.source.lookupExpression? stop = some stopNode)
    (firstChild : children scope base first) (startChild : children scope start startCode)
    (stopChild : children scope stop stopCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression (some startCode.expression)
        (some stopCode.expression)⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have startTypeEq := CellAwareArraySourceInversion.typed_type unique startFound
    (replicate_typed boundsTyped start (by simp))
  have stopTypeEq := CellAwareArraySourceInversion.typed_type unique stopFound
    (replicate_typed boundsTyped stop (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, start, stop]; simp) baseFound
  have startTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change start ∈ [base, start, stop]; simp) startFound
  have stopTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change stop ∈ [base, start, stop]; simp) stopFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have startIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ startChild _ startFound startTyped
  have stopIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ stopChild _ stopFound stopTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arraySlice base (some start) (some stop)) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
      (some startCode.expression) (some stopCode.expression)).rename ξ) value finalStore at evaluated
    rw [arraySlice_rename] at evaluated
    simp only [Option.map_some] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.arraySlice at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (arraySlice_base_failure (baseType := first.type) (depth := depth) (start := some _) (stop := some _)
            firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
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
            startIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (arraySlice_both_start_failure (baseType := first.type) (depth := depth) firstEvaluation.sound
                secondEvaluation.sound)
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.tailFault firstTrace (.headFault secondTrace)), .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, startHeap, startMap, startWorld, secondTrace, represented, startHeaps,
            secondMaps, secondWorlds, secondFrame, secondMetadata, secondEffect, startState, secondRelated,
            secondPost⟩ :=
            startIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value startSource coreStart startPayload =>
            rw [← startTypeEq] at startPayload
            obtain ⟨startWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) startPayload
            cases rest with
            | caseLeft thirdEvaluation last =>
              have shiftedStop := thirdEvaluation
              rw [← rename_prefix, ← rename_prefix] at shiftedStop
              obtain ⟨thirdSize, thirdOutcome, after, finalMap, finalWorld, thirdTrace, represented, finalHeaps, maps,
                worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
                stopIH _ (by omega) ((environments.extend firstMaps firstWorlds).extend secondMaps secondWorlds)
                  startHeaps ((locals.mono firstMetadata).mono secondMetadata)
                  (agree_prefix (agree_prefix agrees _) (.word startWord))
                  (.cons .word (.cons (payload.extend (.refl _) secondMaps secondWorlds).runtime_hasType
                    (actualTyped.weaken (firstWorlds.trans secondWorlds))))
                  startState secondPost.at_value.2 ((authority.transport firstEffect).transport secondEffect)
                  ((physical.transport firstEffect firstFrame).transport secondEffect secondFrame) owner ownerFrame
                  shiftedStop
              cases represented with
              | fault matched =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (arraySlice_both_stop_failure (baseType := first.type) (depth := depth) firstEvaluation.sound
                    secondEvaluation.sound thirdEvaluation.sound)
                exact ⟨_, _, after, finalMap, finalWorld,
                  .arrayFault occurrence rfl (.tailFault firstTrace (.tailFault secondTrace (.headFault thirdTrace))),
                  .fault matched, finalHeaps, (firstMaps.trans secondMaps).trans maps,
                  (firstWorlds.trans secondWorlds).trans worlds, (firstFrame.trans secondFrame).trans frame,
                  (firstMetadata.trans secondMetadata).trans heapMetadata, (firstEffect.trans secondEffect).trans effect,
                  reached, callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
            | caseRight thirdEvaluation last =>
              have shiftedStop := thirdEvaluation
              rw [← rename_prefix, ← rename_prefix] at shiftedStop
              obtain ⟨thirdSize, thirdOutcome, after, keyMap, keyWorld, thirdTrace, represented, keyHeaps, maps,
                worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
                stopIH _ (by omega) ((environments.extend firstMaps firstWorlds).extend secondMaps secondWorlds)
                  startHeaps ((locals.mono firstMetadata).mono secondMetadata)
                  (agree_prefix (agree_prefix agrees _) (.word startWord))
                  (.cons .word (.cons (payload.extend (.refl _) secondMaps secondWorlds).runtime_hasType
                    (actualTyped.weaken (firstWorlds.trans secondWorlds))))
                  startState secondPost.at_value.2 ((authority.transport firstEffect).transport secondEffect)
                  ((physical.transport firstEffect firstFrame).transport secondEffect secondFrame) owner ownerFrame
                  shiftedStop
              cases represented with
              | @value stopSource coreStop stopPayload =>
                rw [← stopTypeEq] at stopPayload
                obtain ⟨stopWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) stopPayload
                have basePayload := payload.extend (.refl _) (secondMaps.trans maps) (secondWorlds.trans worlds)
                have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
                    SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
                have baseSourceTyped := Dynamic.ValueHasType.mono (secondMetadata.trans heapMetadata)
                  firstPost.at_value.1
                rw [← baseTypeEq] at baseSourceTyped
                obtain ⟨count, counted⟩ := CellAwareArrayReads.length_cases keyHeaps allowed basePayload baseRuntime
                  baseSourceTyped
                obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
                have coreRun := arraySlice_both (baseType := first.type) firstEvaluation.sound secondEvaluation.sound
                  thirdEvaluation.sound measured
                have startEq := CellAwareArrayReads.ofNatModulo_self startWord
                have stopEq := CellAwareArrayReads.ofNatModulo_self stopWord
                rw [← startEq, ← stopEq] at coreRun
                by_cases inside : startWord.val ≤ stopWord.val ∧ stopWord.val ≤ count
                · rw [CellAwareArrayReads.sliced_within stopWord.isLt countSmall inside.1 inside.2] at coreRun
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace (.cons thirdTrace .nil)))
                      (.arraySlice counted .range inside.1 inside.2),
                    .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
                    (firstMaps.trans secondMaps).trans maps, (firstWorlds.trans secondWorlds).trans worlds,
                    (firstFrame.trans secondFrame).trans frame, (firstMetadata.trans secondMetadata).trans heapMetadata,
                    (firstEffect.trans secondEffect).trans effect, reached,
                    callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
                · have outside : stopWord.val < startWord.val ∨ count < stopWord.val := by omega
                  rw [CellAwareArrayReads.sliced_outside startWord.isLt stopWord.isLt countSmall outside] at coreRun
                  obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
                  exact ⟨_, _, after, keyMap, keyWorld,
                    .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace (.cons thirdTrace .nil)))
                      (.arraySliceOutOfBounds counted .range outside),
                    .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps,
                    (firstMaps.trans secondMaps).trans maps, (firstWorlds.trans secondWorlds).trans worlds,
                    (firstFrame.trans secondFrame).trans frame, (firstMetadata.trans secondMetadata).trans heapMetadata,
                    (firstEffect.trans secondEffect).trans effect, reached,
                    callerProtocol.trans (callerProtocol.trans firstRelated secondRelated) related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[s:]`'s head: the base's and the start's meanings, then the bounds check, with the view's length as the stop. -/
theorem slice_from_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {bound : ExpressionId} {boundNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {boundCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base (some bound) none)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (boundFound : invocation.source.lookupExpression? bound = some boundNode)
    (firstChild : children scope base first) (boundChild : children scope bound boundCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression (some boundCode.expression) none⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have boundTypeEq := CellAwareArraySourceInversion.typed_type unique boundFound
    (replicate_typed boundsTyped bound (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, bound]; simp) baseFound
  have boundTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change bound ∈ [base, bound]; simp) boundFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have boundIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ boundChild _ boundFound boundTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
        (some boundCode.expression) none).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [arraySlice_rename]
    simp only [Option.map_some, Option.map_none]
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
          exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_base_failure firstEval, .fault matched, finalHeaps,
            maps, worlds, frame, heapMetadata, effect, reached, related⟩
      · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            boundIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | fault matched =>
            rw [rename_prefix] at secondEval
            exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_from_start_failure firstEval secondEval,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨firstSize, secondSize, baseSource, boundSource, middle, firstSmaller, secondSmaller, rfl, firstTrace,
        secondTrace⟩ := pair_values evaluated
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
        firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, _⟩ :=
          boundIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
            (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | @value _ coreBound boundPayload =>
          rw [rename_prefix] at secondEval
          rw [← boundTypeEq] at boundPayload
          obtain ⟨boundWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) boundPayload
          have basePayload := payload.extend (.refl _) maps worlds
          have boundEq := CellAwareArrayReads.ofNatModulo_self boundWord
          cases result with
          | arraySlice counted chosen ordered within =>
            cases chosen
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_from (baseType := first.type) firstEval secondEval measured
            rw [← boundEq, CellAwareArrayReads.sliced_within countSmall countSmall ordered within] at coreRun
            exact ⟨_, keyStore, keyMap, keyWorld, coreRun,
              .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
          | arraySliceBoundType member notWord _ =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            subst member
            exact (notWord trivial).elim
          | arraySliceOutOfBounds counted chosen outside =>
            cases chosen
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_from (baseType := first.type) firstEval secondEval measured
            rw [← boundEq, CellAwareArrayReads.sliced_outside boundWord.isLt countSmall countSmall outside] at coreRun
            exact ⟨_, keyStore, keyMap, keyWorld, coreRun, .fault (RecursiveStageMeaning.FaultTokens.panic _),
              keyHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[s:]`'s head, reflected. -/
theorem slice_from_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {bound : ExpressionId} {boundNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {boundCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base (some bound) none)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (boundFound : invocation.source.lookupExpression? bound = some boundNode)
    (firstChild : children scope base first) (boundChild : children scope bound boundCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression (some boundCode.expression) none⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have boundTypeEq := CellAwareArraySourceInversion.typed_type unique boundFound
    (replicate_typed boundsTyped bound (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, bound]; simp) baseFound
  have boundTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change bound ∈ [base, bound]; simp) boundFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have boundIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ boundChild _ boundFound boundTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arraySlice base (some bound) none) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
      (some boundCode.expression) none).rename ξ) value finalStore at evaluated
    rw [arraySlice_rename] at evaluated
    simp only [Option.map_some, Option.map_none] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.arraySlice at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (arraySlice_base_failure (baseType := first.type) (depth := depth) (start := some _) (stop := none)
            firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
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
            boundIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (arraySlice_from_start_failure (baseType := first.type) (depth := depth) firstEvaluation.sound
                secondEvaluation.sound)
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.tailFault firstTrace (.headFault secondTrace)), .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            boundIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value boundSource coreBound boundPayload =>
            rw [← boundTypeEq] at boundPayload
            obtain ⟨boundWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) boundPayload
            have basePayload := payload.extend (.refl _) maps worlds
            have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
                SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨count, counted⟩ := CellAwareArrayReads.length_cases keyHeaps allowed basePayload baseRuntime
              baseSourceTyped
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_from (baseType := first.type) firstEvaluation.sound secondEvaluation.sound measured
            have boundEq := CellAwareArrayReads.ofNatModulo_self boundWord
            rw [← boundEq] at coreRun
            by_cases inside : boundWord.val ≤ count
            · rw [CellAwareArrayReads.sliced_within countSmall countSmall inside (Nat.le_refl _)] at coreRun
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
              exact ⟨_, _, after, keyMap, keyWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                  (.arraySlice counted .suffix inside (Nat.le_refl _)),
                .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
            · have outside : count < boundWord.val ∨ count < count := by omega
              rw [CellAwareArrayReads.sliced_outside boundWord.isLt countSmall countSmall outside] at coreRun
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
              exact ⟨_, _, after, keyMap, keyWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                  (.arraySliceOutOfBounds counted .suffix outside),
                .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[:e]`'s head: the base's and the stop's meanings, then the bounds check, with zero as the start. -/
theorem slice_to_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {bound : ExpressionId} {boundNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {boundCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base none (some bound))
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (boundFound : invocation.source.lookupExpression? bound = some boundNode)
    (firstChild : children scope base first) (boundChild : children scope bound boundCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression none (some boundCode.expression)⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have boundTypeEq := CellAwareArraySourceInversion.typed_type unique boundFound
    (replicate_typed boundsTyped bound (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, bound]; simp) baseFound
  have boundTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change bound ∈ [base, bound]; simp) boundFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have boundIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ boundChild _ boundFound boundTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
        none (some boundCode.expression)).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [arraySlice_rename]
    simp only [Option.map_some, Option.map_none]
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
          exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_base_failure firstEval, .fault matched, finalHeaps,
            maps, worlds, frame, heapMetadata, effect, reached, related⟩
      · obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
          firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
          firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
            owner ownerFrame firstTrace
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨_, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps, maps, worlds, frame,
            heapMetadata, effect, reached, related, _⟩ :=
            boundIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
              (locals.mono firstMetadata) (agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
              (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
          cases represented with
          | fault matched =>
            rw [rename_prefix] at secondEval
            exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_to_stop_failure firstEval secondEval,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
    | result evaluated result smaller =>
      obtain ⟨firstSize, secondSize, baseSource, boundSource, middle, firstSmaller, secondSmaller, rfl, firstTrace,
        secondTrace⟩ := pair_values evaluated
      obtain ⟨_, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps, firstMaps, firstWorlds,
        firstFrame, firstMetadata, firstEffect, middleState, firstRelated, firstPost⟩ :=
        firstIH firstSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame firstTrace
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨_, keyStore, keyMap, keyWorld, secondEval, represented, keyHeaps, maps, worlds, frame,
          heapMetadata, effect, reached, related, _⟩ :=
          boundIH secondSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2
            (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner ownerFrame secondTrace
        cases represented with
        | @value _ coreBound boundPayload =>
          rw [rename_prefix] at secondEval
          rw [← boundTypeEq] at boundPayload
          obtain ⟨boundWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) boundPayload
          have basePayload := payload.extend (.refl _) maps worlds
          have boundEq := CellAwareArrayReads.ofNatModulo_self boundWord
          cases result with
          | arraySlice counted chosen ordered within =>
            cases chosen
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_to (baseType := first.type) firstEval secondEval measured
            rw [CellAwareArrayReads.zero_ofNatModulo, ← boundEq, CellAwareArrayReads.sliced_within boundWord.isLt countSmall ordered within] at coreRun
            exact ⟨_, keyStore, keyMap, keyWorld, coreRun,
              .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
          | arraySliceBoundType member notWord _ =>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at member
            subst member
            exact (notWord trivial).elim
          | arraySliceOutOfBounds counted chosen outside =>
            cases chosen
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_to (baseType := first.type) firstEval secondEval measured
            rw [CellAwareArrayReads.zero_ofNatModulo, ← boundEq, CellAwareArrayReads.sliced_outside (by simp [wordModulus]) boundWord.isLt countSmall outside] at coreRun
            exact ⟨_, keyStore, keyMap, keyWorld, coreRun, .fault (RecursiveStageMeaning.FaultTokens.panic _),
              keyHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
              firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
              callerProtocol.trans firstRelated related⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[:e]`'s head, reflected. -/
theorem slice_to_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {bound : ExpressionId} {boundNode : ExpressionNode}
    {depth : Nat} {layout : OrderedMapping.Layout} {boundCode : SourceCoreBasic.LoweredExpr}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base none (some bound))
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (boundFound : invocation.source.lookupExpression? bound = some boundNode)
    (firstChild : children scope base first) (boundChild : children scope bound boundCode)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression none (some boundCode.expression)⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, boundsTyped⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  have boundTypeEq := CellAwareArraySourceInversion.typed_type unique boundFound
    (replicate_typed boundsTyped bound (by simp))
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base, bound]; simp) baseFound
  have boundTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change bound ∈ [base, bound]; simp) boundFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have boundIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ boundChild _ boundFound boundTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arraySlice base none (some bound)) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
      none (some boundCode.expression)).rename ξ) value finalStore at evaluated
    rw [arraySlice_rename] at evaluated
    simp only [Option.map_some, Option.map_none] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.arraySlice at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (arraySlice_base_failure (baseType := first.type) (depth := depth) (start := none) (stop := some _)
            firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
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
            boundIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | fault matched =>
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
              (arraySlice_to_stop_failure (baseType := first.type) (depth := depth) firstEvaluation.sound
                secondEvaluation.sound)
            exact ⟨_, _, after, finalMap, finalWorld,
              .arrayFault occurrence rfl (.tailFault firstTrace (.headFault secondTrace)), .fault matched, finalHeaps,
              firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata,
              firstEffect.trans effect, reached, callerProtocol.trans firstRelated related⟩
        | caseRight secondEvaluation rest =>
          have shifted := secondEvaluation
          rw [← rename_prefix] at shifted
          obtain ⟨secondSize, secondOutcome, after, keyMap, keyWorld, secondTrace, represented, keyHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related, _post⟩ :=
            boundIH _ (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState
              firstPost.at_value.2 (authority.transport firstEffect) (physical.transport firstEffect firstFrame) owner
              ownerFrame shifted
          cases represented with
          | @value boundSource coreBound boundPayload =>
            rw [← boundTypeEq] at boundPayload
            obtain ⟨boundWord, rfl, rfl, _⟩ := index_word_fields (.fixed .uint256) boundPayload
            have basePayload := payload.extend (.refl _) maps worlds
            have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
                SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
            have baseSourceTyped := Dynamic.ValueHasType.mono heapMetadata firstPost.at_value.1
            rw [← baseTypeEq] at baseSourceTyped
            obtain ⟨count, counted⟩ := CellAwareArrayReads.length_cases keyHeaps allowed basePayload baseRuntime
              baseSourceTyped
            obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted basePayload shaped
            have coreRun := arraySlice_to (baseType := first.type) firstEvaluation.sound secondEvaluation.sound measured
            have boundEq := CellAwareArrayReads.ofNatModulo_self boundWord
            rw [CellAwareArrayReads.zero_ofNatModulo, ← boundEq] at coreRun
            by_cases inside : boundWord.val ≤ count
            · rw [CellAwareArrayReads.sliced_within boundWord.isLt countSmall (Nat.zero_le _) inside] at coreRun
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
              exact ⟨_, _, after, keyMap, keyWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                  (.arraySlice counted .prefix (Nat.zero_le _) inside),
                .value (by rw [nodeType, baseTypeEq]; exact .arraySlice basePayload (by omega) carrier), keyHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
            · have outside : boundWord.val < 0 ∨ count < boundWord.val := by omega
              rw [CellAwareArrayReads.sliced_outside (by simp [wordModulus]) boundWord.isLt countSmall outside] at coreRun
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
              exact ⟨_, _, after, keyMap, keyWorld,
                .arrayResult occurrence rfl (.cons firstTrace (.cons secondTrace .nil))
                  (.arraySliceOutOfBounds counted .prefix outside),
                .fault (RecursiveStageMeaning.FaultTokens.panic _), keyHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                firstMetadata.trans heapMetadata, firstEffect.trans effect, reached,
                callerProtocol.trans firstRelated related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[:]`'s head: the base's meaning, then the whole view. -/
theorem slice_whole_preserves [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {depth : Nat} {layout : OrderedMapping.Layout}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base none none)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (firstChild : children scope base first)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression none none⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, _⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base]; simp) baseFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
        none none).rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    rw [arraySlice_rename]
    simp only [Option.map_none]
    cases CellAwareArraySourceInversion.children unique found form rfl trace with
    | fault failed smaller =>
      obtain ⟨childSize, childSmaller, childTrace⟩ := single_fault failed
      obtain ⟨_, finalStore, finalMap, finalWorld, firstEval, represented, finalHeaps, maps, worlds, frame,
        heapMetadata, effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, arraySlice_base_failure firstEval, .fault matched, finalHeaps,
          maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | result evaluated result smaller =>
      obtain ⟨childSize, baseSource, childSmaller, rfl, childTrace⟩ := single_values evaluated
      obtain ⟨_, keyStore, keyMap, keyWorld, firstEval, represented, keyHeaps, maps, worlds, frame, heapMetadata,
        effect, reached, related, _⟩ :=
        firstIH childSize (by omega) environments heaps locals agrees actualTyped initial admitted authority physical
          owner ownerFrame childTrace
      cases represented with
      | @value _ coreValue payload =>
        cases result with
        | arraySlice counted chosen ordered within =>
          cases chosen
          obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted payload shaped
          have coreRun := arraySlice_all (baseType := first.type) firstEval measured
          rw [CellAwareArrayReads.zero_ofNatModulo, CellAwareArrayReads.sliced_within countSmall countSmall ordered
            within] at coreRun
          exact ⟨_, keyStore, keyMap, keyWorld, coreRun,
            .value (by rw [nodeType, baseTypeEq]; exact .arraySlice payload (by omega) carrier), keyHeaps, maps,
            worlds, frame, heapMetadata, effect, reached, related⟩
        | arraySliceBoundType member _ _ => cases member
        | arraySliceOutOfBounds counted chosen outside =>
          cases chosen
          omega
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

include bridge functions faults unique selectedBodies runtime covers in
/-- `a[:]`'s head, reflected. -/
theorem slice_whole_reflects [RecursiveStageMeaning.FaultTokens faults]
    {children : GenericExpressionMeaning.Certificate} {depth : Nat} {layout : OrderedMapping.Layout}
    (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked invocation.source id node
      (.product first.type (.product .word .word)))
    (form : node.form = .arraySlice base none none)
    (baseFound : invocation.source.lookupExpression? base = some baseNode)
    (firstChild : children scope base first)
    (shaped : SourceCoreDataExpressions.viewShape? first.type = some (depth, layout))
    (code : lowered = ⟨.product first.type (.product .word .word),
      SourceCoreDataExpressions.arraySlice first.type depth first.expression none none⟩)
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
  obtain ⟨baseType, nodeType, allowed, baseTypedAt, _⟩ :=
    slice_source_types unique found form metadata.coercions sourceTyped
  have baseTypeEq := CellAwareArraySourceInversion.typed_type unique baseFound baseTypedAt
  obtain ⟨originalTypes, operandTyped⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found sourceTyped
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
    (by rw [form]; change base ∈ [base]; simp) baseFound
  have firstIH := fun n (bound : n < size) => @childMeaning n bound _ _ _ firstChild _ baseFound baseTyped
  have occurrence : Staging.Recursive.Occurrence invocation id (.arraySlice base none none) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  have carrier := CellAwareArrayReads.viewShape_carrier shaped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program registry sourceSize invocation context environment before id
        outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type
        (.product first.type (.product .word .word)) faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model
        (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
        mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached := by
    change EvaluationSize size actual store ((SourceCoreDataExpressions.arraySlice first.type depth first.expression
      none none).rename ξ) value finalStore at evaluated
    rw [arraySlice_rename] at evaluated
    simp only [Option.map_none] at evaluated
    have complete := evaluated.sound
    unfold SourceCoreDataExpressions.arraySlice at evaluated
    cases evaluated with
    | caseLeft firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps, maps, worlds,
        frame, heapMetadata, effect, reached, related, _post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | fault matched =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
          (arraySlice_base_failure (baseType := first.type) (depth := depth) (start := none) (stop := none)
            firstEvaluation.sound)
        exact ⟨_, _, after, finalMap, finalWorld, .arrayFault occurrence rfl (.headFault firstTrace),
          .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, effect, reached, related⟩
    | caseRight firstEvaluation branch =>
      obtain ⟨firstSize, firstOutcome, after, keyMap, keyWorld, firstTrace, represented, keyHeaps, maps,
        worlds, frame, heapMetadata, effect, reached, related, post⟩ :=
        firstIH _ (by omega) environments heaps locals agrees actualTyped initial admitted authority physical owner
          ownerFrame firstEvaluation
      cases represented with
      | @value baseSource coreValue payload =>
        have baseRuntime : SourceCoreRawMetadata.runtimeType baseNode.type =
            SourceCoreRawMetadata.runtimeType baseType := by rw [baseTypeEq]
        have baseSourceTyped := post.at_value.1
        rw [← baseTypeEq] at baseSourceTyped
        obtain ⟨count, counted⟩ := CellAwareArrayReads.length_cases keyHeaps allowed payload baseRuntime
          baseSourceTyped
        obtain ⟨measured, countSmall⟩ := CellAwareArrayReads.length_preserve keyHeaps counted payload shaped
        have coreRun := arraySlice_all (baseType := first.type) firstEvaluation.sound measured
        rw [CellAwareArrayReads.zero_ofNatModulo, CellAwareArrayReads.sliced_within countSmall countSmall
          (Nat.zero_le _) (Nat.le_refl _)] at coreRun
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete coreRun
        exact ⟨_, _, after, keyMap, keyWorld,
          .arrayResult occurrence rfl (.cons firstTrace .nil) (.arraySlice counted .whole (Nat.zero_le _) (Nat.le_refl _)),
          .value (by rw [nodeType, baseTypeEq]; exact .arraySlice payload (by omega) carrier), keyHeaps, maps,
          worlds, frame, heapMetadata, effect, reached, related⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, heapMetadata, effect, reached, related,
    SelectedStagedPostAdmission.after_expression_sized initial reached admitted selectedBodies runtime covers locals
      sourceTyped trace frame⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationArrayBounds
end
