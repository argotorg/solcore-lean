import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.Frontend.SourceCore.Compatible

/-!
# Compatible expressions: memory arrays

The compiler's receipts of the memory array forms: an accepted lowering of `new`, a literal, a length,
a read, a slice, `toArray`, `lidx`, `CanStore.load` and `CanStore.store` gives its Core code, the
lowerings of its children and the layout of the array's present elements. Main declarations:
`newArray_of_lower`, `arrayIndex_of_lower`, `memrefStore_of_lower` and their `_of_functions` forms.
-/

section
/-! Each receipt inverts the form's case of `SourceCoreCompatibleDataExpressions.lowerWithReasons`, as
`CompatibleExpressionIndices.index_of_lower` does for mapping reads. A receipt holds no execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionArrays
open Core Frontend SourceInference CompatibleExpressionReads

abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope
abbrev Child := SourceCoreFunctions.ExpressionLowerer
abbrev Lowered := SourceCoreBasic.LoweredExpr

/-- The Core type of a memory array whose present elements have the layout `⟨word, payload, identity⟩`:
a cell of its length, its default element and its entries. -/
abbrev arrayType (payload : Core.Ty) (identity : Core.DataTypeId) : Core.Ty :=
  .cell (.product .word (.product payload (.namedData identity)))

/-- The layout of an array's present elements, keyed by the words of positions. -/
abbrev arrayLayout (payload : Core.Ty) (identity : Core.DataTypeId) : Core.OrderedMapping.Layout :=
  ⟨.word, payload, identity⟩

/-- The comparison the compiler prepares for words, which reads and stores look positions up by. -/
abbrev WordComparison (values : ValuesContext) (fuel : Nat)
    (comparison : SourceCoreCompatibleDataEquality.Prepared values.checked) : Prop :=
  SourceCoreCompatibleDataEquality.prepare fuel values.checked (.constructor (.builtin .word)) = .ok comparison

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ} {value : α}
    (accepted : action.mapError map = .ok value) : action = .ok value := by
  cases action with
  | error error => cases accepted
  | ok actual => cases accepted; rfl

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked

private theorem forM_ensure {site : SourceCoreElaboration.ErrorSite} {expected : Core.Ty} :
    ∀ {values : List Lowered},
      values.forM (fun value => SourceCoreBasic.ensureType site expected value.type) = .ok () →
      ∀ value ∈ values, value.type = expected
  | [], _, _, member => by cases member
  | head :: tail, checked, value, member => by
    simp only [List.forM] at checked
    obtain ⟨⟨⟩, headChecked, tailChecked⟩ := bind_ok checked
    rcases List.mem_cons.mp member with same | member
    · subst value; exact (ensureType_ok headChecked).symm
    · exact forM_ensure tailChecked value member

variable {values : ValuesContext} {child : Child} {fuel : Nat} {source : TypedSource} {scope : Scope}
  {id : ExpressionId} {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : Lowered}

/-- `new T[](n)`: the array type's layout, `T`'s default and the length's lowering. -/
theorem newArray_of_lower {element : TypeSystem.Ty} {length : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .newArray element length)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ payload identity default first,
      lowered = ⟨arrayType payload identity,
        SourceCoreDataExpressions.newArray (arrayLayout payload identity) default first.expression⟩ ∧
      Metadata values.checked source id node (arrayType payload identity) ∧
      values.checked.catalog.project (TypeSystem.Ty.array element) = .ok (arrayType payload identity) ∧
      SourceCoreCompatibleDataExpressions.arrayDefault values.checked.catalog element = some default ∧
      child fuel source scope length reasonAt = .ok first ∧ first.type = .word := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨arrayCore, projected, accepted⟩ := bind_ok accepted
  replace projected := projectType_of_accepted projected
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  split at accepted
  case h_2 => cases accepted
  rename_i payload identity _
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  subst type
  split at accepted
  case h_2 => cases accepted
  rename_i default defaultAt
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, firstEnsured, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨payload, identity, default, first, rfl, metadata, projected, defaultAt, firstLowered,
    (ensureType_ok firstEnsured).symm⟩

/-- `[e₀, …, eₙ₋₁]`: the array type's layout, the element type's default and the elements' lowerings,
each at the element's Core type. -/
theorem arrayLiteral_of_lower {element : TypeSystem.Ty} {elements : List ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .arrayLiteral element elements)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ payload identity default children,
      lowered = ⟨arrayType payload identity,
        SourceCoreDataExpressions.arrayLiteral (arrayLayout payload identity) default
          (SourceCoreCalls.packArguments children).expression children.length⟩ ∧
      Metadata values.checked source id node (arrayType payload identity) ∧
      values.checked.catalog.project (TypeSystem.Ty.array element) = .ok (arrayType payload identity) ∧
      SourceCoreCompatibleDataExpressions.arrayDefault values.checked.catalog element = some default ∧
      elements.mapM (fun value => child fuel source scope value reasonAt) = .ok children ∧
      ∀ value ∈ children, value.type = payload := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨arrayCore, projected, accepted⟩ := bind_ok accepted
  replace projected := projectType_of_accepted projected
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  split at accepted
  case h_2 => cases accepted
  rename_i payload identity _
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  subst type
  split at accepted
  case h_2 => cases accepted
  rename_i default defaultAt
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨children, childrenLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, childrenEnsured, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨payload, identity, default, children, rfl, metadata, projected, defaultAt, childrenLowered,
    forM_ensure childrenEnsured⟩

/-- A length: the base's lowering, an array's cell or a slice. -/
theorem arrayLength_of_lower {base : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .arrayLength base)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ first, Metadata values.checked source id node .word ∧ child fuel source scope base reasonAt = .ok first ∧
      ((∃ rest, first.type = .cell (.product .word rest) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.arrayLength first.expression⟩) ∨
        (∃ view, first.type = .product view (.product .word .word) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.sliceLength first.expression⟩)) := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  refine ⟨first, metadata, firstLowered, ?_⟩
  split at accepted
  · rename_i rest shape
    cases accepted
    exact .inl ⟨rest, shape, rfl⟩
  · rename_i view shape
    cases accepted
    exact .inr ⟨view, shape, rfl⟩
  · cases accepted

/-- `a[i]` on a view inside `depth` slices: the base's and the index's lowerings and the word comparison. -/
theorem arrayIndex_of_lower {base index : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .arrayIndex base index)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ depth layout comparison first second,
      lowered = ⟨layout.valueType,
        SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression second.expression⟩ ∧
      Metadata values.checked source id node layout.valueType ∧
      child fuel source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth, layout) ∧
      child fuel source scope index reasonAt = .ok second ∧ second.type = .word ∧
      WordComparison values fuel comparison := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i shape shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  rcases shape with ⟨depth, layout⟩
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨second, secondLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, secondEnsured, accepted⟩ := bind_ok accepted
  obtain ⟨comparison, comparisonPrepared, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨depth, layout, comparison, first, second, rfl, metadata, firstLowered, shaped, secondLowered,
    (ensureType_ok secondEnsured).symm, mapError_ok comparisonPrepared⟩

/-- `a[s:e]` and its forms without a bound, on a view inside `depth` slices: the base's and the present
bounds' lowerings, each bound a word. -/
theorem arraySlice_of_lower {base : ExpressionId} {start stop : Option ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .arraySlice base start stop)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ depth layout first starts stops,
      lowered = ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression
          (starts.map (·.expression)) (stops.map (·.expression))⟩ ∧
      Metadata values.checked source id node (.product first.type (.product .word .word)) ∧
      child fuel source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth, layout) ∧
      start.mapM (fun bound => child fuel source scope bound reasonAt) = .ok starts ∧
      stop.mapM (fun bound => child fuel source scope bound reasonAt) = .ok stops ∧
      ∀ bound ∈ starts.toList ++ stops.toList, bound.type = .word := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i shape shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  rcases shape with ⟨depth, layout⟩
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨starts, startsLowered, accepted⟩ := bind_ok accepted
  obtain ⟨stops, stopsLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, boundsEnsured, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨depth, layout, first, starts, stops, rfl, metadata, firstLowered, shaped, startsLowered,
    stopsLowered, forM_ensure boundsEnsured⟩

/-- `toArray(s)` on a slice inside `depth + 1` slices: the slice's lowering, the layout of the array under
it and the word comparison. -/
theorem toArray_of_lower {element : TypeSystem.Ty} {slice : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .toArray element slice)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ depth layout comparison first,
      lowered = ⟨.cell (.product .word (.product layout.valueType layout.type)),
        SourceCoreDataExpressions.sliceCopy layout comparison.expression (depth + 1) first.type
          first.expression⟩ ∧
      Metadata values.checked source id node (.cell (.product .word (.product layout.valueType layout.type))) ∧
      child fuel source scope slice reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth + 1, layout) ∧
      WordComparison values fuel comparison := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i inner layout shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨comparison, comparisonPrepared, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨inner, layout, comparison, first, rfl, metadata, firstLowered, shaped, mapError_ok comparisonPrepared⟩

/-- `lidx(a, i)` on an array: the array's and the index's lowerings. -/
theorem elementRef_of_lower {base index : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .elementRef base index)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ layout first second,
      lowered = ⟨.product first.type .word,
        SourceCoreDataExpressions.elementRef layout first.expression second.expression⟩ ∧
      Metadata values.checked source id node (.product first.type .word) ∧
      child fuel source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (0, layout) ∧
      child fuel source scope index reasonAt = .ok second ∧ second.type = .word := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i layout shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨second, secondLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, secondEnsured, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨layout, first, second, rfl, metadata, firstLowered, shaped, secondLowered,
    (ensureType_ok secondEnsured).symm⟩

/-- `CanStore.load(r)`: the memref's lowering, the layout of its array's present elements and the word
comparison. -/
theorem memrefLoad_of_lower {reference : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .memrefLoad reference)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ layout comparison first,
      lowered = ⟨layout.valueType,
        SourceCoreDataExpressions.memrefLoad layout comparison.expression first.expression⟩ ∧
      Metadata values.checked source id node layout.valueType ∧
      child fuel source scope reference reasonAt = .ok first ∧
      SourceCoreDataExpressions.memrefLayout? first.type = some layout ∧
      WordComparison values fuel comparison := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i layout shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨comparison, comparisonPrepared, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨layout, comparison, first, rfl, metadata, firstLowered, shaped, mapError_ok comparisonPrepared⟩

/-- `CanStore.store(r, v)`: the memref's and the value's lowerings, the value at its array's element type,
and the word comparison. -/
theorem memrefStore_of_lower {reference value : ExpressionId}
    (found : source.lookupExpression? id = some node) (form : node.form = .memrefStore reference value)
    (accepted : SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values child source scope id
      reasonAt = .ok lowered) :
    ∃ layout comparison first second,
      lowered = ⟨.unit,
        SourceCoreDataExpressions.memrefStore layout comparison.expression first.expression second.expression⟩ ∧
      Metadata values.checked source id node .unit ∧
      child fuel source scope reference reasonAt = .ok first ∧
      SourceCoreDataExpressions.memrefLayout? first.type = some layout ∧
      child fuel source scope value reasonAt = .ok second ∧ second.type = layout.valueType ∧
      WordComparison values fuel comparison := by
  unfold SourceCoreCompatibleDataExpressions.lowerWithReasons at accepted
  obtain ⟨read, readAccepted, accepted⟩ := bind_ok accepted
  rcases read with ⟨actualNode, type⟩
  have metadata := metadata_of_read readAccepted
  have same := Option.some.inj (metadata.found.symm.trans found)
  subst actualNode
  simp only [form] at accepted
  obtain ⟨first, firstLowered, accepted⟩ := bind_ok accepted
  split at accepted
  case h_2 => cases accepted
  rename_i layout shaped
  obtain ⟨_, chosen, accepted⟩ := bind_ok accepted
  cases chosen
  obtain ⟨⟨⟩, typeEnsured, accepted⟩ := bind_ok accepted
  have typeEq := ensureType_ok typeEnsured
  subst type
  obtain ⟨second, secondLowered, accepted⟩ := bind_ok accepted
  obtain ⟨⟨⟩, secondEnsured, accepted⟩ := bind_ok accepted
  obtain ⟨comparison, comparisonPrepared, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨layout, comparison, first, second, rfl, metadata, firstLowered, shaped, secondLowered,
    (ensureType_ok secondEnsured).symm, mapError_ok comparisonPrepared⟩


/-- The memory array forms, which the functions lowering hands to the data lowering. -/
inductive ArrayForm : ExpressionForm → Prop where
  | newArray (element : TypeSystem.Ty) (length : ExpressionId) : ArrayForm (.newArray element length)
  | arrayLiteral (element : TypeSystem.Ty) (elements : List ExpressionId) :
      ArrayForm (.arrayLiteral element elements)
  | arrayLength (base : ExpressionId) : ArrayForm (.arrayLength base)
  | arrayIndex (base index : ExpressionId) : ArrayForm (.arrayIndex base index)
  | arraySlice (base : ExpressionId) (start stop : Option ExpressionId) : ArrayForm (.arraySlice base start stop)
  | toArray (element : TypeSystem.Ty) (slice : ExpressionId) : ArrayForm (.toArray element slice)
  | elementRef (base index : ExpressionId) : ArrayForm (.elementRef base index)
  | memrefLoad (reference : ExpressionId) : ArrayForm (.memrefLoad reference)
  | memrefStore (reference value : ExpressionId) : ArrayForm (.memrefStore reference value)

section Functions
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {context : SourceCoreFunctions.Context}

/-- The child lowering that the functions lowering hands to the data lowering, one step below. -/
abbrev below (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer) (fuel : Nat)
    (context : SourceCoreFunctions.Context) : Child :=
  fun budget childSource childScope childId childReasonAt =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope
      childId childReasonAt

/-- With no special lowering at the occurrence and the compatible leaves, the functions lowering of an
array form is the data lowering's, its children lowered one step below. -/
theorem data_of_functions {form : ExpressionForm}
    (found : source.lookupExpression? id = some node) (shape : node.form = form) (array : ArrayForm form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id
      reasonAt = .ok lowered) :
    SourceCoreCompatibleDataExpressions.lowerWithReasons (fuel + 1) values (below policy body fuel context)
      source scope id reasonAt = .ok lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (below policy body fuel context) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      cases array
      all_goals
        simp only [shape, readPolicy] at accepted
        cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
        | error error => simp [read] at accepted
        | ok pair =>
          rcases pair with ⟨other, type⟩
          have metadata := metadata_of_read read
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst other
          simp only [read, shape, leafPolicy] at accepted
          unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
          simp only [read, bind, Except.bind, shape] at accepted
          exact accepted
  · simp [owner, bind, Except.bind] at accepted

variable (found : source.lookupExpression? id = some node)
  (special : ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower context child budget source scope id reasonAt) = .ok none)
  (readPolicy : policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
  (leafPolicy : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
  (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id
    reasonAt = .ok lowered)
include found special readPolicy leafPolicy accepted

theorem newArray_of_functions {element : TypeSystem.Ty} {length : ExpressionId}
    (form : node.form = .newArray element length) :
    ∃ payload identity default first,
      lowered = ⟨arrayType payload identity,
        SourceCoreDataExpressions.newArray (arrayLayout payload identity) default first.expression⟩ ∧
      Metadata values.checked source id node (arrayType payload identity) ∧
      values.checked.catalog.project (TypeSystem.Ty.array element) = .ok (arrayType payload identity) ∧
      SourceCoreCompatibleDataExpressions.arrayDefault values.checked.catalog element = some default ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope length reasonAt =
        .ok first ∧ first.type = .word := by
  obtain ⟨payload, identity, default, first, output, metadata, projected, defaultAt, firstLowered, firstType⟩ :=
    newArray_of_lower found form (data_of_functions found form (.newArray _ _) special readPolicy leafPolicy accepted)
  exact ⟨payload, identity, default, first, output, metadata, projected, defaultAt,
    by simpa only [below, Nat.min_self] using firstLowered, firstType⟩

theorem arrayLiteral_of_functions {element : TypeSystem.Ty} {elements : List ExpressionId}
    (form : node.form = .arrayLiteral element elements) :
    ∃ payload identity default children,
      lowered = ⟨arrayType payload identity,
        SourceCoreDataExpressions.arrayLiteral (arrayLayout payload identity) default
          (SourceCoreCalls.packArguments children).expression children.length⟩ ∧
      Metadata values.checked source id node (arrayType payload identity) ∧
      values.checked.catalog.project (TypeSystem.Ty.array element) = .ok (arrayType payload identity) ∧
      SourceCoreCompatibleDataExpressions.arrayDefault values.checked.catalog element = some default ∧
      elements.mapM (fun value => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source
        scope value reasonAt) = .ok children ∧
      ∀ value ∈ children, value.type = payload := by
  obtain ⟨payload, identity, default, children, output, metadata, projected, defaultAt, lowerings, types⟩ :=
    arrayLiteral_of_lower found form (data_of_functions found form (.arrayLiteral _ _) special readPolicy leafPolicy accepted)
  exact ⟨payload, identity, default, children, output, metadata, projected, defaultAt,
    by simpa only [below, Nat.min_self] using lowerings, types⟩

theorem arrayLength_of_functions {base : ExpressionId} (form : node.form = .arrayLength base) :
    ∃ first, Metadata values.checked source id node .word ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok first ∧
      ((∃ rest, first.type = .cell (.product .word rest) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.arrayLength first.expression⟩) ∨
        (∃ view, first.type = .product view (.product .word .word) ∧
          lowered = ⟨.word, SourceCoreDataExpressions.sliceLength first.expression⟩)) := by
  obtain ⟨first, metadata, firstLowered, shaped⟩ :=
    arrayLength_of_lower found form (data_of_functions found form (.arrayLength _) special readPolicy leafPolicy accepted)
  exact ⟨first, metadata, by simpa only [below, Nat.min_self] using firstLowered, shaped⟩

theorem arrayIndex_of_functions {base index : ExpressionId} (form : node.form = .arrayIndex base index) :
    ∃ depth layout comparison first second,
      lowered = ⟨layout.valueType,
        SourceCoreDataExpressions.viewIndex layout comparison.expression depth first.expression second.expression⟩ ∧
      Metadata values.checked source id node layout.valueType ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth, layout) ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope index reasonAt =
        .ok second ∧ second.type = .word ∧
      WordComparison values fuel comparison := by
  obtain ⟨depth, layout, comparison, first, second, output, metadata, firstLowered, shaped, secondLowered,
    secondType, prepared⟩ :=
    arrayIndex_of_lower found form (data_of_functions found form (.arrayIndex _ _) special readPolicy leafPolicy accepted)
  exact ⟨depth, layout, comparison, first, second, output, metadata,
    by simpa only [below, Nat.min_self] using firstLowered, shaped,
    by simpa only [below, Nat.min_self] using secondLowered, secondType, prepared⟩

theorem arraySlice_of_functions {base : ExpressionId} {start stop : Option ExpressionId}
    (form : node.form = .arraySlice base start stop) :
    ∃ depth layout first starts stops,
      lowered = ⟨.product first.type (.product .word .word),
        SourceCoreDataExpressions.arraySlice first.type depth first.expression
          (starts.map (·.expression)) (stops.map (·.expression))⟩ ∧
      Metadata values.checked source id node (.product first.type (.product .word .word)) ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth, layout) ∧
      start.mapM (fun bound => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope
        bound reasonAt) = .ok starts ∧
      stop.mapM (fun bound => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope
        bound reasonAt) = .ok stops ∧
      ∀ bound ∈ starts.toList ++ stops.toList, bound.type = .word := by
  obtain ⟨depth, layout, first, starts, stops, output, metadata, firstLowered, shaped, startsLowered,
    stopsLowered, types⟩ :=
    arraySlice_of_lower found form (data_of_functions found form (.arraySlice _ _ _) special readPolicy leafPolicy accepted)
  exact ⟨depth, layout, first, starts, stops, output, metadata,
    by simpa only [below, Nat.min_self] using firstLowered, shaped,
    by simpa only [below, Nat.min_self] using startsLowered,
    by simpa only [below, Nat.min_self] using stopsLowered, types⟩

theorem toArray_of_functions {element : TypeSystem.Ty} {slice : ExpressionId}
    (form : node.form = .toArray element slice) :
    ∃ depth layout comparison first,
      lowered = ⟨.cell (.product .word (.product layout.valueType layout.type)),
        SourceCoreDataExpressions.sliceCopy layout comparison.expression (depth + 1) first.type
          first.expression⟩ ∧
      Metadata values.checked source id node (.cell (.product .word (.product layout.valueType layout.type))) ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope slice reasonAt =
        .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (depth + 1, layout) ∧
      WordComparison values fuel comparison := by
  obtain ⟨depth, layout, comparison, first, output, metadata, firstLowered, shaped, prepared⟩ :=
    toArray_of_lower found form (data_of_functions found form (.toArray _ _) special readPolicy leafPolicy accepted)
  exact ⟨depth, layout, comparison, first, output, metadata,
    by simpa only [below, Nat.min_self] using firstLowered, shaped, prepared⟩

theorem elementRef_of_functions {base index : ExpressionId} (form : node.form = .elementRef base index) :
    ∃ layout first second,
      lowered = ⟨.product first.type .word,
        SourceCoreDataExpressions.elementRef layout first.expression second.expression⟩ ∧
      Metadata values.checked source id node (.product first.type .word) ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope base reasonAt = .ok first ∧
      SourceCoreDataExpressions.viewShape? first.type = some (0, layout) ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope index reasonAt =
        .ok second ∧ second.type = .word := by
  obtain ⟨layout, first, second, output, metadata, firstLowered, shaped, secondLowered, secondType⟩ :=
    elementRef_of_lower found form (data_of_functions found form (.elementRef _ _) special readPolicy leafPolicy accepted)
  exact ⟨layout, first, second, output, metadata, by simpa only [below, Nat.min_self] using firstLowered, shaped,
    by simpa only [below, Nat.min_self] using secondLowered, secondType⟩

theorem memrefLoad_of_functions {reference : ExpressionId} (form : node.form = .memrefLoad reference) :
    ∃ layout comparison first,
      lowered = ⟨layout.valueType,
        SourceCoreDataExpressions.memrefLoad layout comparison.expression first.expression⟩ ∧
      Metadata values.checked source id node layout.valueType ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope reference reasonAt =
        .ok first ∧
      SourceCoreDataExpressions.memrefLayout? first.type = some layout ∧
      WordComparison values fuel comparison := by
  obtain ⟨layout, comparison, first, output, metadata, firstLowered, shaped, prepared⟩ :=
    memrefLoad_of_lower found form (data_of_functions found form (.memrefLoad _) special readPolicy leafPolicy accepted)
  exact ⟨layout, comparison, first, output, metadata, by simpa only [below, Nat.min_self] using firstLowered,
    shaped, prepared⟩

theorem memrefStore_of_functions {reference value : ExpressionId}
    (form : node.form = .memrefStore reference value) :
    ∃ layout comparison first second,
      lowered = ⟨.unit,
        SourceCoreDataExpressions.memrefStore layout comparison.expression first.expression second.expression⟩ ∧
      Metadata values.checked source id node .unit ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope reference reasonAt =
        .ok first ∧
      SourceCoreDataExpressions.memrefLayout? first.type = some layout ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope value reasonAt =
        .ok second ∧ second.type = layout.valueType ∧
      WordComparison values fuel comparison := by
  obtain ⟨layout, comparison, first, second, output, metadata, firstLowered, shaped, secondLowered, secondType,
    prepared⟩ :=
    memrefStore_of_lower found form (data_of_functions found form (.memrefStore _ _) special readPolicy leafPolicy accepted)
  exact ⟨layout, comparison, first, second, output, metadata,
    by simpa only [below, Nat.min_self] using firstLowered, shaped,
    by simpa only [below, Nat.min_self] using secondLowered, secondType, prepared⟩

end Functions

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionArrays
end
