import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaceRuns

/-! An absent declared mapping root is normalized by the actual literal emitted
by `describe`. Its header and nested default come from the certified compatible
encoder. Literal evaluation and root normalization preserve the entire store;
only the later comparator helpers allocate administrative cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.VirtualRoot
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive Quoted : Value → Expr → Prop where
  | unit : Quoted .unit .unit
  | bool (value : Bool) : Quoted (.bool value) (.bool value)
  | word (value : Word) : Quoted (.word value) (.word value)
  | integer (value : Int) : Quoted (.integer value) (.integer value)
  | pair {a b x y} : Quoted a x → Quoted b y → Quoted (.pair a b) (.pair x y)
  | inLeft {value expression} (type : Ty) : Quoted value expression → Quoted (.inLeft type value) (.inLeft type expression)
  | inRight {value expression} (type : Ty) : Quoted value expression → Quoted (.inRight type value) (.inRight type expression)
  | constructed {value expression} (constructor : ConstructorId) : Quoted value expression → Quoted (.constructed constructor value) (.construct constructor expression)

theorem quoted_of_quote {value : Value} {expression : Expr}
    (generated : SourceCoreCompatibleDataExpressions.quote value = some expression) : Quoted value expression := by
  induction value using Value.rec (motive_2 := fun _ => True) generalizing expression with
  | unit => cases generated; exact .unit
  | bool value => cases generated; exact .bool value
  | word value => cases generated; exact .word value
  | integer value => cases generated; exact .integer value
  | hostFunction | closure | cellRef => cases generated
  | pair a b first second =>
    cases left : SourceCoreCompatibleDataExpressions.quote a <;> cases right : SourceCoreCompatibleDataExpressions.quote b <;>
      simp [SourceCoreCompatibleDataExpressions.quote, left, right] at generated
    cases generated
    exact .pair (first left) (second right)
  | inLeft type value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .inLeft type (ih child)
  | inRight type value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .inRight type (ih child)
  | constructed constructor value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .constructed constructor (ih child)
  | nil | cons => trivial

theorem Quoted.weaken {value : Value} {expression : Expr} (quoted : Quoted value expression) (cutoff : Nat) :
    expression.weakenAt cutoff = expression := by
  induction quoted <;> simp_all [Expr.weakenAt]

theorem Quoted.evaluates {value : Value} {expression : Expr} (quoted : Quoted value expression)
    (environment : Environment) (store : Store) : Evaluates environment store expression value store := by
  induction quoted with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | pair _ _ left right => exact .pair left right
  | inLeft _ _ ih => exact .inLeft ih
  | inRight _ _ ih => exact .inRight ih
  | constructed _ _ ih => exact .construct ih

/-- A static receipt of the actual encoder and quote calls in `describe`. -/
inductive Generated (context : SourceCoreCompatibleDataPlaces.Context) (route : Route)
    (key value : TypeSystem.Ty) : Prop where
  | encoded {expression : Expr}
      {encoded : SourceCoreCompatibleValues.Encoded ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value [])}
      (accepted : SourceCoreCompatibleValues.encode ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value []) = .ok encoded)
      (unchanged : encoded.context.registry.entries = context.registry.entries)
      (quoted : SourceCoreCompatibleDataExpressions.quote encoded.value = some expression)
      (root : route.rootMapping = some expression) : Generated context route key value

theorem generated_of_describe {context : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {binder : TypedBinder} {key value : TypeSystem.Ty} {route : Route}
    (found : rootBinder source assignment.target.root = .ok binder)
    (declared : binder.scheme.body = .mapping key value)
    (accepted : describe context signatures source site assignment = .ok route) : Generated context route key value := by
  rcases binder with ⟨id, name, ⟨quantified, declaredType⟩, requirements, staged, span⟩
  dsimp only at declared
  subst declaredType
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> try cases accepted
  obtain ⟨actualBinder, binding, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  have same := Except.ok.inj (binding.symm.trans found)
  subst actualBinder
  obtain ⟨rootType, rootProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  cases identity : context.checked.catalog.identity? (.mapping key value) with
  | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
  | some identityValue =>
    simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨coreKey, keyProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
    obtain ⟨coreValue, valueProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
    split at accepted <;> try cases accepted
    cases encodedBy : SourceCoreCompatibleValues.encode ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value []) with
    | error error => simp [encodedBy, Except.mapError] at accepted
    | ok encoded =>
      simp only [encodedBy, Except.mapError] at accepted
      split at accepted <;> try cases accepted
      rename_i unchanged
      cases quoted : SourceCoreCompatibleDataExpressions.quote encoded.value with
      | none => simp [quoted, throw] at accepted
      | some expression =>
        simp only [quoted] at accepted
        cases projected : project context.checked site assignment.target.type with
        | error error => simp [projected] at accepted
        | ok type =>
          simp only [projected] at accepted
          cases accepted
          exact .encoded encodedBy unchanged quoted rfl

/-- Only the returned registry entries are inspected by generated literal code.
The actual encoder's extension receipt supplies the other registry laws. -/
theorem return_registry {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {expected : TypeSystem.Ty} {source : SourceCoreDataValues.Value}
    (encoded : SourceCoreCompatibleValues.Encoded fuel context expected source)
    (unchanged : encoded.context.registry.entries = context.registry.entries) :
    SourceCoreRawMetadata.Extends encoded.context.registry context.registry where
  signatures := encoded.preserves.signatures.symm
  limits := encoded.preserves.limits.symm
  staticLength := encoded.preserves.staticLength.symm
  suffix := ⟨[], by simpa only [List.append_nil] using unchanged.symm⟩

theorem Generated.fields {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    (functions : FunctionModel context.checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping) :
    ∃ expression header layout fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback := by
  cases generated with
  | encoded accepted unchanged quote root =>
    have represented := CompatibleEncoding.encode_represents_at (functions := functions) accepted (.mapping .empty) mapping world
    have represented := represented.extend (return_registry _ unchanged) (.refl mapping) (.refl world)
    obtain ⟨header, layout, entries, fallback, native, _, _, fields⟩ := mapping_fields represented rfl
    have empty : entries = [] := by
      cases entries with
      | nil => rfl
      | cons head tail => have length := fields.stored.length; simp at length
    subst entries
    exact ⟨_, header, layout, fallback, root, by simpa only [native] using quoted_of_quote quote, fields⟩

theorem Generated.at_layout {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    (functions : FunctionModel context.checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (layout : Core.OrderedMapping.Layout) (registered : layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout)) :
    ∃ expression header fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback := by
  obtain ⟨expression, header, actualLayout, fallback, root, quoted, fields⟩ := generated.fields functions mapping world
  have same := registered_layout_eq fields.registered registered (Except.ok.inj (fields.represents.projection.symm.trans projected))
  subst actualLayout
  exact ⟨expression, header, fallback, root, quoted, fields⟩

theorem Generated.at_layout_extended {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    (functions : FunctionModel context.checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (layout : Core.OrderedMapping.Layout) (registered : layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ expression header fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked registry functions mapping world key value [] header layout [] fallback := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout functions mapping world layout registered projected
  exact ⟨expression, header, fallback, root, quoted, ⟨fields.metadata.extend extended,
    fields.identity, fields.keyProjection, fields.valueProjection, fields.registered,
    fields.stored.extend extended (.refl mapping) (.refl world), fields.default.extend extended (.refl mapping) (.refl world)⟩⟩

theorem normalize_absent (prepared : Prepared) {expression : Expr} {value : Value}
    (root : prepared.route.rootMapping = some expression) (quoted : Quoted value expression)
    (environment : Environment) (store : Store) (optional : Expr)
    (selected : Selects environment optional (.inLeft prepared.route.rootType .unit)) :
    Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit value) store := by
  simp only [normalizeRoot, root]
  apply Evaluates.caseLeft (selected.evaluates store)
  apply Evaluates.inRight
  rw [quoted.weaken]
  exact quoted.evaluates _ store

theorem generated_normalizes {context : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    {key value : TypeSystem.Ty} (generated : Generated context prepared.route key value)
    (functions : FunctionModel context.checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (environment : Environment) (store : Store) (optional : Expr)
    (selected : Selects environment optional (.inLeft prepared.route.rootType .unit)) :
    ∃ header layout fallback,
      Dynamic.RootInitialValue ⟨.mapping key value, none, none⟩ (some (.mapping key value [])) ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback ∧
      Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit (Transport.carrier header fallback layout [])) store := by
  obtain ⟨expression, header, layout, fallback, root, quoted, fields⟩ := generated.fields functions mapping world
  exact ⟨header, layout, fallback, .emptyMapping _ _, fields, normalize_absent prepared root quoted environment store optional selected⟩

theorem getter_absent {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {functions : FunctionModel context.checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (packValues keys))) :
    ∃ header result finalStore administrative,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      ReadResult context.checked registry functions mapping world sourceValue sourceLookup [] index.layout.valueType index.missing header result ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (liftedRead prepared.optionalLeaf result) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout_extended functions mapping world index.layout registered projected extended
  let stored := Transport.carrier header fallback index.layout []
  let input := Value.pair (.inLeft prepared.route.rootType .unit) (packValues keys)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨result, meaning, evaluated⟩ := selectOne_meaning certificate prepared faithful functionLeaves fields keyRep
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) selectedKey
  obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    bodyEnvironment store header fallback [] key
  refine ⟨header, result, _, administrative, fields.metadata, .emptyMapping _ _, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  exact .caseRight (normalize_absent prepared root quoted _ store (.first (.var 0)) (.first (.var rfl))) evaluated

theorem setter_absent {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {functions : FunctionModel context.checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement))) :
    ∃ header fallback result finalStore administrative count,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      UpdateResult context.checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement [] header index.layout fallback index.missing result count ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout_extended functions mapping world index.layout registered projected extended
  let stored := Transport.carrier header fallback index.layout []
  let input := Value.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ := updateOne_meaning certificate prepared faithful functionLeaves
    fields keyRep replacementRep bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) selectedKey (.second (.second (.var rfl)))
  refine ⟨header, fallback, result, finalStore, administrative, count, fields.metadata, .emptyMapping _ _, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (normalize_absent prepared root quoted _ store (.first (.var 0)) (.first (.var rfl)))
  simpa only [bodyEnvironment, input, stored, rootType] using evaluated

theorem getter_absent_run {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {functions : FunctionModel context.checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (packValues keys))) :
    ∃ header result finalStore administrative,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      ReadResult context.checked registry functions mapping world sourceValue sourceLookup [] index.layout.valueType index.missing header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done (liftedRead prepared.optionalLeaf result) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = liftedRead prepared.optionalLeaf result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  obtain ⟨header, result, finalStore, administrative, metadata, initial, meaning, evaluated, appended, count⟩ :=
    getter_absent certificate prepared steps generated registered projected extended faithful functionLeaves keyRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨header, result, finalStore, administrative, metadata, initial, meaning,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, count⟩

theorem setter_absent_run {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {functions : FunctionModel context.checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement))) :
    ∃ header fallback result finalStore administrative count,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      UpdateResult context.checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement [] header index.layout fallback index.missing result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨header, fallback, result, finalStore, administrative, count, metadata, initial, meaning, evaluated, appended, length⟩ :=
    setter_absent certificate prepared steps rootType generated registered projected extended faithful functionLeaves keyRep replacementRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨header, fallback, result, finalStore, administrative, count, metadata, initial, meaning,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.VirtualRoot
