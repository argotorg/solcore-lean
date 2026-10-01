import Solcore.SourceSemantics.CoreLowering.CompatibleMappingUpdates

/-! The actual generated getter/setter always finish with enough fuel and all
completed runs agree with their independent source result. The scope is an
initialized root and one index; source-expression and raw key guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

/-- The standalone helper does not check the raw source key type. With that
independent receipt, its missing-default outcome is exactly the source fault. -/
theorem UpdateResult.failure {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {key replacement : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {header missing token : Word}
    {layout : Core.OrderedMapping.Layout} {fallback : Option Value} {count : Nat}
    (result : UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources
      header layout fallback missing (.inLeft (SourceCoreMappingWithDefault.type layout) (.word token)) count)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches key sourceKey) :
    token = missing.add header ∧ count = checked.catalog.entries.length + 1 ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKey sourceValue sources)) [.index key]
        (.missingMappingDefault sourceValue) := by
  cases result with
  | missing absent unavailable => exact ⟨rfl, rfl, .indexDefaultUnavailable keyTyped absent unavailable⟩

 theorem getter_initialized_run {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {registry : Registry} {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (packValues keys))) :
    ∃ result finalStore administrative,
      ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done (liftedRead prepared.optionalLeaf result) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = liftedRead prepared.optionalLeaf result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ :=
    getter_initialized certificate prepared steps faithful functionLeaves fields keyRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨result, finalStore, administrative, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

 theorem setter_initialized_run {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {registry : Registry} {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (.pair (packValues keys) replacement))) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ :=
    setter_initialized certificate prepared steps rootType faithful functionLeaves fields keyRep replacementRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨result, finalStore, administrative, count, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
