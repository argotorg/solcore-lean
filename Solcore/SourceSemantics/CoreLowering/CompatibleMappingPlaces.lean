import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMeaning
import Solcore.Frontend.SourceCoreCompatibleDataPlaces

/-! Single generated compatible index paths. These are the production
select/update/getter/setter expressions. Their static step/comparator receipts
are separate from whole source-expression typing and evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

structure Index (checked : SourceCoreCompatibleCatalog.Checked) (index : PreparedIndex) where
  comparison : SourceCoreCompatibleDataEquality.Prepared checked
  expression : index.comparison = comparison.expression
  keyType : index.layout.keyType = comparison.type

def liftedRead (resultType : Ty) (result : Value) : Value :=
  match result with
  | .inRight .word value => .inRight .word (.inRight .unit value)
  | .inLeft _ reason => .inLeft resultType reason
  | _ => result

 theorem selectedIndex_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      Evaluates environment store (selectedIndex prepared index current keys) result
        (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key) := by
  simpa only [selectedIndex, certificate.expression] using
    lookup_meaning certificate.comparison certificate.keyType faithful functionLeaves fields keyRep
      environment store index.missing current _ mappingSelected keySelected

 theorem selectOne_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      Evaluates environment store (select prepared [.index index] current keys) (liftedRead prepared.optionalLeaf result)
        (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key) := by
  obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
    environment store current keys mappingSelected keySelected
  refine ⟨result, meaning, ?_⟩
  cases meaning with
  | found | default => exact LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))
  | missing => exact LanguageResult.bind_failure _ evaluated

 theorem normalizeRoot_initialized (prepared : Prepared) {environment : Environment} {optional : Expr} {value : Value}
    (selected : Selects environment optional (.inRight .unit value)) (store : Store) :
    Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit value) store := by
  unfold normalizeRoot
  cases prepared.route.rootMapping with
  | none => exact selected.evaluates store
  | some empty => exact .caseRight (selected.evaluates store) (.inRight (.var rfl))

 theorem getter_initialized {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
      Evaluates environment store (.apply (getter prepared keyType) argument) (liftedRead prepared.optionalLeaf result) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let stored := Transport.carrier header fallback index.layout entries
  let input := Value.pair (.inRight .unit stored) (packValues keys)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨result, meaning, evaluated⟩ := selectOne_meaning certificate prepared faithful functionLeaves fields keyRep
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) selectedKey
  obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    bodyEnvironment store header fallback entries key
  refine ⟨result, _, administrative, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  exact .caseRight (normalizeRoot_initialized prepared (.first (.var rfl)) store) evaluated

theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
    SourceCoreDataExpressions.projectPacked index types (expression.weakenAt 0) =
      (SourceCoreDataExpressions.projectPacked index types expression).weakenAt 0 := by
  induction types generalizing index expression with
  | nil => simp [SourceCoreDataExpressions.projectPacked, Expr.weakenAt]
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      by_cases zero : index = 0
      · simp [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt]
      · simpa [SourceCoreDataExpressions.projectPacked, zero, Expr.weakenAt] using ih (index - 1) (.second expression)

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
