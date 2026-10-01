import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedUpdates
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot

/-! Actual compatible getter/setter closures over complete mixed paths.
Normalization is a structural receipt: an initialized value or the literal
certified from describe's virtual empty mapping. Source-cell writes and the
index/RHS expression sequence remain outside these pure helper theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive RootInput (prepared : Prepared) : Dynamic.Cell → Value → Dynamic.Value → Value → Prop where
  | initialized {sourceType source value} :
      RootInput prepared ⟨sourceType, some source, none⟩ (.inRight .unit value) source value
  | virtual {key valueType expression value}
      (root : prepared.route.rootMapping = some expression)
      (quoted : VirtualRoot.Quoted value expression) :
      RootInput prepared ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value

 theorem RootInput.initial {prepared : Prepared} {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : RootInput prepared cell optional source value) : Dynamic.RootInitialValue cell (some source) := by
  cases root with
  | initialized => exact .initialized
  | virtual => exact .emptyMapping _ _

 theorem RootInput.normalize {prepared : Prepared} {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : RootInput prepared cell optional source value)
    (environment : Environment) (store : Store) (expression : Expr) (selected : Selects environment expression optional) :
    Evaluates environment store (normalizeRoot prepared expression) (.inRight .unit value) store := by
  cases root with
  | initialized => exact normalizeRoot_initialized prepared selected store
  | virtual generated quoted => exact VirtualRoot.normalize_absent prepared generated quoted environment store expression selected

 theorem generated_root {context : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared} {key valueType : TypeSystem.Ty}
    (generated : VirtualRoot.Generated context prepared.route key valueType)
    (functions : FunctionModel context.checked.catalog) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ header layout fallback,
      Fields context.checked registry functions mapping world key valueType [] header layout [] fallback ∧
      RootInput prepared ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit)
        (.mapping key valueType []) (Transport.carrier header fallback layout []) := by
  obtain ⟨expression, header, layout, fallback, root, quoted, fields⟩ := generated.fields functions mapping world
  exact ⟨header, layout, fallback, ⟨fields.metadata.extend extended, fields.identity, fields.keyProjection, fields.valueProjection,
    fields.registered, fields.stored.extend extended (.refl mapping) (.refl world), fields.default.extend extended (.refl mapping) (.refl world)⟩,
    .virtual root quoted⟩

 theorem getter_preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {leafType sourceType : TypeSystem.Ty} {leafCore : Ty}
    {cell : Dynamic.Cell} {source leaf : Dynamic.Value} {optional value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceType source value steps projections leaf count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ native finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧ Dynamic.ProjectionsRead (some source) projections (some leaf) ∧
      ValueRep checked registry functions mapping world leafType leaf native leafCore ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨native, finalStore, administrative, read, related, evaluated, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (value :: input :: environment) store (.var 0) (.second (.var 1)) (.var rfl) (.second (.var rfl))
  refine ⟨native, finalStore, administrative, root.initial, read, related, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  cases steps with
  | nil => exact (nonempty rfl).elim
  | cons step rest =>
    simp only [stepsEqual]
    exact .caseRight (root.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

 theorem setter_preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {sourceType : TypeSystem.Ty} {nativeType : Ty}
    {cell : Dynamic.Cell} {replacementSource source updated : Dynamic.Value} {replacement optional value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceType source value nativeType steps projections updated count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ native finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updated ∧
      ValueRep checked registry functions mapping world sourceType updated native nativeType ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) (.inRight .word native) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨native, finalStore, administrative, updated, related, evaluated, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (value :: input :: environment) store prepared.route.rootType (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
  refine ⟨native, finalStore, administrative, root.initial, updated, related, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  cases steps with
  | nil => exact (nonempty rfl).elim
  | cons step rest =>
    simp only [stepsEqual]
    exact .caseRight (root.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

 theorem getter_fault {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {cell : Dynamic.Cell} {source : Dynamic.Value} {optional value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : FaultTree checked registry functions mapping world prepared keys source value prepared.route.rootType steps projections reason token count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr)
    (readSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧ Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨finalStore, administrative, fault, readEvaluation, _, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (value :: input :: environment) store (.var 0) (.second (.var 1)) (.var 0) (.var rfl) (.second (.var rfl))
  refine ⟨finalStore, administrative, root.initial, fault, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (readSelected.evaluates store)
  cases steps with
  | nil => exact (nonempty rfl).elim
  | cons step rest =>
    simp only [stepsEqual]
    exact .caseRight (root.normalize _ store (.first (.var 0)) (.first (.var rfl))) readEvaluation

 theorem setter_fault {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {cell : Dynamic.Cell} {source : Dynamic.Value} {optional value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (root : RootInput prepared cell optional source value)
    (tree : FaultTree checked registry functions mapping world prepared keys source value prepared.route.rootType steps projections reason token count)
    (stepsEqual : prepared.steps = steps) (nonempty : steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (keyType : Ty) (argument : Expr) (replacement : Value)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some source) ∧ Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) (.inLeft prepared.route.rootType (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨finalStore, administrative, fault, _, updateEvaluation, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (value :: input :: environment) store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1))) (.var rfl) (.first (.second (.var rfl)))
  refine ⟨finalStore, administrative, root.initial, fault, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  cases steps with
  | nil => exact (nonempty rfl).elim
  | cons step rest =>
    simp only [stepsEqual]
    exact .caseRight (root.normalize _ store (.first (.var 0)) (.first (.var rfl))) updateEvaluation

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
