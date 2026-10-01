import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedHelpers

/-! Enough fuel and reflection of every completed run of the actual generated
mixed helpers. Runtime child evaluations are derived by the structural proofs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

structure FiniteRun (environment : Environment) (store : Store) (code : Expr) (value : Value) (after : Store) : Prop where
  completes : ∃ required, ∀ budget, required ≤ budget → runStateful budget (.initial code environment store) = .done value after
  reflects : ∀ budget actual actualStore, runStateful budget (.initial code environment store) = .done actual actualStore → actual = value ∧ actualStore = after

theorem FiniteRun.of_evaluates {environment : Environment} {store after : Store} {code : Expr} {value : Value}
    (evaluated : Evaluates environment store code value after) : FiniteRun environment store code value after :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

theorem getter_preserves_run {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
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
      FiniteRun environment store (.apply (getter prepared keyType) argument) (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨native, finalStore, administrative, initial, meaning, represented, evaluated, appended, counted⟩ :=
    getter_preserves root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument argumentSelected
  exact ⟨native, finalStore, administrative, initial, meaning, represented, .of_evaluates evaluated, appended, counted⟩

theorem setter_preserves_run {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
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
      FiniteRun environment store (.apply (setter prepared keyType) argument) (.inRight .word native) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨native, finalStore, administrative, initial, meaning, represented, evaluated, appended, counted⟩ :=
    setter_preserves root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument argumentSelected
  exact ⟨native, finalStore, administrative, initial, meaning, represented, .of_evaluates evaluated, appended, counted⟩

theorem getter_fault_run {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
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
      FiniteRun environment store (.apply (getter prepared keyType) argument) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨finalStore, administrative, initial, meaning, evaluated, appended, counted⟩ :=
    getter_fault root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument readSelected
  exact ⟨finalStore, administrative, initial, meaning, .of_evaluates evaluated, appended, counted⟩

theorem setter_fault_run {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
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
      FiniteRun environment store (.apply (setter prepared keyType) argument) (.inLeft prepared.route.rootType (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨finalStore, administrative, initial, meaning, evaluated, appended, counted⟩ :=
    setter_fault root tree stepsEqual nonempty faithful functionLeaves keyLength environment store keyType argument replacement argumentSelected
  exact ⟨finalStore, administrative, initial, meaning, .of_evaluates evaluated, appended, counted⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
