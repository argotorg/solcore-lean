import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceExecution
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.ReachedExpressionFaults
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceBitNot

/-!
# Compatible profile: bare assignments

Certificates, native typing, snapshots, right-hand sides and meaning of bare assignments and bit-not updates.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCertificates
/-! Bare assignment receipts are extracted from the actual place compiler.
The raw declared type and virtual mapping quote remain authenticated by describe;
no native type equality is used to recover source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open CompatibleMixedRoute CompatiblePlaceCompilerCertificates DataPlaceCertificates

structure Layout (compilation : SourceCoreCompatibleDataPlaces.Context) (prepared : Prepared) : Prop where
  steps : prepared.steps = []
  keys : prepared.keys = []
  sameType : prepared.route.rootType = prepared.route.leafType
  projected : compilation.checked.catalog.project prepared.route.rootSourceType = .ok prepared.route.rootType
  virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
    CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value
  ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none

private theorem nil_fields {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root [] position steps keys leaf) :
    steps = [] ∧ keys = [] ∧ leaf = root := by cases path; exact ⟨rfl, rfl, rfl⟩

theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {next lowered : Expr} {outputType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator (some rhs)
      outputType next reasonAt invalid invalidOperand missing = .ok lowered) :
    ∃ binder prepared index value,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      Layout compilation prepared ∧ expression fuel source scope rhs reasonAt = .ok value ∧
      value.type = prepared.route.leafType ∧
      (operator = .equal ∨ prepared.route.leafType = .word ∨ prepared.route.leafType = .integer ∧ operator.wordOnly = false) ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments []) value.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | present rhsAccepted rhsType =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      rw [bare] at path
      obtain ⟨steps, keys, rfl⟩ := nil_fields path
      rw [keys] at generated
      cases generated
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have types : route.rootType = route.leafType :=
        Except.ok.inj (description.rootProjected.symm.trans (by
          rw [← compilation.checked.catalog.project_runtimeType binder.scheme.body, description.selectedType,
            compilation.checked.catalog.project_runtimeType]
          exact description.leafProjected))
      refine ⟨binder, prepared, index, _, description.binding, rootEq, rootEq ▸ description.selectedType,
        by simpa only [routeEq] using lookup, ?_, rhsAccepted, by simpa only [routeEq] using rhsType.symm, ?_, by simp [routeEq]⟩
      · refine ⟨steps, keys, routeEq ▸ types, rootEq ▸ (routeEq ▸ description.rootProjected), ?_, ?_⟩
        · intro key value declared
          exact routeEq ▸ description.virtual key value (rootEq.symm.trans declared)
        · intro ordinary
          exact routeEq ▸ description.ordinary (fun key value same => ordinary key value (rootEq.trans same))
      · rcases operatorValid with ⟨same, _⟩ | word | integer
        · exact .inl same
        · exact .inr (.inl (routeEq ▸ word))
        · exact .inr (.inr (routeEq ▸ integer))

/-- Any virtual initializer is an actual pure quote; arbitrary expressions
cannot be smuggled into the empty-path normalization receipt. -/
theorem Layout.quoted {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {expression : Expr}
    (found : prepared.route.rootMapping = some expression) :
    ∃ value, CompatibleMapping.VirtualRoot.Quoted value expression := by
  classical
  by_cases mapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
  · obtain ⟨key, value, declared⟩ := mapping
    cases layout.virtual key value declared with
    | encoded accepted unchanged quoted root =>
      have same := Option.some.inj (root.symm.trans found)
      subst expression
      exact ⟨_, CompatibleMapping.VirtualRoot.quoted_of_quote quoted⟩
  · have absent := layout.ordinary (fun key value same => mapping ⟨key, value, same⟩)
    rw [absent] at found
    cases found

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentNative
/-! Syntax transport and finite native phases for bare assignments. Only the
pure virtual-root quote is invariant under renaming. RHS/continuation code and
its actual environment are renamed together; existing closure stores are never
assumed identical to evaluations in another environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

private theorem quote_rename {value : Value} {expression : Expr}
    (quoted : CompatibleMapping.VirtualRoot.Quoted value expression) (ξ : Renaming) :
    expression.rename ξ = expression := by induction quoted <;> simp_all [Expr.rename]

theorem getter_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (type : Ty) (ξ : Renaming) :
    (getter prepared type).rename ξ = getter prepared type := by
  cases found : prepared.route.rootMapping with
  | none => simp [getter, layout.steps, normalizeRoot, found, LanguageResult.success, Expr.rename, Renaming.lift]
  | some expression =>
    obtain ⟨value, quoted⟩ := layout.quoted found
    simp [getter, layout.steps, normalizeRoot, found, LanguageResult.success, Expr.rename,
      Renaming.lift, quoted.weaken, quote_rename quoted]

theorem setter_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (type : Ty) (ξ : Renaming) :
    (setter prepared type).rename ξ = setter prepared type := by
  simp [setter, layout.steps, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem modified_rename (type : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) (ξ : Renaming) :
    (modified type operator false (.var 1) (.var 0) invalid).rename ξ.lift.lift =
      modified type operator false (.var 1) (.var 0) invalid := by
  cases operator <;> simp [modified, LanguageResult.success, LanguageResult.failure,
    shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, Expr.rename, Renaming.lift]

theorem execute_rename {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) (index : Nat) (rhs next : Expr) (outputType : Ty)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) (ξ : Renaming) :
    (execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ =
      execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments []) (rhs.rename ξ) (next.rename ξ)
        outputType operator false invalid := by
  simp [execute, SourceCoreCalls.packArguments, LanguageResult.bind, LanguageResult.success,
    shift, List.range, List.range.loop, List.foldl, Expr.rename, Expr.weakenAt,
    getter_rename layout, setter_rename layout, modified_rename, DataPlaceGuard.rename_lift, Renaming.lift]

/-- The bare getter returns the optional normalized snapshot itself. Its input
normalization is either the real retained optional or an authenticated pure
mapping literal; both evaluations preserve the store. -/
theorem getter_evaluates {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {environment : Environment} {store : Store} {target : Location}
    {optional snapshot : Value} (read : store.read? target = some optional)
    (normalized : Evaluates (.pair optional .unit :: DataPlaceExecution.keysEnvironment prepared.route.rootType target .unit environment)
      store (normalizeRoot prepared (.first (.var 0))) snapshot store) :
    Evaluates (DataPlaceExecution.keysEnvironment prepared.route.rootType target .unit environment) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot) store := by
  simp only [getter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.var rfl)) (.inRight normalized)

theorem keys_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (shift 1 (SourceCoreCalls.packArguments []).expression) (.inRight .word .unit) store := by
  simp only [SourceCoreCalls.packArguments, shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
  exact .inRight .unit

/-- Getter/setter closures are constructed in this exact actual environment.
The bare setter selects the supplied replacement and makes no heap allocation. -/
theorem setter_evaluates {compilation : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    (layout : Layout compilation prepared) {environment : Environment} {store : Store} {target : Location}
    {optional : Value} (snapshot right replacement : Value) (read : store.read? target = some optional) :
    Evaluates (modifiedEnvironment prepared.route.rootType target .unit snapshot right replacement environment) store
      (.apply (setter prepared .unit) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word replacement) store := by
  simp only [setter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.pair (.var rfl) (.var rfl)))
    (.inRight (.second (.second (.var rfl))))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentSnapshot
/-! Empty projection paths retain an optional snapshot. A declared mapping can
supply an authenticated virtual empty value while its physical cell remains
absent. All native phases run in the actual renamed environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}

inductive SnapshotRep (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (sourceType : TypeSystem.Ty) (type : Ty) :
    Option Dynamic.Value → Value → Prop where
  | absent : SnapshotRep checked registry functions mapping world sourceType type none (.inLeft type .unit)
  | present {source value} (related : ValueRep checked registry functions mapping world sourceType source value type) :
      SnapshotRep checked registry functions mapping world sourceType type (some source) (.inRight .unit value)

theorem SnapshotRep.runtime_hasType {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (related : SnapshotRep checked registry functions mapping world sourceType type source value) :
    RuntimeValueHasType world value (OptionalCell.cellType type) ambient.definitions := by
  cases related with
  | absent => exact .inLeft .unit
  | present related => exact .inRight related.runtime_hasType

theorem SnapshotRep.extend {mapping nextMap : LocationMap} {world nextWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {source : Option Dynamic.Value} {value : Value}
    (related : SnapshotRep checked registry functions mapping world sourceType type source value)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld) :
    SnapshotRep checked registry functions nextMap nextWorld sourceType type source value := by
  cases related with
  | absent => exact .absent
  | present related => exact .present (related.extend (.refl _) maps worlds)

structure Snapshot (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (prepared : Prepared) (place : PlaceResolution) (environment : Dynamic.Environment) (actual : Environment)
    (heap : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping) (index : Nat) where
  location : Dynamic.Location
  target : Location
  cell : Dynamic.Cell
  optional : Value
  initial : Option Dynamic.Value
  value : Value
  lookup : Dynamic.Environment.LooksUp environment place.root location
  read : Dynamic.Heap.Reads heap location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world location target prepared.route.rootType
  nativeLookup : actual[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  nativeRead : store.read? target = some optional
  root : Dynamic.RootInitialValue cell initial
  represented : SnapshotRep checked registry functions mapping world prepared.route.rootSourceType prepared.route.rootType initial value
  normalized : Evaluates (.pair optional .unit :: keysEnvironment prepared.route.rootType target .unit actual)
    store (normalizeRoot prepared (.first (.var 0))) value store

variable {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}

abbrev Snapshot.resolved (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index) :
    Dynamic.ResolvedPlace := ⟨snapshot.location, snapshot.cell.type, place.type, [], snapshot.initial⟩

theorem Snapshot.resolves {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (bare : place.projections = []) :
    Dynamic.SourcePlaceResolves program context evidence source environment heap place snapshot.resolved heap :=
  .intro snapshot.lookup snapshot.read (bare ▸ .nil) snapshot.read snapshot.root .nil

theorem Snapshot.resolve_unique {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (bare : place.projections = []) {resolved : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment heap place resolved after) :
    resolved = snapshot.resolved ∧ after = heap := by
  cases trace with
  | intro lookup _ projections read initial selected =>
    rw [bare] at projections
    cases projections
    have same := lookup.functional snapshot.lookup
    cases same
    have same := read.functional snapshot.read
    cases same
    have selectedEq := selected.functional (.nil)
    have initialEq := initial.functional snapshot.root
    exact ⟨by simp only [Snapshot.resolved, selectedEq, initialEq], rfl⟩

theorem Snapshot.getter {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world index) :
    Evaluates (keysEnvironment prepared.route.rootType snapshot.target .unit actual) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0))) (.inRight .word snapshot.value) store :=
  getter_evaluates layout snapshot.nativeRead snapshot.normalized

theorem Snapshot.runtimeTyped {actualContext : Core.Context}
    (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world index)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    RuntimeEnvironmentHasTypes world (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      (OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: actualContext)
      ambient.definitions :=
  .cons snapshot.represented.runtime_hasType (.cons .unit (.cons (.cellRef snapshot.reference.typed) typed))

/-- Resolve the real lexical reference, then select its optional snapshot.
The source heap, native store, and location map are unchanged. -/
theorem snapshot_of_heap {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    {context : SourceSemantics.Context} {scope : Scope} {administrativeContext : Core.Context}
    {canonical : Environment} {ξ : Renaming}
    (layout : Layout compilation prepared) (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType) :
    Nonempty (Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index)) := by
  classical
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨location, cell, lookup, read, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
  have nativeLookup := agrees nativeLookup
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference read
  cases represented with
  | uninitialized projected =>
    by_cases isMapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
    · obtain ⟨key, value, declared⟩ := isMapping
      have sourceType := cellType.trans declared
      simp only at sourceType
      obtain ⟨native, root⟩ := CompatiblePlaceLiveRoot.RootRead.virtual (layout.virtual key value declared)
        extension (sourceType ▸ projected) (sourceType ▸ read) reference nativeRead
      exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        (sourceType.symm ▸ root.input.initial), .present (declared.symm ▸ root.payload), root.input.normalize _ store _ (.first (.var rfl))⟩⟩
    · have noVirtual := layout.ordinary (fun key value same => isMapping ⟨key, value, same⟩)
      refine ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
        .uninitialized ?_, .absent, ?_⟩⟩
      · rintro ⟨key, value, same⟩
        exact isMapping ⟨key, value, cellType.symm.trans same⟩
      · simpa only [normalizeRoot, noVirtual] using
          (Evaluates.first (Evaluates.var (index := 0) rfl) :
            Evaluates (.pair (.inLeft prepared.route.rootType .unit) .unit :: keysEnvironment prepared.route.rootType target .unit actual)
              store (.first (.var 0)) (.inLeft prepared.route.rootType .unit) store)
  | initialized related =>
    have root := CompatiblePlaceLiveRoot.RootRead.initialized read reference nativeRead related
    exact ⟨⟨_, _, _, _, _, _, lookup, read, cellType, reference, nativeLookup, nativeRead,
      .initialized, .present (cellType ▸ related), root.input.normalize _ store _ (.first (.var rfl))⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentRhs
/-! Typed RHS transport for a bare assignment uses its real renamed reference,
saved optional snapshot, and arbitrary administrative captures. Semantic phase
receipts below are outputs of the child induction, not static assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}

variable (snapshot : Snapshot checked registry functions prepared place environment actual heap store mapping world (ξ index))

structure RhsResult (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
    store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : ResultRepresents (payloadModel checked registry functions) finalMap finalWorld node.type lowered.type faults outcome value
  heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore
  maps : LocationMap.Extends mapping finalMap
  worlds : WorldExtends world finalWorld
  frame : AdministrativePreserved mapping store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend heap after
  latest : Nonempty (CompatiblePlaceRhs.Latest checked registry functions finalMap finalWorld prepared snapshot.resolved snapshot.target after finalStore)

private theorem latest_of_heap {nextMap : LocationMap} {nextWorld : StoreTyping} {after : Dynamic.Heap} {finalStore : Store}
    (heaps : HeapRepresents checked registry functions nextMap nextWorld after finalStore)
    (maps : LocationMap.Extends mapping nextMap) (worlds : WorldExtends world nextWorld)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    Nonempty (CompatiblePlaceRhs.Latest checked registry functions nextMap nextWorld prepared snapshot.resolved snapshot.target after finalStore) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ snapshot.read
  have reference := snapshot.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference read
  exact ⟨⟨cell, optional, read, sameType.trans snapshot.type, reference, nativeRead, represented⟩⟩

variable {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}

theorem rhs_preserves
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) trace
  refine ⟨value, finalStore, finalMap, finalWorld, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem rhs_reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
        (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, finalMap, finalWorld, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap snapshot heaps maps worlds metadata⟩

/-- Strip only the actually executed reference, empty key tuple and getter.
The remaining computation evaluates the renamed RHS once. -/
theorem snapshot_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    CoreProof.ContinuationAgreement actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) rhs next outputType operator false invalid).rename ξ)
      (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual) store
      (LanguageResult.bind outputType (shift 3 (rhs.rename ξ))
        (CompatiblePlaceRhsReflection.remainder prepared .unit (next.rename ξ) outputType operator invalid)) := by
  rw [execute_rename layout]
  exact (CoreProof.ContinuationAgreement.letE (.var snapshot.nativeLookup)).trans
    ((CoreProof.ContinuationAgreement.bind (keys_evaluates _ store)).trans
      (CoreProof.ContinuationAgreement.bind (snapshot.getter layout)))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentCommit
/-! A bare transaction either fails at the optional snapshot modifier or
writes its represented replacement to the post-RHS live cell. The generated
setter and final store operation run in their actual captured environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

/-- Both modifier outcomes are constructed from authenticated saved/RHS
values. An absent compound snapshot fails after the RHS has completed. -/
theorem modifier_total {sourceType : TypeSystem.Ty} {type : Ty} {initial : Option Dynamic.Value}
    {snapshot rightCore : Value} {right : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog functions identities)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer ∧ operator.wordOnly = false)
    (saved : SnapshotRep checked registry functions mapping world sourceType type initial snapshot)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshot)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    (Dynamic.AssignmentOperandsInvalid operator initial right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inLeft type (.word invalid)) store) ∨
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      (Dynamic.AssignmentValueApplies operator initial right result ∨
        ∃ operation, binaryOperator (type = .integer) operator = some ⟨operation, true⟩ ∧ rightCore = .word Word.zero ∧
          Dynamic.AssignmentOperandsPanic operator initial right SourceCorePanics.divisionByZero) ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  cases saved with
  | present related =>
    obtain ⟨result, value, related, evaluated, outcome⟩ :=
      CompatiblePlaceModifier.initialized_outcome observations profile related rightRep snapshotSelected rightSelected store invalid
    exact .inr ⟨result, value, related, outcome.imp (fun applied => applied.1) id, evaluated⟩
  | absent =>
    by_cases equal : operator = .equal
    · subst operator
      exact .inr ⟨right, rightCore, rightRep, .inl (.equal _ _), .inRight (rightSelected.evaluates store)⟩
    · refine .inl ⟨.uninitialized equal, ?_⟩
      cases operator <;> first
      | exact (equal rfl).elim
      | (by_cases integer : type = .integer <;>
          simp only [binaryOperator, integer, ite_true, ite_false, modified] <;>
          exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word))

theorem cell_initial {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (related : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  classical
  cases related with
  | initialized _ => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ =>
    by_cases isMapping : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := isMapping
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨_, .uninitialized isMapping⟩

def writtenContext (prepared : Prepared) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.rootType :: prepared.route.rootType ::
    OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: context

variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {index : Nat} {ξ : Renaming}
  {faults : FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- A successful RHS and modifier produce an exact whole-prefix agreement,
including typed seven slots for the real renamed continuation. -/
theorem commit_with_write {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (bare : place.projections = [])
    {right updated : Dynamic.Value} {rightValue updatedValue : Value} {rhsHeap : Dynamic.Heap}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {operator : Syntax.ValueAssignOp} {invalid : Word}
    (rhs : RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot (.value right) rhsHeap
        (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType)
    (replacement : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
    (applied : Dynamic.AssignmentValueApplies operator snapshot.initial right updated)
    (modified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
      (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
      (.inRight .word updatedValue) rhsStore)
    (passes : SourceCoreDataPlaces.Passes (binaryOperator (prepared.route.leafType = .integer) operator) rightValue)
    {actualContext : Core.Context} (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ after finalStore,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment heap place id updated after ∧
      Dynamic.Heap.Writes rhsHeap snapshot.location (some updated) after ∧
      HeapRepresents compilation.checked registry functions rhsMap rhsWorld after finalStore ∧
      AdministrativePreserved mapping store rhsMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      RuntimeEnvironmentHasTypes rhsWorld
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        (writtenContext prepared actualContext) ambient.definitions ∧
      AdministrativePreserved rhsMap rhsStore rhsMap finalStore ∧
      Dynamic.HeapMetadataExtend rhsHeap after ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨latest⟩ := rhs.latest
  obtain ⟨initial, initialValue⟩ := cell_initial latest.related
  have written := DataPlaceCommitReflection.source_writes latest.read updated
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    rhs.heaps.write_initialized latest.reference latest.read (latest.type.symm ▸ replacement) written
  have trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment heap place id updated
        ⟨rhsHeap.cells.set snapshot.location.index {latest.cell with value := some updated}⟩ := by
    cases rhs.trace with
    | value right =>
      exact .intro (snapshot.resolves bare) right
        (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written)
  refine ⟨_, finalStore, trace, written, finalHeaps, rhs.frame.trans writeFrame, rhs.metadata.trans (.of_write written), ?_, writeFrame, .of_write written, ?_⟩
  · exact .cons .unit (.cons replacement.runtime_hasType (.cons replacement.runtime_hasType
      (.cons rightRep.runtime_hasType (.cons (snapshot.represented.extend rhs.maps rhs.worlds).runtime_hasType
        (.cons .unit (.cons (.cellRef latest.reference.typed) (actualTyped.weaken rhs.worlds)))))))
  · intro next outputType
    exact (snapshot_prefix layout snapshot _ _ _ _ _).trans
      ((ContinuationAgreement.bind rhs.evaluated).trans
        ((ContinuationAgreement.bind modified).trans
          ((ContinuationAgreement.bind (setter_evaluates layout snapshot.value rightValue updatedValue latest.nativeRead)).trans
            ((DataPlaceGuard.agreement passes).trans
              (ContinuationAgreement.letE (.storeCell (.var rfl) latest.nativeRead (.inRight (.var rfl)) coreWritten))))))

theorem commit {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
    (layout : Layout compilation prepared)
    (snapshot : Snapshot compilation.checked registry functions prepared place environment actual heap store mapping world (ξ index))
    (bare : place.projections = [])
    {right updated : Dynamic.Value} {rightValue updatedValue : Value} {rhsHeap : Dynamic.Heap}
    {rhsStore : Store} {rhsMap : LocationMap} {rhsWorld : StoreTyping} {operator : Syntax.ValueAssignOp} {invalid : Word}
    (rhs : RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot (.value right) rhsHeap
        (.inRight .word rightValue) rhsStore rhsMap rhsWorld)
    (rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType right rightValue prepared.route.rootType)
    (replacement : ValueRep compilation.checked registry functions rhsMap rhsWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
    (applied : Dynamic.AssignmentValueApplies operator snapshot.initial right updated)
    (modified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
      (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
      (.inRight .word updatedValue) rhsStore)
    (passes : SourceCoreDataPlaces.Passes (binaryOperator (prepared.route.leafType = .integer) operator) rightValue)
    {actualContext : Core.Context} (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions) :
    ∃ after finalStore,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment heap place id updated after ∧
      Dynamic.Heap.Writes rhsHeap snapshot.location (some updated) after ∧
      HeapRepresents compilation.checked registry functions rhsMap rhsWorld after finalStore ∧
      AdministrativePreserved mapping store rhsMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      RuntimeEnvironmentHasTypes rhsWorld
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        (writtenContext prepared actualContext) ambient.definitions ∧
      ∀ next outputType, ContinuationAgreement actual store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (writtenEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue updatedValue updatedValue actual)
        finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨after, finalStore, trace, written, heaps, frame, metadata, typed, _, _, agreement⟩ :=
    commit_with_write layout snapshot bare rhs rightRep replacement applied modified passes actualTyped
  exact ⟨after, finalStore, trace, written, heaps, frame, metadata, typed, agreement⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentMeaning
/-! Completed bare assignment code reconstructs the independent source
transaction or fault. RHS meaning is typed and instantiated in the actual
three temporary slots; successful continuation typing names its seven values.
A concrete expression-tree consumer discharges the child interface separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof

inductive Result (compilation : SourceCoreCompatibleDataPlaces.Context) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions} (functions : FunctionModel compilation.checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FaultRep) (prepared : Prepared) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (actual : Environment) (actualContext : Core.Context) (ξ : Renaming)
    (next : Expr) (outputType : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap} {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (result : value = .inLeft outputType (.word token)) (represented : faults reason token)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
        rhs actual actualContext ξ next outputType value finalStore
  | success {updated : Dynamic.Value} {updatedValue : Value} {after : Dynamic.Heap} {commitStore : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (represented : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updated updatedValue prepared.route.rootType)
      (heaps : HeapRepresents compilation.checked registry functions finalMap finalWorld after commitStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap commitStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (writtenContext prepared actualContext) ambient.definitions)
      (continuation : Evaluates (slots ++ actual) commitStore (shift 7 (next.rename ξ)) value finalStore) :
      Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
        rhs actual actualContext ξ next outputType value finalStore

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}

/-- Finite reflection needs no source RHS trace and no chosen child execution.
The actual completed code is the sole runtime premise. -/
theorem reflects_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    [FunctionCalls.FaultTokens faults] (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase :=  snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  have remaining := phase.unwrap completed
  cases remaining with
  | caseLeft evaluated _ =>
    obtain ⟨outcome, after, finalMap, finalWorld, result⟩ :=
      rhs_reflects snapshot meaning generated found environments heaps locals agrees actualTyped evaluated
    cases related : result.represented with
    | fault token =>
      have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed failed
      cases result.trace with
      | fault fault =>
        exact .fault (.rhs (snapshot.resolves bare) fault) rfl token result.heaps result.maps result.worlds result.frame result.metadata
  | caseRight evaluated remaining =>
    rename_i rhsStore rightValue
    obtain ⟨outcome, after, finalMap, finalWorld, result⟩ :=
      rhs_reflects snapshot meaning generated found environments heaps locals agrees actualTyped evaluated
    cases related : result.represented with
    | value payload =>
      rename_i right
      rename_i rhsStore
      have rightRep : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      have modifier := modifier_total observations profile saved rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rcases modifier with ⟨invalidOperands, failed⟩ | ⟨updated, updatedValue, replacement, outcome, modified⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
          simpa only [layout.sameType] using failed
        have evaluation := phase.wrap (LanguageResult.bind_success outputType result.evaluated
          (LanguageResult.bind_failure outputType failed))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluation
        obtain ⟨latest⟩ := result.latest
        obtain ⟨initial, initialized⟩ := cell_initial latest.related
        cases result.trace with
        | value rhsTrace =>
          exact .fault (.operands (snapshot.resolves bare) rhsTrace latest.read
            (latest.type.trans snapshot.type.symm) initialized .nil invalidOperands) rfl (invalidToken _ _ invalidOperands)
            result.heaps result.maps result.worlds result.frame result.metadata
      · rcases outcome with applied | ⟨operation, selected, zero, panics⟩
        · have passes := CompatiblePlaceModifier.passes_of_applies observations profile rightRep applied
            (prepared.route.leafType = .integer)
          obtain ⟨after, commitStore, trace, _, finalHeaps, frame, metadata, typed, agreement⟩ :=
            commit layout snapshot bare result rightRep replacement applied (by simpa only [layout.sameType] using modified)
              passes actualTyped
          exact .success trace replacement finalHeaps result.maps result.worlds frame metadata
            (slots := [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
              .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed
            ((agreement next outputType).unwrap completed)
        · -- The setter runs and the check fails, so the source panics without a write.
          have selected : binaryOperator (prepared.route.leafType = .integer) operator = some ⟨operation, true⟩ := by
            simpa only [layout.sameType] using selected
          subst zero
          have nativeModified : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value
              (.word Word.zero) actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType
                (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
              (.inRight .word updatedValue) rhsStore := by
            simpa only [layout.sameType] using modified
          obtain ⟨latest⟩ := result.latest
          obtain ⟨initial, initialized⟩ := cell_initial latest.related
          have evaluation := phase.wrap (LanguageResult.bind_success outputType result.evaluated
            (LanguageResult.bind_success outputType nativeModified
              (LanguageResult.bind_success outputType
                (setter_evaluates layout snapshot.value (.word Word.zero) updatedValue latest.nativeRead)
                (DataPlaceGuard.panic_of_selected selected))))
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluation
          cases result.trace with
          | value rhsTrace =>
            exact .fault (.panic (snapshot.resolves bare) rhsTrace latest.read
              (latest.type.trans snapshot.type.symm) initialized .nil panics) rfl (FunctionCalls.FaultTokens.panic _)
              result.heaps result.maps result.worlds result.frame result.metadata

/-- Compatibility entry point retaining the original unconditional token law. -/
theorem reflects
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    [FunctionCalls.FaultTokens faults] (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  exact reflects_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped slot rootTyped (AssignmentOperandDiagnostics.of_unconditional invalidToken) completed

end Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignment
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
/-! Actual bare-root, absent-RHS lowering has no source expression children.
The numeric profile below concerns retained IR; source compound admission is
still Word-only. Raw source type views come from describe, not Core type equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues
open CompatibleMixedRoute CompatiblePlaceCompilerCertificates DataPlaceCertificates

structure Layout (prepared : Prepared) : Prop where
  steps : prepared.steps = []
  ordinary : prepared.route.rootMapping = none
  sameType : prepared.route.rootType = prepared.route.leafType

private theorem nil_fields {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {position : Nat} {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root [] position steps keys leaf) :
    steps = [] ∧ keys = [] ∧ leaf = root := by
  cases path
  exact ⟨rfl, rfl, rfl⟩

theorem of_lower {compilation : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {operator : Syntax.ValueAssignOp} {next lowered : Expr} {outputType : Ty}
    {invalid invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (bare : assignment.target.projections = [])
    (profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer)
    (accepted : lower compilation compilation.checked.signatures expression fuel source scope site assignment operator none
      outputType next reasonAt invalid invalidOperand missing = .ok lowered) :
    ∃ binder prepared index,
      rootBinder source assignment.target.root = .ok binder ∧
      prepared.route.rootSourceType = binder.scheme.body ∧
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType assignment.target.type ∧
      SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, prepared.route.rootType) ∧
      Layout prepared ∧
      lowered = execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit) next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) true invalidOperand := by
  cases generated_of_lower accepted with
  | intro route prepared index codes value described lookup preparedBy generated _ rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, leaf, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeEq, _, path⟩ := description.prepared preparedBy
      rw [bare] at path
      obtain ⟨steps, keys, rfl⟩ := nil_fields path
      rw [keys] at generated
      cases generated
      have rootEq : prepared.route.rootSourceType = binder.scheme.body := routeEq ▸ description.rootSource
      have view := description.selectedType
      have notMapping : ∀ k v, binder.scheme.body ≠ .mapping k v := by
        intro k v same
        rcases profile with word | integer
        · rw [same, word] at view; cases view
        · rw [same, integer] at view; cases view
      have types : route.rootType = route.leafType :=
        Except.ok.inj (description.rootProjected.symm.trans (by
          rw [← compilation.checked.catalog.project_runtimeType binder.scheme.body, view,
            compilation.checked.catalog.project_runtimeType]
          exact description.leafProjected))
      refine ⟨binder, prepared, index, description.binding, rootEq, rootEq ▸ view,
        by simpa only [routeEq] using lookup, ?_, by simp [routeEq]⟩
      exact ⟨steps, routeEq ▸ description.ordinary notMapping, routeEq ▸ types⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
/-! Bare-root execute prefixes do not allocate or evaluate source children.
An absent root fails at the unary modifier, before setter, write or continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload CompatibleHeap
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {prepared : Prepared} {environment : Environment} {store : Store}
  {target : Location} {optional : Value}

theorem keys_evaluates (environment : Environment) (store : Store) :
    Evaluates environment store (shift 1 (SourceCoreCalls.packArguments []).expression) (.inRight .word .unit) store := by
  simp only [SourceCoreCalls.packArguments, shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
  exact .inRight .unit

theorem getter_evaluates (layout : Layout prepared)
    (read : store.read? target = some optional) :
    Evaluates (keysEnvironment prepared.route.rootType target .unit environment) store
      (.apply (getter prepared .unit) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inRight .word optional) store := by
  simp only [getter, layout.steps, normalizeRoot, layout.ordinary]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.var rfl))
    (.inRight (.first (.var rfl)))

theorem setter_evaluates (layout : Layout prepared) (snapshot replacement : Value)
    (read : store.read? target = some optional) :
    Evaluates (modifiedEnvironment prepared.route.rootType target .unit snapshot .unit replacement environment) store
      (.apply (setter prepared .unit) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (.inRight .word replacement) store := by
  simp only [setter, layout.steps]
  exact .apply .lambda (.pair (.loadCell (.var rfl) read) (.pair (.var rfl) (.var rfl)))
    (.inRight (.second (.second (.var rfl))))

theorem prefix_plug (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some optional)
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value} {after : Store}
    (tail : Evaluates (snapshotEnvironment prepared.route.rootType target .unit optional environment) store
      (CompatiblePlacePrefixReflection.remainder prepared .unit (LanguageResult.success .unit) next outputType operator true invalid)
      result after) :
    Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after := by
  exact .letE (.var lookup) (LanguageResult.bind_success _ (keys_evaluates _ _)
    (LanguageResult.bind_success _ (getter_evaluates layout read) tail))

/-- Inversion recovers the actual continuation after the effect-free reference,
Unit key bundle and live load. Both omitted source-child phases stay absent. -/
theorem prefix_reflects (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some optional)
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    Evaluates (snapshotEnvironment prepared.route.rootType target .unit optional environment) store
      (CompatiblePlacePrefixReflection.remainder prepared .unit (LanguageResult.success .unit) next outputType operator true invalid)
      result after := by
  cases completed with
  | letE reference rest =>
    obtain ⟨same, stores⟩ := evaluation_deterministic reference (Evaluates.var lookup)
    subst_vars
    cases rest with
    | caseLeft keys failed =>
      have same := (evaluation_deterministic keys (keys_evaluates _ _)).1
      cases same
    | caseRight keys rest =>
      obtain ⟨same, stores⟩ := evaluation_deterministic keys (keys_evaluates _ _)
      cases same
      subst_vars
      cases rest with
      | caseLeft getter failed =>
        have same := (evaluation_deterministic getter (getter_evaluates layout read)).1
        cases same
      | caseRight getter rest =>
        obtain ⟨same, stores⟩ := evaluation_deterministic getter (getter_evaluates layout read)
        cases same
        subst_vars
        exact rest

/-- An uninitialized bare root is a unary-operand failure, not a projected-read
fault. No store cell is changed, even when the continuation would have effects. -/
theorem absent_evaluates (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid)
      (.inLeft outputType (.word invalid)) store := by
  apply prefix_plug layout lookup read
  apply LanguageResult.bind_success _ (show Evaluates _ _ (shift 3 (LanguageResult.success .unit))
    (.inRight .word .unit) store from by
      simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
      exact .inRight .unit)
  apply LanguageResult.bind_failure
  simp only [modified, if_true]
  exact .caseLeft (.var rfl) (.inLeft .word)

/-- Completed absent-root runs return exactly that failure and the original
store; no assumption about a source or native child execution is used. -/
theorem absent_reflects (layout : Layout prepared) {index : Nat}
    (lookup : environment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (read : store.read? target = some (.inLeft prepared.route.rootType .unit))
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value} {after : Store}
    (completed : Evaluates environment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    result = .inLeft outputType (.word invalid) ∧ after = store :=
  evaluation_deterministic completed (absent_evaluates layout lookup read next outputType operator invalid)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
/-! Bare numeric snapshot assignments on the common compatible heap. The
source traces and native modifier/setter/write are constructed from a live
represented cell, without any source-child induction hypothesis. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}

private theorem nonmapping {type : TypeSystem.Ty}
    (profile : SourceCoreRawMetadata.runtimeType type = .word ∨ SourceCoreRawMetadata.runtimeType type = .integer) :
    ∀ key value, type ≠ .mapping key value := by
  intro key value same
  subst type
  rcases profile with impossible | impossible <;> cases impossible

theorem resolves {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {place : PlaceResolution} {cell : Dynamic.Cell}
    {initial : Option Dynamic.Value}
    (bare : place.projections = []) (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (read : Dynamic.Heap.Reads heap location cell) (root : Dynamic.RootInitialValue cell initial) :
    Dynamic.SourcePlaceResolves program context evidence source environment heap place
      ⟨location, cell.type, place.type, [], initial⟩ heap := by
  exact .intro lookup read (bare ▸ .nil) read root .nil

/-- A present numeric root creates a single mapped write. Getter and setter
allocate no administrative cells, so both map and world are unchanged. -/
theorem initialized_commit (layout : Layout prepared)

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    {sourceValue : Dynamic.Value} {value : Value} {environment : Environment}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨prepared.route.rootSourceType, some sourceValue, none⟩)
    (native : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world prepared.route.rootSourceType sourceValue value prepared.route.rootType)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    ∃ replacement after,
      Dynamic.BitNotSnapshot (some sourceValue) replacement ∧
      Dynamic.Heap.Writes heap location (some replacement) after ∧
      Nonempty (CompatiblePlaceBitNotCommit.Execution checked registry functions prepared [] environment store mapping world
        target [] value heap after replacement operator invalid) := by
  obtain ⟨replacement, changed, related, applies, modified, _⟩ :=
    CompatiblePlaceNumericBitNotModifier.success profile represented
      (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit value) .unit environment)
      (rhs := .var 0) (.var (index := 1) rfl) operator store invalid
  have written := DataPlaceCommitReflection.source_writes read replacement
  obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read related written
  refine ⟨replacement, _, applies, written, ⟨{
    replacement := changed
    value := changed
    helperStore := store
    finalStore := finalStore
    finalWorld := world
    related := related
    heaps := finalHeaps
    worlds := .refl _
    frame := frame
    metadata := .of_write written
    modified := ?_
    setter := ?_
    read := ⟨_, native⟩
    written := coreWritten }⟩⟩
  · simpa only [← layout.sameType, packValues] using modified
  · exact CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit value) changed native

/-- Every live bare numeric root has exactly one generated phase: an absent
operand failure, or a source snapshot update with a real native commit. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
    {place : PlaceResolution} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {faults : FaultRep} {index : Nat}
    (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {invalid : Word} {result : Value} {after : Store}
    (token : faults (.invalidUnaryOperand .bitNot) invalid)
    (completed : Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
      (LanguageResult.success .unit) next outputType operator true invalid) result after) :
    CompatiblePlaceBitNotMeaning.Result compilation.checked registry functions program context evidence source faults
      place environment coreEnvironment heap store mapping world next outputType result after := by
  obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, cell, sourceLookup, sourceRead, cellType, _⟩ := locals.lookup schemeLookup
  have cellType := cellType.trans bodyEq
  obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible sourceLookup slot
  obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference sourceRead
  cases represented with
  | uninitialized projected =>
    have initial : Dynamic.RootInitialValue _ none := .uninitialized (by
      rintro ⟨key, value, same⟩
      exact nonmapping profile key value (cellType.symm.trans same))
    have trace := resolves (program := program) (context := context) (evidence := evidence) (source := source)
      bare sourceLookup sourceRead initial
    obtain ⟨resultEq, storeEq⟩ := CompatibleBareBitNotNative.absent_reflects layout nativeLookup nativeRead completed
    subst after
    exact .fault (.uninitialized trace rfl) resultEq token heaps (.refl _) (.refl _) (.refl _ _) (.refl _)
  | @initialized type _payload sourceValue value related =>
    simp only at cellType
    subst type
    have trace := resolves (program := program) (context := context) (evidence := evidence) (source := source)
      bare sourceLookup sourceRead Dynamic.RootInitialValue.initialized
    obtain ⟨replacement, sourceAfter, applies, written, ⟨commit⟩⟩ :=
      initialized_commit layout profile heaps reference sourceRead nativeRead related operator invalid
    have update : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
        environment heap place replacement sourceAfter :=
      .intro trace (.intro sourceRead rfl .initialized (.leaf applies) written)
    have tail := CompatibleBareBitNotNative.prefix_reflects layout nativeLookup nativeRead completed
    exact .committed update commit.heaps (.refl _) commit.worlds commit.frame commit.metadata
      (slots := [.unit, commit.value, commit.replacement, .unit, .inRight .unit value,
        .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) target]) rfl (commit.reflects tail)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleProgramAssignmentPreparation
/-! Actual compatible preparation retains the entire original program diagnostic
prefix while adding projected-place and missing-key diagnostics. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CompatibleProgramAssignmentPreparation
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

private def Inventory (_capacity _next : Nat) (_indices : List SourceCoreDataFaultSites.IndexSite)
    (_places : List SourceCoreDataPlaceFaultSites.Site) (_missing : List MissingSite)
    (original fixed : List (Word × Diagnostic)) : Prop := ∃ suffix, fixed = original ++ suffix

private theorem Inventory.append_missing {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed) {site : MissingSite} :
    Inventory capacity next indices places (missing ++ [site]) original fixed := inventory

private theorem Inventory.index_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {index : SourceCoreDataFaultSites.IndexSite} :
    Inventory capacity (next + capacity + 1) (indices ++ [index]) places missing original fixed := inventory

private theorem Inventory.place_range {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List (Word × Diagnostic)} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} {type : TypeSystem.Ty}
    (_kind : place.missingType = some type) :
    Inventory capacity (next + capacity + 1) indices (places ++ [place]) missing original fixed := inventory

private theorem Inventory.place_fixed {capacity next : Nat} {indices : List SourceCoreDataFaultSites.IndexSite}
    {places : List SourceCoreDataPlaceFaultSites.Site} {missing : List MissingSite}
    {original : List (Word × Diagnostic)} {fixed : List (Word × Diagnostic)}
    (inventory : Inventory capacity next indices places missing original fixed)
    {place : SourceCoreDataPlaceFaultSites.Site} (_number : place.reason.val = next)
    (_error : place.diagnostic.error = .invalidPlaceProjection) :
    Inventory capacity (next + 1) indices (places ++ [place]) missing original
      (fixed ++ [(place.reason, place.diagnostic)])  := by
  obtain ⟨suffix, same⟩ := inventory
  exact ⟨suffix ++ [(place.reason, place.diagnostic)], by rw [same, List.append_assoc]⟩

private theorem word_number {number : Nat} {reason : Word}
    (accepted : (match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason) :
    reason.val = number := by
  split at accepted
  · rename_i converted
    have same := Except.ok.inj accepted
    subst reason
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  · cases accepted

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem expression_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : ExpressionNode} {mapping key : ExpressionId}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {seen : List ExpressionId}
    {original : List (Word × Diagnostic)} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic) × List ExpressionId)}
    (ran : (do
      let baseNode ← match source.lookupExpression? mapping with
        | some base => pure base
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression mapping))
      let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
        | .mapping keyType valueType => pure (keyType, valueType)
        | _ => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      unless SourceCoreRawMetadata.runtimeType node.type = valueType do
        throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression node.id))
      pure (.yield (next, indices, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩],
        fixed, node.id :: seen))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 updated.2.1 updated.2.2.1 updated.2.2.2.1
        original updated.2.2.2.2.1 := by
  split at ran
  · rename_i base found
    try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    split at ran
    · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      split at ran
      · exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
      · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
    · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
      cases ran
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem place_resume {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution} {key : ExpressionId} {valueType : TypeSystem.Ty}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)}
    {original : List (Word × Diagnostic)} {reason : Word}
    (inventory : Inventory capacity next indices places missing original fixed)
    {outcome : ForInStep (Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite)}
    (ran : (do
      let keyNode ← match source.lookupExpression? key with
        | some keyNode => pure keyNode
        | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
      pure (.yield (next, places,
        missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
          keyNode.type, valueType, node.span, reason⟩]))) = (Except.ok outcome : Except SourceCoreCompatibleDataPlaceFaultSites.Error _)) :
    ∃ updated, outcome = .yield updated ∧
      Inventory capacity updated.1 indices updated.2.1 updated.2.2 original fixed := by
  split at ran
  · try dsimp only [pure, Except.pure, bind, Except.bind] at ran
    exact ⟨_, (Except.ok.inj ran).symm, inventory.append_missing⟩
  · change (Except.error _ : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
    cases ran

private theorem route_ranges {capacity next : Nat} {owner : Key} {source : TypedSource}
    {node : StatementNode} {assignment : AssignmentResolution}
    {indices : List SourceCoreDataFaultSites.IndexSite} {places : List SourceCoreDataPlaceFaultSites.Site}
    {missing : List MissingSite} {fixed : List (Word × Diagnostic)} {original : List (Word × Diagnostic)}
    {steps : List SourceCoreCompatibleDataPlaces.Step}
    {issue : Nat → Except SourceCoreCompatibleDataPlaceFaultSites.Error Word}
    (_wordEq : ∀ number, issue number = match Word.ofNat? number with
      | some value => Except.ok value
      | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted)
    (inventory : Inventory capacity next indices places missing original fixed)
    {result : Nat × List SourceCoreDataPlaceFaultSites.Site × List MissingSite}
    (ran : forIn steps (next, places, missing) (fun step current => do
      let mut next := current.1
      let mut places := current.2.1
      let mut missing := current.2.2
      match step with
      | .index _ key valueType =>
          let reason ← match places.find? (fun previous => decide
              (previous.owner = owner ∧ previous.location = .occurrence node.id.occurrence ∧
               previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
            | some previous => pure previous.reason
            | none => do
                let reason ← issue next
                discard <| issue (next + (capacity + 1) - 1)
                next := next + (capacity + 1)
                let diagnostic : Diagnostic := ⟨.typeMismatch valueType none,
                  .occurrence node.id.occurrence, some node.span⟩
                places := places ++ [⟨owner, .occurrence node.id.occurrence, assignment.target.root,
                  some valueType, reason, diagnostic⟩]
                pure reason
          let keyNode ← match source.lookupExpression? key with
            | some keyNode => pure keyNode | none => throw (SourceCoreCompatibleDataPlaceFaultSites.Error.lowering (.missingExpression key))
          missing := missing ++ [⟨owner, .occurrence node.id.occurrence, some assignment.target.root,
            keyNode.type, valueType, node.span, reason⟩]
      | _ => pure ()
      pure (.yield (next, places, missing))) = Except.ok result) :
    Inventory capacity result.1 indices result.2.1 result.2.2 original fixed := by
  apply CompatibleMemberCertificates.forIn_preserves ran (fun _ current =>
    Inventory capacity current.1 indices current.2.1 current.2.2 original fixed) inventory
  intro seen step remaining current outcome _split previous ran
  obtain ⟨next, places, missing⟩ := current
  dsimp only at ran
  cases step with
  | member => exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  | index layout key valueType =>
    dsimp only at ran
    split at ran
    · rename_i _prior _found
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      exact place_resume previous ran
    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
      have issued := previous.place_range (place := ⟨owner, .occurrence node.id.occurrence,
        assignment.target.root, some valueType, reason,
        ⟨.typeMismatch valueType none, .occurrence node.id.occurrence, some node.span⟩⟩) rfl
      simp only [Nat.add_assoc] at issued
      exact place_resume issued ran

theorem prepare_prefix {context : SourceCoreCompatibleDataPlaceFaultSites.Context} {plan : Plan} {root : Key}
    {sources : List (Key × TypedSource)} {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    (accepted : SourceCoreCompatibleDataPlaceFaultSites.prepare context plan root sources = .ok program) :
    ∃ base, SourceCoreProgramFaultSites.prepare plan root = .ok base ∧
      ∃ suffix, program.fixed = base.rootTable.additional ++ suffix := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.prepare at accepted
  obtain ⟨base, baseAccepted, accepted⟩ := bind_ok accepted
  obtain ⟨state, loop, accepted⟩ := bind_ok accepted
  let original := base.rootTable.additional
  let capacity := context.registry.limits.maxEntries
  let invariant := fun (_ : List (Key × TypedSource))
    (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
      List MissingSite × List (Word × Diagnostic)) =>
    Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2
  have generated : invariant (plan.specializations.map (fun specialized =>
      (specialized.key, specialized.function.typedBody)) ++ sources) state := by
    apply CompatibleMemberCertificates.forIn_preserves loop invariant
    · change Inventory capacity _ [] [] [] original base.rootTable.additional
      exact ⟨[], (List.append_nil _).symm⟩
    · intro seen item remaining current outcome _split previous ran
      obtain ⟨next, indices, places, missing, fixed⟩ := current
      obtain ⟨owner, source⟩ := item
      dsimp only at ran
      by_cases ownerMismatch : source.owner ≠ owner.declaration
      · rw [if_pos ownerMismatch] at ran
        change (Except.error (.sourceOwnerMismatch owner.declaration source.owner) :
          Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
        cases ran
      · rw [if_neg ownerMismatch] at ran
        obtain ⟨current, nodesLoop, finished⟩ := bind_ok ran
        refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
        let nodeInvariant := fun (_ : List Node)
          (state : Nat × List SourceCoreDataFaultSites.IndexSite × List SourceCoreDataPlaceFaultSites.Site ×
            List MissingSite × List (Word × Diagnostic) × List ExpressionId) =>
          Inventory capacity state.1 state.2.1 state.2.2.1 state.2.2.2.1 original state.2.2.2.2.1
        change nodeInvariant source.nodes current
        apply CompatibleMemberCertificates.forIn_preserves nodesLoop nodeInvariant previous
        intro seen retained remaining current outcome _split previous ran
        obtain ⟨next, indices, places, missing, fixed, seenIndices⟩ := current
        dsimp only at ran
        cases retained with
        | expression node =>
          cases form : node.form <;> simp only [form] at ran
          all_goals first
            | exact ⟨_, (Except.ok.inj ran).symm, previous⟩
            | skip
          case index mapping key =>
            by_cases nodeOwner : node.id.occurrence.owner ≠ source.owner
            · rw [if_pos nodeOwner] at ran
              change (Except.error (.ownerMismatch node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
              cases ran
            · rw [if_neg nodeOwner] at ran
              by_cases mappingOwner : mapping.occurrence.owner ≠ source.owner
              · rw [if_pos mappingOwner] at ran
                change (Except.error (.ownerMismatch mapping) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                cases ran
              · rw [if_neg mappingOwner] at ran
                by_cases keyOwner : key.occurrence.owner ≠ source.owner
                · rw [if_pos keyOwner] at ran
                  change (Except.error (.ownerMismatch key) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                  cases ran
                · rw [if_neg keyOwner] at ran
                  by_cases duplicate : seenIndices.contains node.id = true
                  · rw [if_pos duplicate] at ran
                    change (Except.error (.duplicateOccurrence node.id) : Except SourceCoreCompatibleDataPlaceFaultSites.Error _) = .ok outcome at ran
                    cases ran
                  · rw [if_neg duplicate] at ran
                    split at ran
                    · rename_i _prior _found
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      exact expression_resume previous ran
                    · obtain ⟨reason, _generated, ran⟩ := bind_ok ran
                      obtain ⟨_endpoint, _checked, ran⟩ := bind_ok ran
                      try dsimp only [pure, Except.pure, bind, Except.bind] at ran
                      have issued := previous.index_range (index := ⟨owner, node.id, reason,
                        ⟨.typeMismatch node.type none, .occurrence node.id.occurrence, some node.span⟩⟩)
                      simp only [Nat.add_assoc] at issued
                      exact expression_resume issued ran
        | statement node =>
          obtain ⟨current, targetsLoop, finished⟩ := bind_ok ran
          refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
          change Inventory capacity current.1 indices current.2.1 current.2.2.1
            original current.2.2.2
          apply CompatibleMemberCertificates.forIn_preserves targetsLoop (fun _ current =>
            Inventory capacity current.1 indices current.2.1 current.2.2.1
              original current.2.2.2) previous
          intro seen assignment remaining current outcome _split previous ran
          obtain ⟨next, places, missing, fixed⟩ := current
          dsimp only at ran
          split at ran
          · obtain ⟨route, _described, ran⟩ := bind_ok ran
            split at ran
            · obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              exact ⟨_, (Except.ok.inj finished).symm, route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) previous stepsLoop⟩
            · obtain ⟨reason, generated, ran⟩ := bind_ok ran
              have number := word_number generated
              have issued := previous.place_fixed (place := ⟨owner, .occurrence node.id.occurrence,
                assignment.target.root, none, reason,
                ⟨.invalidPlaceProjection, .occurrence node.id.occurrence, some node.span⟩⟩) number rfl
              try dsimp only [pure, Except.pure, bind, Except.bind] at ran
              obtain ⟨current, stepsLoop, finished⟩ := bind_ok ran
              refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
              apply route_ranges (owner := owner) (source := source) (node := node) (assignment := assignment) (steps := route.steps) (fun _ => rfl) _ stepsLoop
              exact issued
          · exact ⟨_, (Except.ok.inj ran).symm, previous⟩
  obtain ⟨extra, _extraAccepted, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst program
  obtain ⟨next, indices, places, missing, fixed⟩ := state
  change Inventory capacity next indices places missing original fixed at generated
  have actualBase : SourceCoreProgramFaultSites.prepare plan root = .ok base := by
    cases h : SourceCoreProgramFaultSites.prepare plan root with
    | error error => rw [h] at baseAccepted; cases baseAccepted
    | ok value => rw [h] at baseAccepted; cases baseAccepted; rfl
  exact ⟨base, actualBase, generated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleProgramAssignmentPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier
/-! Original Word metadata determines scalar operands without a callable
observation assumption. These facts support the actual bare compound commit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem word_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = .word) :
    ∃ word, source = .word word ∧ value = .word word ∧ type = .word := by
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | word word => intro _; exact ⟨word, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
      intro view
      have scalar : checked.catalog.project metadata.resultType = .ok .word := by
        rw [← checked.catalog.project_runtimeType, view]
        rfl
      cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | integer | product | function | proxy | mappingValue =>
      intro view
      cases view
  | nil | cons | empty | entry | absent | present => trivial

theorem initialized_success
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (divisor : operator.mayPanic = false ∨ right ≠ .word Word.zero)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : DataEquality.Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases profile with rfl | word
  · exact ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store),
      DataPlaceModifier.assignment_excludes_invalid (.equal _ _)⟩
  · obtain ⟨left, rfl, rfl, rfl⟩ := word_fields leftRep word
    obtain ⟨right, rfl, rfl, _⟩ := word_fields rightRep word
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.word_success operator left right
      (divisor.imp_right fun different same => different (congrArg Dynamic.Value.word same))
      snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .word) word (.word result), applied, evaluated,
      DataPlaceModifier.assignment_excludes_invalid applied⟩

/-- The native modifier always gives a leaf. The source either applies the
operation, or panics on a zero divisor. -/
theorem initialized_outcome
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : DataEquality.Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧
      ((Dynamic.AssignmentValueApplies operator (some left) right result ∧
          ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right) ∨
        (∃ operation, binaryOperator (type = .integer) operator = some ⟨operation, true⟩ ∧
          rightCore = .word Word.zero ∧
          Dynamic.AssignmentOperandsPanic operator (some left) right SourceCorePanics.divisionByZero)) := by
  by_cases zero : operator.mayPanic = true ∧ right = .word Word.zero
  · obtain ⟨panics, rfl⟩ := zero
    have word : SourceCoreRawMetadata.runtimeType sourceType = .word := by
      rcases profile with same | word
      · subst same; simp [Syntax.ValueAssignOp.mayPanic] at panics
      · exact word
    obtain ⟨left, rfl, rfl, rfl⟩ := word_fields leftRep word
    obtain ⟨zero, sameZero, rfl, _⟩ := word_fields rightRep word
    cases sameZero
    cases operator <;> simp [Syntax.ValueAssignOp.mayPanic] at panics
    · exact ⟨_, _, .compatible (actual := .word) word (.word (left.udiv Word.zero)),
        .caseRight (snapshotSelected.evaluates store)
          (.inRight (.binary (.var rfl) ((rightSelected.weaken _).evaluates store) rfl)),
        .inr ⟨.wordDiv, rfl, rfl, .compound .uncheckedDivide (.wordUncheckedDivide left)⟩⟩
    · exact ⟨_, _, .compatible (actual := .word) word (.word (left.umod Word.zero)),
        .caseRight (snapshotSelected.evaluates store)
          (.inRight (.binary (.var rfl) ((rightSelected.weaken _).evaluates store) rfl)),
        .inr ⟨.wordMod, rfl, rfl, .compound .uncheckedModulo (.wordUncheckedModulo left)⟩⟩
  · have divisor : operator.mayPanic = false ∨ right ≠ .word Word.zero := by
      by_cases panics : operator.mayPanic = true
      · exact .inr fun same => zero ⟨panics, same⟩
      · exact .inl (by simpa using panics)
    obtain ⟨result, value, related, applied, evaluated, valid⟩ :=
      initialized_success profile divisor leftRep rightRep snapshotSelected rightSelected store invalid
    exact ⟨result, value, related, evaluated, .inl ⟨applied, valid⟩⟩

/-- An applied source operation passes the check of its modifier. -/
theorem passes_of_applies {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right result : Dynamic.Value} {rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    (applies : Dynamic.AssignmentValueApplies operator snapshot right result) (integer : Bool) :
    SourceCoreDataPlaces.Passes (binaryOperator integer operator) rightCore := by
  by_cases panics : operator.mayPanic = true
  · have word : SourceCoreRawMetadata.runtimeType sourceType = .word := by
      rcases profile with same | word
      · subst same; simp [Syntax.ValueAssignOp.mayPanic] at panics
      · exact word
    obtain ⟨word, rfl, rfl, _⟩ := word_fields rightRep word
    rcases DataPlaceModifier.assignment_divisor applies with total | different
    · rw [panics] at total; cases total
    · have nonzero : word ≠ Word.zero := fun same => different (same ▸ rfl)
      cases operator <;> simp [Syntax.ValueAssignOp.mayPanic] at panics
      · exact .nonzero nonzero
      · exact .nonzero nonzero
  · exact CompatiblePlaceModifier.passes_of_total (by simpa using panics) integer rightCore

/-- The optional pre-RHS snapshot determines whether the actual modifier
fails or produces a replacement. Every outcome keeps the current RHS store. -/
theorem modifier_total {sourceType : TypeSystem.Ty} {type : Ty} {initial : Option Dynamic.Value}
    {snapshot rightCore : Value} {right : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word)
    (saved : SnapshotRep checked registry functions mapping world sourceType type initial snapshot)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshot)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    (Dynamic.AssignmentOperandsInvalid operator initial right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inLeft type (.word invalid)) store) ∨
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      (Dynamic.AssignmentValueApplies operator initial right result ∨
        ∃ operation, binaryOperator (type = .integer) operator = some ⟨operation, true⟩ ∧ rightCore = .word Word.zero ∧
          Dynamic.AssignmentOperandsPanic operator initial right SourceCorePanics.divisionByZero) ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  cases saved with
  | present related =>
      obtain ⟨result, value, represented, evaluated, outcome⟩ :=
        initialized_outcome profile related rightRep snapshotSelected rightSelected store invalid
      exact .inr ⟨result, value, represented, outcome.imp (fun applied => applied.1) id, evaluated⟩
  | absent =>
      by_cases equal : operator = .equal
      · subst operator
        exact .inr ⟨right, rightCore, rightRep, .inl (.equal _ _), .inRight (rightSelected.evaluates store)⟩
      · refine .inl ⟨.uninitialized equal, ?_⟩
        cases operator <;> first
        | exact (equal rfl).elim
        | (by_cases integer : type = .integer <;>
            simp only [binaryOperator, integer, ite_true, ite_false, modified] <;>
            exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word))

end Solcore.SourceSemantics.CoreLowering.CompatibleBareWordModifier
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotPreservation
/-! Preservation for every independent bare-root snapshot trace and fault.
No source key/RHS exists, and the native store is unchanged on failure. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap DataEquality
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {administrativeContext : Core.Context}
  {place : PlaceResolution} {prepared : Prepared} {mapping : LocationMap} {world : StoreTyping}
  {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap}
  {store : Store} {index : Nat}

theorem preserves (layout : Layout prepared) (bare : place.projections = [])

    (profile : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {updated : Dynamic.Value}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment before place updated after)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word)
    (passes : SourceCoreDataPlaces.Passes operator .unit) :
    ∃ finalStore,
      Evaluates coreEnvironment store (execute prepared (.var index) (SourceCoreCalls.packArguments [])
        (LanguageResult.success .unit) (LanguageResult.success .unit) .unit operator true invalid)
        (.inRight .word .unit) finalStore ∧
      HeapRepresents compilation.checked registry functions mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases trace with
  | intro resolve written =>
    cases resolve with
    | @intro _ _ _ _ _ _ _ location initialCell currentCell resolved initial selected lookup initialRead keys currentRead root selection =>
      rw [bare] at keys
      cases keys
      cases selection
      cases written with
      | intro writeRead typeEq writeInitial changed sourceWrite =>
        cases changed with
        | leaf applies =>
          obtain ⟨scheme, schemeLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookup, staticRead, staticType, _⟩ := locals.lookup schemeLookup
          have sameLocation := lookup.functional staticLookup
          subst staticLocation
          have sameCell := currentRead.functional staticRead
          subst staticCell
          have cellType := staticType.trans bodyEq
          obtain ⟨target, nativeLookup, reference⟩ := environments.lookup_visible lookup slot
          obtain ⟨optional, nativeRead, represented⟩ := heaps.read_at reference currentRead
          cases root with
          | emptyMapping key value =>
            have impossible := cellType ▸ profile
            rcases impossible with impossible | impossible <;> cases impossible
          | uninitialized => cases applies
          | initialized =>
            cases represented with
            | @initialized rawType payload sourceValue nativeValue related =>
              simp only at cellType
              subst_vars
              obtain ⟨replacement, changedValue, replacementRep, actualApplies, modifier, _⟩ :=
                CompatiblePlaceNumericBitNotModifier.success profile related
                  (environment := rhsEnvironment prepared.route.rootType target .unit (.inRight .unit nativeValue) .unit coreEnvironment)
                  (rhs := .var 0) (.var (index := 1) rfl) operator store invalid
              have same := CompatiblePlaceBitNotModifier.functional actualApplies applies
              subst replacement
              obtain ⟨finalStore, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference currentRead replacementRep sourceWrite
              let commit : CompatiblePlaceBitNotCommit.Execution compilation.checked registry functions prepared [] coreEnvironment
                  store mapping world target [] nativeValue before after updated operator invalid := {
                replacement := changedValue, value := changedValue, helperStore := store, finalStore := finalStore,
                finalWorld := world, related := replacementRep, heaps := finalHeaps, worlds := .refl _, frame := frame,
                metadata := .of_write sourceWrite,
                modified := by simpa only [← layout.sameType, packValues] using modifier,
                setter := CompatibleBareBitNotNative.setter_evaluates layout (.inRight .unit nativeValue) changedValue nativeRead,
                read := ⟨_, nativeRead⟩, written := coreWritten }
              refine ⟨finalStore, ?_, finalHeaps, frame, .of_write sourceWrite⟩
              apply CompatibleBareBitNotNative.prefix_plug layout nativeLookup nativeRead
              apply commit.plug passes
              simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success]
              simpa only [commit, packValues] using (Evaluates.inRight (leftType := .word)
                (environment := writtenEnvironment prepared.route.rootType target .unit (.inRight .unit nativeValue)
                  .unit changedValue changedValue coreEnvironment) (initialStore := finalStore) Evaluates.unit)

end Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotMeaning
end
