import Solcore.SourceSemantics.CoreLowering.DataPlaceExactFault
import Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot

/-! Completed live-root getters reflect an independently constructed source
snapshot or failure. Uninitialized mappings are virtual empty values; ordinary
absent roots remain absent for a bare assignment and fail before a projection.
Only administrative Core cells are appended. No source evaluation trace or
child/helper execution is an assumption of the live-root reflection theorem. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataPlaceSnapshot DataEquality

/-- Source observations of the snapshot phase. The invalid-projection branch
records the independent absent root and nonempty path; missing-default reasons
retain their exact type-indexed diagnostic. -/
inductive ResultRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (missing : TypeSystem.Ty → Word) (leaf : TypeSystem.Ty)
    (cell : Dynamic.Cell) (projections : List Dynamic.EvaluatedProjection) : Value → Prop where
  | read {initial selected : Option Dynamic.Value} {snapshot : Value}
      (root : Dynamic.RootInitialValue cell initial)
      (read : Dynamic.ProjectionsRead initial projections selected)
      (related : OptionalRep catalog signatures functions mapping world leaf prepared.route.leafType selected snapshot) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections (.inRight .word snapshot)
  | missing {source : Dynamic.Value} {reason : Dynamic.SemanticFault}
      (root : Dynamic.RootInitialValue cell (some source))
      (fault : Dynamic.ProjectionsFaults (some source) projections reason) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections
        (.inLeft prepared.optionalLeaf (.word (DataPlaceExactFault.token missing reason)))
  | uninitialized (root : Dynamic.RootInitialValue cell none) (nonempty : projections ≠ []) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections
        (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection))

theorem ResultRep.extend {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {prepared : Prepared} {missing : TypeSystem.Ty → Word} {leaf : TypeSystem.Ty} {cell : Dynamic.Cell}
    {projections : List Dynamic.EvaluatedProjection} {value : Value}
    (related : ResultRep catalog signatures functions mapping world prepared missing leaf cell projections value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRep catalog signatures functions futureMapping futureWorld prepared missing leaf cell projections value := by
  cases related with
  | read root read related => exact .read root read (related.extend maps worlds)
  | missing root fault => exact .missing root fault
  | uninitialized root nonempty => exact .uninitialized root nonempty

private theorem initial_exists {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  cases related with
  | initialized => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ projected =>
    by_cases mappingType : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingType
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨none, .uninitialized mappingType⟩

private theorem empty_projections {checked : Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : DataPayloadReadPaths.Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    (empty : steps = []) : projections = [] := by
  induction path with
  | nil => rfl
  | member => cases empty
  | index => cases empty
  | comptime _ ih => exact ih empty

/-- A compositional argument-evaluation law. The source outcome and all
recursive helper executions are constructed from static preparation and full
payloads. The live-root theorem below supplies the actual load itself. -/
theorem evaluates {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world cell optional prepared.route.rootType)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (packValues values)) store) :
    ∃ result finalStore administrative,
      ResultRep checked.catalog signatures functions mapping world prepared missing leaf cell evaluated result ∧
      Evaluates environment before (.apply (getter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative := by
  obtain ⟨count, semanticPath⟩ := path.prepared_path preparation shaped keysRelated (allKeys := values)
    (by intro index value selected; simpa only [Nat.zero_add] using selected)
  obtain ⟨initial, root⟩ := initial_exists cellRep
  cases initial with
  | none =>
    by_cases empty : evaluated = []
    · subst evaluated
      obtain ⟨snapshot, finalStore, administrative, represented, ran, appended, _⟩ :=
        getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root .nil semanticPath argumentEvaluated
      exact ⟨_, finalStore, administrative, .read root .nil represented, ran, appended⟩
    · obtain ⟨noMapping, optionalEq⟩ := root_absent rootLayout cellRep root
      have stepsNonempty : prepared.steps ≠ [] := fun impossible => empty (empty_projections semanticPath impossible)
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        refine ⟨_, store, [], .uninitialized root empty, .apply .lambda argumentEvaluated ?_, by simp⟩
        simp only [stepsEq, normalizeRoot, noMapping, LanguageResult.failure]
        rw [optionalEq]
        exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  | some sourceRoot =>
    obtain ⟨coreRoot, normalized, rootRelated⟩ := root_present rootLayout cellRep root
    rcases DataPlaceReadTotality.read_or_fault functionTypes layouts path preparation shaped keysRelated rootRelated with
        ⟨selected, value, read, related⟩ | ⟨reason, fault⟩
    · obtain ⟨snapshot, finalStore, administrative, represented, ran, appended, _⟩ :=
        getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root read semanticPath argumentEvaluated
      exact ⟨_, finalStore, administrative, .read root read represented, ran, appended⟩
    · have stepsNonempty : prepared.steps ≠ [] := by
        intro impossible
        have empty := empty_projections semanticPath impossible
        rw [empty] at fault
        cases fault
      obtain ⟨finalStore, administrative, ran, _, appended⟩ :=
        DataPlaceExactFault.preserves observations faithful layouts path preparation shaped keysRelated
          (allKeys := values) (by intro index value selected; simpa only [Nat.zero_add] using selected) keyLength
          rootRelated fault (coreRoot :: .pair optional (packValues values) :: environment) store
          (.var 0) (.second (.var 1)) .unit (.var rfl) (.second (.var rfl))
      refine ⟨_, finalStore, administrative, .missing root fault, .apply .lambda argumentEvaluated ?_, appended⟩
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        exact .caseRight (normalized.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using ran)

/-- Every completed live-root getter yields an independently constructed source
snapshot or fault. The source heap is unchanged, while finite Core preservation
accounts for all appended helper cells and preserves the existing admin frame. -/
theorem reflects_at {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    {heap : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {target : Location}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr} {result : Value}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues values))
    (completed : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      result finalStore) :
    ∃ futureWorld administrative,
      ResultRep checked.catalog signatures functions mapping futureWorld prepared missing leaf cell evaluated result ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld result (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions ∧
      AdministrativePreserved mapping store mapping finalStore ∧ finalStore = store ++ administrative := by
  obtain ⟨optional, coreRead, cellRep⟩ := read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) keyExpression)
      (.pair optional (packValues values)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead) (keysSelected.evaluates store)
  obtain ⟨actual, after, administrative, represented, ran, appended⟩ :=
    evaluates functionTypes layouts observations faithful path preparation shaped keysRelated keyLength rootLayout cellRep argument
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed ran
  obtain ⟨futureWorld, extension, finalHeaps, typed, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped ran appended
  exact ⟨futureWorld, administrative, represented.extend (.refl _) extension, extension, finalHeaps, typed, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
