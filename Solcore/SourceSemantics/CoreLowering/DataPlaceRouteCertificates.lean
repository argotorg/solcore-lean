import Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceResolvedTarget

/-! Static mixed member/index routes extracted from the real compiler.
Exact retained source types are explicit: equality of erased projections does
not by itself authenticate source nominal or mapping metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues
open DataPlaceMemberCertificates DataPlaceMembers

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

/-- A successful checked projection exposes both the raw projection and its
well-formedness under the actual catalog definitions. -/
theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (accepted : project checked site sourceType = .ok type) :
    checked.catalog.project sourceType = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreGeneralTypes.projectType at accepted
  cases projected : checked.project sourceType with
  | error error => simp [projected, Except.map, Except.mapError] at accepted
  | ok projection =>
    simp only [projected, Except.map, Except.mapError, Except.ok.injEq] at accepted
    subst type
    refine ⟨?_, projection.typed⟩
    unfold SourceCoreDataCatalog.Checked.project at projected
    cases raw : checked.catalog.project sourceType with
    | error error => simp [raw, bind, Except.bind] at projected
    | ok actual =>
      simp only [raw, bind, Except.bind] at projected
      split at projected
      · cases projected; rfl
      · cases projected

private theorem nominal_project {catalog : SourceCoreDataCatalog.Catalog}
    {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type with
  | constructor constructor =>
    cases constructor with
    | declaration => simp [SourceCoreDataCatalog.Catalog.project, selected]
    | builtin builtin => cases builtin <;> simp [SourceCoreDataCatalog.nominalParts] at nominal
  | application => simp [SourceCoreDataCatalog.Catalog.project, selected]
  | _ => simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- A source metadata profile, containing no Core evaluation premises. Member
payloads retain exact source field types; each index occurrence has exactly the
mapping's retained key type, including observable type metadata. -/
inductive Profile (signatures : ProgramSignatures) (source : TypedSource) :
    TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} (erased : SourceCoreDataCatalog.erase type = type) :
      Profile signatures source type [] type
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {rest : List PlaceProjection}
      (nominal : SourceCoreDataCatalog.nominalParts root = some (signature.id, arguments))
      (selected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (uniform : Uniform signature arguments index field)
      (tail : Profile signatures source field rest leaf) :
      Profile signatures source root (.member name index :: rest) leaf
  | index {key value leaf : TypeSystem.Ty} {id : ExpressionId} {node : ExpressionNode}
      {rest : List PlaceProjection}
      (erased : SourceCoreDataCatalog.erase (.mapping key value) = .mapping key value)
      (found : source.lookupExpression? id = some node) (typed : node.type = key)
      (tail : Profile signatures source value rest leaf) :
      Profile signatures source (.mapping key value) (.index id :: rest) leaf

theorem Profile.erased {signatures : ProgramSignatures} {source : TypedSource}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (profile : Profile signatures source root projections leaf) : SourceCoreDataCatalog.erase root = root := by
  cases profile with
  | nil erased | index erased => exact erased
  | member nominal => exact DataEqualityValues.erase_nominal nominal

/-- The emitted route with authentic source fields, actual projected types and
retained key occurrence metadata. Mapping helper preparation is a later step. -/
inductive RawPath (checked : Checked) (signatures : ProgramSignatures) (source : TypedSource) :
    TypeSystem.Ty → Ty → List Step → List PlaceProjection → TypeSystem.Ty → Ty →
      List TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} {coreType : Ty}
      (projected : checked.catalog.project type = .ok coreType) :
      RawPath checked signatures source type coreType [] [] type coreType []
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {name : String}
      {branches : List MemberBranch} {fieldType leafType : Ty} {steps : List Step}
      {rest : List PlaceProjection} {keys : List TypeSystem.Ty}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (rootProjected : checked.catalog.project root = .ok (.namedData dataType))
      (fieldProjected : checked.catalog.project field = .ok fieldType)
      (tail : RawPath checked signatures source field fieldType steps rest leaf leafType keys) :
      RawPath checked signatures source root (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: rest) leaf leafType keys
  | index {key value leaf : TypeSystem.Ty} {layout : OrderedMapping.Layout} {id : ExpressionId}
      {node : ExpressionNode} {steps : List Step} {rest : List PlaceProjection} {leafType : Ty}
      {keys : List TypeSystem.Ty}
      (identity : checked.catalog.identity? (.mapping key value) = some layout.dataType)
      (erased : SourceCoreDataCatalog.erase (.mapping key value) = .mapping key value)
      (keyProjected : checked.catalog.project key = .ok layout.keyType)
      (valueProjected : checked.catalog.project value = .ok layout.valueType)
      (found : source.lookupExpression? id = some node) (typed : node.type = key)
      (tail : RawPath checked signatures source value layout.valueType steps rest leaf leafType keys) :
      RawPath checked signatures source (.mapping key value) layout.type
        (.index layout id value :: steps) (.index id :: rest) leaf leafType (key :: keys)

/-- Successful actual traversal produces the static mixed route. This theorem
never runs or assumes the meaning of a generated getter, comparator or default. -/
theorem raw_of_routeSteps {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf selected : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    {rootType leafType : Ty}
    (profile : Profile signatures source root projections leaf)
    (rootProjected : checked.catalog.project root = .ok rootType)
    (leafProjected : checked.catalog.project leaf = .ok leafType)
    (accepted : routeSteps checked signatures source site binder root projections = .ok (steps, selected)) :
    selected = leaf ∧ ∃ keys, RawPath checked signatures source root rootType steps projections leaf leafType keys := by
  induction profile generalizing steps selected rootType with
  | nil erased =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    have same := Except.ok.inj (rootProjected.symm.trans leafProjected)
    subst rootType
    exact ⟨rfl, [], .nil leafProjected⟩
  | @member root field leaf name index signature arguments rest nominal selectedSignature uniform tail ih =>
    simp only [routeSteps] at accepted
    obtain ⟨⟨head, chosen⟩, headAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨identity, branches, coreField, rfl, rfl, certificate⟩ :=
      certificate_of_memberStep (DataEqualityValues.erase_nominal nominal) nominal selectedSignature uniform headAccepted
    obtain ⟨⟨remaining, result⟩, tailAccepted, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    have projected := nominal_project nominal certificate.identityLookup
    have same := Except.ok.inj (rootProjected.symm.trans projected)
    subst rootType
    obtain ⟨rfl, keys, path⟩ := ih (project_facts certificate.projectedField).1 leafProjected tailAccepted
    exact ⟨rfl, keys, .member (certificate.layout nominal selectedSignature) projected
      (project_facts certificate.projectedField).1 path⟩
  | @index key value leaf id node rest erased found typed tail ih =>
    rw [routeSteps.eq_def] at accepted
    simp only [erased] at accepted
    by_cases owned : id.occurrence.owner = source.owner
    · simp only [owned, ne_eq, not_true_eq_false, ↓reduceIte, found, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨coreKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨projectedKey, keyProjected, accepted⟩ := bind_ok accepted
      obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
      cases checkedUnit
      obtain ⟨projectedValue, valueProjected, accepted⟩ := bind_ok accepted
      cases identity : checked.catalog.identity? (.mapping key value) with
      | none => simp [identity, throw] at accepted
      | some identityId =>
        simp only [identity] at accepted
        split at accepted
        next registered =>
          obtain ⟨⟨remaining, result⟩, tailAccepted, accepted⟩ := bind_ok accepted
          simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          have projected : checked.catalog.project (.mapping key value) = .ok (.namedData identityId) := by
            simp [SourceCoreDataCatalog.Catalog.project, identity]
          have same := Except.ok.inj (rootProjected.symm.trans projected)
          subst rootType
          obtain ⟨rfl, keys, path⟩ := ih (project_facts valueProjected).1 leafProjected tailAccepted
          exact ⟨rfl, key :: keys, .index (layout := ⟨projectedKey, projectedValue, identityId⟩) identity erased (project_facts keyProjected).1
            (project_facts valueProjected).1 found typed path⟩
        next rejected => cases accepted
    · simp [owned, throw, pure, Except.pure, bind, Except.bind] at accepted

/-- Exact key types in source projection order, including repeated occurrences. -/
inductive KeyTypes (source : TypedSource) : List PlaceProjection → List TypeSystem.Ty → Prop where
  | nil : KeyTypes source [] []
  | member {name index rest types} (tail : KeyTypes source rest types) :
      KeyTypes source (.member name index :: rest) types
  | index {id node type rest types} (found : source.lookupExpression? id = some node)
      (typed : node.type = type) (tail : KeyTypes source rest types) :
      KeyTypes source (.index id :: rest) (type :: types)

theorem RawPath.keyTypes {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {keys : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType keys) :
    KeyTypes source projections keys := by
  induction path with
  | nil => exact .nil
  | member _ _ _ _ ih => exact .member ih
  | index _ _ _ _ found typed _ ih => exact .index found typed ih

private theorem tree_cons {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope}
    {id : ExpressionId} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (id :: ids) types codes) :
    ∃ node typeTypes code restCodes, source.lookupExpression? id = some node ∧
      types = node.type :: typeTypes ∧ codes = code :: restCodes ∧
      DataExpressionSequence.Tree source certificate scope ids typeTypes restCodes := by
  cases tree with
  | single found generated => exact ⟨_, [], _, [], found, rfl, rfl, .nil⟩
  | cons found generated tail => exact ⟨_, _, _, _, found, rfl, rfl, tail⟩

theorem KeyTypes.tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate} {scope : Scope}
    {projections : List PlaceProjection} {keys types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (keyTypes : KeyTypes source projections keys)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes) :
    types = keys := by
  induction keyTypes generalizing types codes with
  | nil => cases tree; rfl
  | member tail ih => exact ih tree
  | @index id node type rest keys found typed tail ih =>
    obtain ⟨actual, remaining, code, restCodes, foundActual, rfl, rfl, restTree⟩ := tree_cons tree
    have same := Option.some.inj (found.symm.trans foundActual)
    subst actual
    rw [typed, ih restTree]

/-- Actual mapping preparation and the related key vector instantiate the
semantic path automatically. Key positions use the real preparation counter;
member projections leave that counter unchanged. -/
theorem RawPath.prepared_path {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {root leaf : TypeSystem.Ty} {rootType leafType : Ty} {steps : List Step}
    {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source root rootType steps projections leaf leafType sourceTypes)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {preparedSteps : List PreparedStep}
    {preparedKeys : List (ExpressionId × Ty)} {sources : List Dynamic.Value} {values allKeys : List Value}
    {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (prepared : DataPlaceMappingPreparation.Steps checked fuel missing position steps preparedSteps preparedKeys)
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (represented : DataExpressionSequence.Values (DataPayload.payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (atPosition : ∀ i value, values[i]? = some value → allKeys[position + i]? = some value) :
    ∃ count, DataPayloadReadPaths.Path checked signatures functions mapping world allKeys
      root rootType preparedSteps evaluated leaf leafType count := by
  induction path generalizing position preparedSteps preparedKeys sources values evaluated coreTypes with
  | nil projected =>
    cases prepared
    cases shaped
    exact ⟨0, .nil projected⟩
  | member layout rootProjected fieldProjected tail ih =>
    cases prepared with
    | member prepared =>
      cases shaped with
      | member shaped =>
        obtain ⟨count, rest⟩ := ih prepared shaped represented atPosition
        exact ⟨count, .member layout fieldProjected rest⟩
  | @index key value leaf layout id node steps rest leafType types identity erased keyProjected valueProjected found typed tail ih =>
    cases prepared with
    | @index _ _ _ _ entry sourceKey registeredValue comparison default _ _ _ selected mappingType comparisonGenerated defaultGenerated prepared =>
      obtain ⟨actualEntry, actualSelected, actualType⟩ := DataEqualityValues.identity_entry identity
      have sameEntry := Option.some.inj (selected.symm.trans actualSelected)
      subst actualEntry
      rw [erased, mappingType] at actualType
      obtain ⟨keySame, valueSame⟩ := TypeSystem.Ty.mapping.inj actualType
      subst sourceKey
      subst registeredValue
      cases shaped with
      | index shaped =>
        cases represented with
        | cons head represented =>
          have headRep : DataPayload.ValueRep checked.catalog signatures functions mapping world key _ _ _ := head
          have sameType := Except.ok.inj (headRep.projection.symm.trans keyProjected)
          cases sameType
          obtain ⟨count, restPath⟩ := ih prepared shaped represented (by
            intro i v found
            simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm 1] using atPosition (i + 1) v found)
          refine ⟨checked.catalog.entries.length + 1 + count, .index
            (DataPlaceMappingIndex.Index.of_generated comparisonGenerated defaultGenerated keyProjected valueProjected)
            keyProjected valueProjected headRep ?_ restPath⟩
          simpa only [Nat.add_zero] using atPosition 0 _ rfl

/-- Root normalization authenticated by the actual describe branch. -/
inductive RootShape (catalog : SourceCoreDataCatalog.Catalog) :
    TypeSystem.Ty → Option OrderedMapping.Layout → Prop where
  | ordinary {sourceType : TypeSystem.Ty}
      (notMapping : ¬ ∃ key value, sourceType = .mapping key value) : RootShape catalog sourceType none
  | mapping {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
      (identity : catalog.identity? (.mapping key value) = some layout.dataType)
      (keyProjected : catalog.project key = .ok layout.keyType)
      (valueProjected : catalog.project value = .ok layout.valueType)
      (registered : layout.Registered catalog.definitions) : RootShape catalog (.mapping key value) (some layout)

theorem RootShape.layout {catalog : SourceCoreDataCatalog.Catalog} {prepared : Prepared}
    (shape : RootShape catalog prepared.route.rootSourceType prepared.route.rootMapping) :
    DataPlaceSnapshot.RootLayout catalog prepared prepared.route.rootSourceType := by
  cases prepared with
  | mk route steps keys invalid => cases route with
    | mk root rootType leafType routeSteps rootMapping =>
      cases shape with
      | ordinary notMapping => exact .ordinary notMapping rfl
      | mapping identity keyProjected valueProjected registered =>
        exact .mapping rfl identity keyProjected valueProjected registered

/-- A described route exposes its authentic root normalization and full mixed
path. The source profile is checked against the real declaration selected by
`rootBinder`, rather than an arbitrary externally supplied root type. -/
theorem described {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (profile : ∀ binder, rootBinder source assignment.target.root = .ok binder →
      Profile signatures source binder.scheme.body assignment.target.projections assignment.target.type)
    (accepted : describe checked signatures source site assignment = .ok route) :
    RootShape checked.catalog route.rootSourceType route.rootMapping ∧
      ∃ keys, RawPath checked signatures source route.rootSourceType route.rootType route.steps
        assignment.target.projections assignment.target.type route.leafType keys := by
  unfold describe at accepted
  dsimp only at accepted
  split at accepted
  next allowed =>
    obtain ⟨binder, binding, accepted⟩ := bind_ok accepted
    obtain ⟨rootType, rootProjected, accepted⟩ := bind_ok accepted
    obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := bind_ok accepted
    split at accepted
    next compatible =>
      have sourceProfile := profile binder binding
      have erased := sourceProfile.erased
      simp only [erased] at accepted
      have finish {rootMapping : Option OrderedMapping.Layout}
          (shape : RootShape checked.catalog binder.scheme.body rootMapping)
          (finished : (do
            let leaf ← project checked site assignment.target.type
            pure (⟨binder.scheme.body, rootType, leaf, steps, rootMapping⟩ : Route)) = .ok route) :
          RootShape checked.catalog route.rootSourceType route.rootMapping ∧
            ∃ keys, RawPath checked signatures source route.rootSourceType route.rootType route.steps
              assignment.target.projections assignment.target.type route.leafType keys := by
        obtain ⟨leafType, leafProjected, finished⟩ := bind_ok finished
        simp only [pure, Except.pure, Except.ok.injEq] at finished
        subst route
        obtain ⟨_, keys, path⟩ := raw_of_routeSteps sourceProfile (project_facts rootProjected).1
          (project_facts leafProjected).1 routed
        exact ⟨shape, keys, path⟩
      cases typeEq : binder.scheme.body <;> simp only [typeEq] at accepted
      all_goals try
        exact finish (.ordinary (by
          rw [typeEq]
          rintro ⟨_, _, impossible⟩
          cases impossible)) (by simpa only [typeEq, pure, Except.pure, bind, Except.bind] using accepted)
      rename_i key value
      cases identity : checked.catalog.identity? (.mapping key value) with
      | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
      | some id =>
        simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
        obtain ⟨coreKey, keyProjected, accepted⟩ := bind_ok accepted
        obtain ⟨coreValue, valueProjected, accepted⟩ := bind_ok accepted
        split at accepted
        next registered =>
          have keyFacts := project_facts keyProjected
          have valueFacts := project_facts valueProjected
          apply finish (rootMapping := some ⟨coreKey, coreValue, id⟩) ?_ ?_
          · rw [typeEq]
            exact .mapping identity keyFacts.1 valueFacts.1 ⟨keyFacts.2, valueFacts.2, registered⟩
          · simpa only [typeEq, pure, Except.pure, bind, Except.bind] using accepted
        next rejected => cases accepted
    next incompatible => cases accepted
  next rejected => cases accepted

end Solcore.SourceSemantics.CoreLowering.DataPlaceRouteCertificates
