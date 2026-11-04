import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.SourceSemantics.Instantiation
import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.SourceSemantics.CoreLowering.AmbientDefinitions

/-!
# Compatible profile: paths

Prepared paths, path arguments, reads, updates and faults, live roots and snapshots, and the ambient heap.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates
/-! Static receipts extracted from the actual compatible member compiler. Rows
retain their original instantiated field types; only runtime projections agree. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces DataPatternValues

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- A compiler loop whose successful rows always yield preserves a prefix
invariant through the entire input. This is a proof about `forIn`, not another
executable compiler traversal. -/
theorem forIn_preserves {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} (accepted : forIn items initial step = .ok final)
    (invariant : List α → β → Prop) (start : invariant [] initial)
    (next : ∀ seen item remaining state outcome,
      items = seen ++ item :: remaining → invariant seen state → step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ invariant (seen ++ [item]) updated) : invariant items final := by
  have loop : ∀ remaining seen state,
      items = seen ++ remaining → invariant seen state → forIn remaining state step = .ok final →
      invariant items final := by
    intro remaining
    induction remaining with
    | nil =>
      intro seen state split valid finished
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at finished
      subst final
      simpa [split] using valid
    | cons item remaining ih =>
      intro seen state split valid finished
      rw [List.forIn_cons] at finished
      obtain ⟨outcome, ran, finished⟩ := bind_ok finished
      obtain ⟨updated, rfl, preserved⟩ := next seen item remaining state outcome split valid ran
      exact ih (seen ++ [item]) updated (by simpa [List.append_assoc] using split) preserved finished
  exact loop items [] initial rfl start accepted

private theorem mapM_length {α β ε : Type} {f : α → Except ε β} {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM f = .ok outputs) : outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => simp [List.mapM_nil, pure, Except.pure] at accepted; subst outputs; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, _, accepted⟩ := bind_ok accepted
    obtain ⟨rest, mapped, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst outputs
    simpa using ih mapped


structure Row (checked : Checked) (site : SourceCoreElaboration.ErrorSite)
    (root field : TypeSystem.Ty) (substitution : TypeSystem.ParameterSubstitution)
    (identity : DataTypeId) (index : Nat) (input : ProgramDataConstructorSignature × Nat)
    (branch : MemberBranch) : Prop where
  authenticated : checked.resolveConstructor
    ⟨input.1.id, substitution, input.1.payloadTypes.map substitution.apply, root⟩ = .ok branch.constructor
  position : branch.constructor = ⟨identity, input.2⟩
  fieldLookup : ∃ actual, (input.1.payloadTypes.map substitution.apply)[index]? = some actual ∧
    SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field
  payloads : (input.1.payloadTypes.map substitution.apply).mapM (project checked site) = .ok branch.payloadTypes

structure Certificate (checked : Checked) (site : SourceCoreElaboration.ErrorSite)
    (root field : TypeSystem.Ty) (signature : ProgramDataSignature)
    (arguments : List TypeSystem.Ty) (index : Nat)
    (identity : DataTypeId) (branches : List MemberBranch) (fieldType : Ty) : Prop where
  identityLookup : checked.catalog.identity? root = some identity
  projectedField : project checked site field = .ok fieldType
  rows : ListRel (Row checked site root field (signature.parameters.zip arguments) identity index)
    signature.constructors.zipIdx branches

/-- All successful compiler rows have a source field whose normalized type
agrees with the selected field. No child runtime evaluation is a premise. -/
theorem certificate_of_memberStep {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {original : TypeSystem.Ty}
    {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {index : Nat}
    {step : Step} {selectedField : TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (signature.id, arguments))
    (signatureSelected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (accepted : memberStep checked signatures site binder original index = .ok (step, selectedField)) :
    ∃ identity branches fieldType, step = .member identity index branches fieldType ∧
      Certificate checked site (SourceCoreRawMetadata.runtimeType original) selectedField signature arguments index identity branches fieldType := by
  unfold memberStep at accepted
  simp only [nominal, signatureSelected, pure, Except.pure, bind, Except.bind] at accepted
  by_cases valid : signature.parameters.length = arguments.length ∧ signature.constructors ≠ []
  · have count := valid.1
    have nonempty := valid.2
    simp only [count, decide_true, List.isEmpty_eq_false_iff.mpr nonempty, Bool.not_false,
      Bool.and_self, ↓reduceIte] at accepted
    cases identityLookup : checked.catalog.identity? (SourceCoreRawMetadata.runtimeType original) with
    | none => simp [identityLookup, throw] at accepted
    | some identity =>
      simp only [identityLookup] at accepted
      obtain ⟨state, loopAccepted, accepted⟩ := bind_ok accepted
      let row := fun field => Row checked site (SourceCoreRawMetadata.runtimeType original) field (signature.parameters.zip arguments) identity index
      let invariant := fun (seen : List (ProgramDataConstructorSignature × Nat))
          (state : Option TypeSystem.Ty × List MemberBranch) =>
        (state.1 = none ∧ seen = [] ∧ state.2 = []) ∨
          ∃ field, state.1 = some field ∧ ListRel (row field) seen state.2
      have certified : invariant signature.constructors.zipIdx state := by
        apply forIn_preserves loopAccepted invariant
        · exact .inl ⟨rfl, rfl, rfl⟩
        · intro seen item remaining state outcome decomposition previous rowAccepted
          obtain ⟨constructor, position⟩ := item
          obtain ⟨selected, branches⟩ := state
          dsimp only at rowAccepted
          cases fieldLookup : (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)))[index]? with
          | none => simp [fieldLookup, throw] at rowAccepted
          | some actual =>
            simp only [fieldLookup] at rowAccepted
            cases selected with
            | none =>
              obtain ⟨rfl, rfl⟩ : seen = [] ∧ branches = [] := by
                rcases previous with absent | ⟨field, impossible, _⟩
                · exact ⟨absent.2.1, absent.2.2⟩
                · cases impossible
              simp only at rowAccepted
              cases resolved : checked.resolveConstructor
                  ⟨constructor.id, signature.parameters.zip arguments,
                    constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)), SourceCoreRawMetadata.runtimeType original⟩ with
              | error error => simp [resolved, Except.mapError] at rowAccepted
              | ok tag =>
                simp only [resolved, Except.mapError] at rowAccepted
                by_cases tagValid : tag.owner = identity ∧ tag.index = position
                · simp only [tagValid.1, tagValid.2, decide_true, Bool.and_self, ↓reduceIte] at rowAccepted
                  obtain ⟨payloadTypes, payloads, rowAccepted⟩ := bind_ok rowAccepted
                  simp only [Except.ok.injEq] at rowAccepted
                  subst outcome
                  refine ⟨_, rfl, .inr ⟨actual, rfl, .cons ?_ .nil⟩⟩
                  exact ⟨resolved, by cases tag; simp_all, ⟨actual, fieldLookup, rfl⟩, payloads⟩
                · simp [tagValid, Bool.and_eq_true, throw] at rowAccepted
            | some selected =>
              have rows : ListRel (row selected) seen branches := by
                rcases previous with absent | ⟨field, same, rows⟩
                · cases absent.1
                · cases same; exact rows
              by_cases sameField : SourceCoreRawMetadata.runtimeType selected = SourceCoreRawMetadata.runtimeType actual
              · simp only [sameField, ↓reduceIte] at rowAccepted
                cases resolved : checked.resolveConstructor
                    ⟨constructor.id, signature.parameters.zip arguments,
                      constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)), SourceCoreRawMetadata.runtimeType original⟩ with
                | error error => simp [resolved, Except.mapError] at rowAccepted
                | ok tag =>
                  simp only [resolved, Except.mapError] at rowAccepted
                  by_cases tagValid : tag.owner = identity ∧ tag.index = position
                  · simp only [tagValid.1, tagValid.2, decide_true, Bool.and_self, ↓reduceIte] at rowAccepted
                    obtain ⟨payloadTypes, payloads, rowAccepted⟩ := bind_ok rowAccepted
                    simp only [Except.ok.injEq] at rowAccepted
                    subst outcome
                    refine ⟨_, rfl, .inr ⟨selected, rfl, DataPatternExecution.ListRel.append rows (.cons ?_ .nil)⟩⟩
                    exact ⟨resolved, by cases tag; simp_all, ⟨actual, fieldLookup, sameField.symm⟩, payloads⟩
                  · simp [tagValid, Bool.and_eq_true, throw] at rowAccepted
              · simp [sameField, throw] at rowAccepted
      rcases certified with absent | ⟨field, selected, rows⟩
      · simp [absent.1, throw] at accepted
      · simp only [selected] at accepted
        obtain ⟨fieldType, projected, accepted⟩ := bind_ok accepted
        simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
        obtain ⟨rfl, rfl⟩ := accepted
        exact ⟨identity, state.2, fieldType, rfl, identityLookup, projected, rows⟩
  · simp [valid, Bool.and_eq_true, throw] at accepted

private theorem project_sound {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : TypeSystem.Ty} {type : Ty} (accepted : project checked site source = .ok type) :
    checked.catalog.project source = .ok type := by
  unfold project SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases generated : checked.catalog.project source with
  | error error => simp [generated, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · simp only [pure, Except.pure, Except.map, Except.mapError, Except.ok.injEq] at accepted
      subst type
      rfl
    · cases accepted

private theorem projectList_sound {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : List TypeSystem.Ty} {types : List Ty}
    (accepted : source.mapM (project checked site) = .ok types) :
    source.mapM checked.catalog.project = .ok types := by
  induction source generalizing types with
  | nil => simpa [List.mapM_nil, pure, Except.pure] using accepted
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted ⊢
    obtain ⟨first, projected, accepted⟩ := bind_ok accepted
    obtain ⟨rest, generated, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst types
    simp [project_sound projected, ih generated, bind, Except.bind]

private theorem relation_at {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {index : Nat} {input : α}
    (found : inputs[index]? = some input) : ∃ output, outputs[index]? = some output ∧ relation input output := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih => cases index with
    | zero => cases found; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

/-- Every authenticated runtime constructor is covered by the emitted rows.
Raw metadata need not equal the canonical row: normalization and actual
constructor lookup prove agreement of native payload positions. -/
theorem Certificate.select {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {root field : TypeSystem.Ty} {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty}
    {index : Nat} {identity : DataTypeId} {branches : List MemberBranch} {fieldType : Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
    (signatureSelected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (certificate : Certificate checked site (SourceCoreRawMetadata.runtimeType root) field signature arguments index identity branches fieldType)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : CompatiblePayload.FunctionModel checked.catalog ambient}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : CompatiblePayload.ConstructorFields checked registry functions mapping world root metadata tag id sources values types) :
    tag.owner = identity ∧ ∃ branch actual sourceChild valueChild,
      branches[tag.index]? = some branch ∧ branch.constructor = tag ∧ branch.payloadTypes = types ∧
      metadata.payloadTypes[index]? = some actual ∧
      SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field ∧
      types[index]? = some fieldType ∧ Dynamic.ValueAt sources index sourceChild ∧ values[index]? = some valueChild ∧
      CompatiblePayload.ValueRep checked registry functions mapping world actual sourceChild valueChild fieldType := by
  have authentic := CompatiblePayload.constructor_authenticated fields.metadataRep fields.registryOwner
  obtain ⟨actualSignature, constructor, actualArguments, signatureFound, constructorFound, parameters, selectedArguments, payloads, result⟩ :=
    CompatibleConstructorMetadata.facts authentic
  have signatureMember : actualSignature ∈ checked.signatures.dataTypes.filter
      (fun data => decide (data.id = metadata.constructor.dataType)) := by rw [signatureFound]; simp
  have signatureId : actualSignature.id = metadata.constructor.dataType := by simpa using (List.mem_filter.mp signatureMember).2
  have nominalEqual := congrArg SourceCoreDataCatalog.nominalParts
    ((congrArg SourceCoreRawMetadata.runtimeType result).symm.trans fields.view.symm)
  simp only [CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal,
    nominal, Option.some.injEq, Prod.mk.injEq] at nominalEqual
  have sameSignature : actualSignature = signature := by
    rw [← signatureId, nominalEqual.1, signatureSelected] at signatureFound
    exact (List.singleton_inj.mp signatureFound).symm
  subst actualSignature
  have constructorMember : constructor ∈ signature.constructors.filter
      (fun candidate => decide (candidate.id = metadata.constructor)) := by rw [constructorFound]; simp
  have constructorId : constructor.id = metadata.constructor := by simpa using (List.mem_filter.mp constructorMember).2
  obtain ⟨position, found⟩ := List.getElem?_of_mem (List.mem_filter.mp constructorMember).1
  have zipped : signature.constructors.zipIdx[position]? = some (constructor, position) := by
    simp [List.getElem?_zipIdx, found]
  obtain ⟨branch, branchFound, row⟩ := relation_at certificate.rows zipped
  let canonical : DataConstructorInstantiation := ⟨constructor.id, signature.parameters.zip arguments,
      constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)),
      SourceCoreRawMetadata.runtimeType root⟩
  have canonicalSelected := (CompatibleConstructorMetadata.resolved_facts row.authenticated).2
  have views : SourceCoreRawMetadata.runtimeType canonical.resultType = SourceCoreRawMetadata.runtimeType metadata.resultType := by
    simpa only [canonical, SourceCoreRawMetadata.runtimeType_idempotent] using fields.view
  have sameTag : branch.constructor = tag := by
    have same := CompatibleConstructorMetadata.constructor_lookup_congr checked.catalog (left := canonical) (right := metadata) constructorId views
    rw [canonicalSelected, fields.selected] at same
    exact Option.some.inj same
  have normalized := CompatibleConstructorMetadata.payloads_runtimeType
    (CompatibleConstructorMetadata.resolved_facts row.authenticated).1 authentic constructorId views
  have projected := CompatibleConstructorMetadata.resolved_payloads_project row.authenticated
    (sameTag.symm ▸ fields.resolved) views
  have branchTypes : branch.payloadTypes = types := by
    rw [projectList_sound row.payloads, fields.payloads.projection] at projected
    exact Except.ok.inj projected
  obtain ⟨canonicalField, canonicalAt, sameField⟩ := row.fieldLookup
  have actualAt : ∃ actual, metadata.payloadTypes[index]? = some actual ∧
      SourceCoreRawMetadata.runtimeType actual = SourceCoreRawMetadata.runtimeType field := by
    have normalizedAt := congrArg (fun types => types[index]?) normalized
    simp only [List.getElem?_map, canonicalAt, Option.map_some] at normalizedAt
    cases actualAt : metadata.payloadTypes[index]? with
    | none => simp [actualAt] at normalizedAt
    | some actual =>
      simp only [actualAt, Option.map_some, Option.some.injEq] at normalizedAt
      exact ⟨actual, rfl, normalizedAt.symm.trans sameField⟩
  obtain ⟨actual, sourceAt, fieldView⟩ := actualAt
  obtain ⟨sourceChild, valueChild, coreType, sourceFound, valueFound, typeFound, related⟩ := fields.payloads.at sourceAt
  have coreField : coreType = fieldType := by
    have projected := related.projection
    have same := congrArg checked.catalog.project fieldView
    simp only [checked.catalog.project_runtimeType] at same
    rw [projected, project_sound certificate.projectedField] at same
    exact Except.ok.inj same
  subst coreType
  have owner : tag.owner = identity := by rw [← sameTag, row.position]
  refine ⟨owner, branch, actual, sourceChild, valueChild, ?_, sameTag, branchTypes,
    sourceAt, fieldView, typeFound, sourceFound, valueFound, related⟩
  have tagIndex : tag.index = position := by rw [← sameTag, row.position]
  simpa only [tagIndex] using branchFound

end Solcore.SourceSemantics.CoreLowering.CompatibleMemberCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
/-! Static extraction from actual mixed place preparation. Each comparison is
prepared once from the catalog row and each index retains its source-order
position. Layout/source projection agreement belongs to route authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

inductive Steps (checked : Checked) (fuel : Nat) (missing : TypeSystem.Ty → Word) :
    List Step → Nat → List PreparedStep → List (ExpressionId × Ty) → Prop where
  | nil {position} : Steps checked fuel missing [] position [] []
  | member {dataType index branches fieldType rest position prepared keys}
      (tail : Steps checked fuel missing rest position prepared keys) :
      Steps checked fuel missing (.member dataType index branches fieldType :: rest) position
        (.member dataType index branches fieldType :: prepared) keys
  | index {layout key valueType rest position prepared keys entry sourceKey recordedValue}
      (row : checked.catalog.entries[layout.dataType.index]? = some entry)
      (source : entry.sourceType = .mapping sourceKey recordedValue)
      {comparison : SourceCoreCompatibleDataEquality.Prepared checked}
      (generated : SourceCoreCompatibleDataEquality.prepare fuel checked sourceKey = .ok comparison)
      (tail : Steps checked fuel missing rest (position + 1) prepared keys) :
      Steps checked fuel missing (.index layout key valueType :: rest) position
        (.index ⟨layout, key, position, comparison.expression, missing valueType⟩ :: prepared) ((key, layout.keyType) :: keys)

 theorem Steps.append {checked : Checked} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    {first second : List Step} {position : Nat} {left right : List PreparedStep} {leftKeys rightKeys : List (ExpressionId × Ty)}
    (a : Steps checked fuel missing first position left leftKeys)
    (b : Steps checked fuel missing second (position + leftKeys.length) right rightKeys) :
    Steps checked fuel missing (first ++ second) position (left ++ right) (leftKeys ++ rightKeys) := by
  induction a with
  | nil => simpa using b
  | member _ ih => exact .member (ih b)
  | index row source generated _ ih =>
    exact .index row source generated (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b))

/-- Successful preparation yields a receipt for every original step, without
assuming comparisons or path selection have executed. -/
theorem of_prepare {context : SourceCoreCompatibleDataPlaces.Context} {fuel : Nat} {route : Route} {invalid : Word}
    {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      Steps context.checked fuel missing route.steps 0 prepared.steps prepared.keys := by
  unfold prepare at accepted
  obtain ⟨state, loopAccepted, accepted⟩ := CompatibleEncoding.bind_ok accepted
  let invariant := fun seen (state : List PreparedStep × List (ExpressionId × Ty)) =>
    Steps context.checked fuel missing seen 0 state.1 state.2
  have generated : invariant route.steps state := by
    apply CompatibleMemberCertificates.forIn_preserves loopAccepted invariant
    · exact .nil
    · intro seen item remaining state outcome decomposition previous accepted
      obtain ⟨steps, keys⟩ := state
      cases item with
      | member dataType index branches fieldType =>
        simp only [pure, Except.pure, Except.ok.injEq] at accepted
        subst outcome
        refine ⟨_, rfl, ?_⟩
        simpa only [invariant, List.append_nil] using previous.append (.member (dataType := dataType) (index := index) (branches := branches) (fieldType := fieldType) .nil)
      | index layout key valueType =>
        dsimp only at accepted
        cases row : context.checked.catalog.entries[layout.dataType.index]? with
        | none => simp [row, throw, throwThe, bind, Except.bind] at accepted
        | some entry =>
          simp only [row] at accepted
          cases source : entry.sourceType <;> try (simp [source, throw, throwThe, bind, Except.bind] at accepted)
          case mapping sourceKey recordedValue =>
            simp only [pure, Except.pure] at accepted
            cases generated : SourceCoreCompatibleDataEquality.prepare fuel context.checked sourceKey with
            | error error => simp [generated, Except.mapError] at accepted
            | ok comparison =>
              simp only [generated, Except.mapError, Except.ok.injEq] at accepted
              subst outcome
              refine ⟨_, rfl, ?_⟩
              simpa only [invariant, Nat.zero_add] using previous.append (.index (key := key) (valueType := valueType) row source generated .nil)
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst prepared
  exact ⟨rfl, rfl, generated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
/-! Actual compatible route compilation produces source-independent path
receipts. Member rows retain raw-field views; index rows retain actual key
occurrences, catalog layout and source/native projection checks. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

private theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : TypeSystem.Ty} {type : Ty} (accepted : project checked site source = .ok type) :
    checked.catalog.project source = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases generated : checked.catalog.project source with
  | error error => simp [generated, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · rename_i valid
      simp only [pure, Except.pure, Except.map, Except.mapError, Except.ok.injEq] at accepted
      subst type
      exact ⟨rfl, Ty.isWellFormed_sound valid⟩
    · cases accepted

structure IndexSite (checked : Checked) (source : TypedSource)
    (root keySource valueSource : TypeSystem.Ty) (key : ExpressionId) (layout : OrderedMapping.Layout) : Prop where
  view : SourceCoreRawMetadata.runtimeType root = .mapping keySource valueSource
  owner : key.occurrence.owner = source.owner
  node : ∃ node, source.lookupExpression? key = some node ∧ checked.catalog.project node.type = .ok layout.keyType
  keyProjection : checked.catalog.project keySource = .ok layout.keyType
  valueProjection : checked.catalog.project valueSource = .ok layout.valueType
  identity : checked.catalog.identity? root = some layout.dataType
  registered : layout.Registered checked.catalog.definitions

inductive Path (checked : Checked) (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) :
    TypeSystem.Ty → List PlaceProjection → List Step → TypeSystem.Ty → Prop where
  | nil {type} : Path checked source site type [] [] type
  | member {root field leaf name index signature arguments identity branches fieldType projections steps}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType)
      (tail : Path checked source site field projections steps leaf) :
      Path checked source site root (.member name index :: projections) (.member identity index branches fieldType :: steps) leaf
  | index {root keySource valueSource leaf key layout projections steps}
      (certificate : IndexSite checked source root keySource valueSource key layout)
      (tail : Path checked source site valueSource projections steps leaf) :
      Path checked source site root (.index key :: projections) (.index layout key valueSource :: steps) leaf

private theorem member_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {binder : Resolved.LocalId} {root field : TypeSystem.Ty} {index : Nat} {step : Step}
    (accepted : memberStep checked checked.signatures site binder root index = .ok (step, field)) :
    ∃ signature arguments identity branches fieldType,
      SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments) ∧
      checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature] ∧
      step = .member identity index branches fieldType ∧
      CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType := by
  have whole := accepted
  unfold memberStep at accepted
  cases nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) with
  | none => simp [nominal, throw, bind, Except.bind] at accepted
  | some parts =>
    obtain ⟨declaration, arguments⟩ := parts
    simp only [nominal, pure, Except.pure, bind, Except.bind] at accepted
    cases selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | nil => simp [selected, throw] at accepted
    | cons signature rest => cases rest with
      | cons other rest => simp [selected, throw] at accepted
      | nil =>
        have member : signature ∈ checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) := by rw [selected]; simp
        have sourceId : signature.id = declaration := by simpa using (List.mem_filter.mp member).2
        have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments) := by simpa only [sourceId] using nominal
        have selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature] := by simpa only [sourceId] using selected
        obtain ⟨identity, branches, fieldType, shape, certificate⟩ :=
          CompatibleMemberCertificates.certificate_of_memberStep nominal selected whole
        exact ⟨signature, arguments, identity, branches, fieldType, by simp only [sourceId], selected, shape, certificate⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

/-- Extraction follows actual routeSteps; it neither evaluates keys nor
assumes a source-expression compiler or a helper evaluation. -/
theorem of_routeSteps {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {binder : Resolved.LocalId} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (accepted : routeSteps checked checked.signatures source site binder root projections = .ok (steps, leaf)) :
    Path checked source site root projections steps leaf := by
  induction projections generalizing root steps leaf with
  | nil =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact .nil
  | cons projection projections ih =>
    cases projection with
    | member name index =>
      simp only [routeSteps] at accepted
      obtain ⟨⟨step, field⟩, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
      obtain ⟨signature, arguments, identity, branches, fieldType, nominal, selected, rfl, certificate⟩ := member_facts generated
      obtain ⟨⟨rest, selectedLeaf⟩, restGenerated, accepted⟩ := CompatibleEncoding.bind_ok accepted
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact .member nominal selected certificate (ih restGenerated)
    | index key =>
      simp only [routeSteps] at accepted
      cases view : SourceCoreRawMetadata.runtimeType root <;> try (simp [view, throw, throwThe, bind, Except.bind] at accepted)
      case mapping keySource valueSource =>
        simp only [pure, Except.pure] at accepted
        by_cases owner : key.occurrence.owner = source.owner
        · simp only [owner, ↓reduceIte] at accepted
          cases nodeFound : source.lookupExpression? key with
          | none => simp [nodeFound] at accepted
          | some node =>
            simp only [nodeFound] at accepted
            obtain ⟨nodeType, nodeProjected, accepted⟩ := CompatibleEncoding.bind_ok accepted
            obtain ⟨keyType, keyProjected, accepted⟩ := CompatibleEncoding.bind_ok accepted
            obtain ⟨checkedUnit, typesEqual, remainder⟩ := CompatibleEncoding.bind_ok accepted
            have unitEq : checkedUnit = () := Subsingleton.elim _ _
            have same := ensureType_ok (unitEq ▸ typesEqual)
            rw [← same] at nodeProjected
            obtain ⟨valueType, valueProjected, accepted⟩ := CompatibleEncoding.bind_ok remainder
            cases identity : checked.catalog.identity? root with
            | none => simp [identity] at accepted
            | some dataType =>
              simp only [identity] at accepted
              split at accepted
              · rename_i registered
                obtain ⟨⟨rest, selectedLeaf⟩, restGenerated, accepted⟩ := CompatibleEncoding.bind_ok accepted
                simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
                obtain ⟨rfl, rfl⟩ := accepted
                exact .index ⟨view, owner, ⟨node, nodeFound, (project_facts nodeProjected).1⟩,
                  (project_facts keyProjected).1, (project_facts valueProjected).1,
                  identity, ⟨(project_facts keyProjected).2, (project_facts valueProjected).2, registered⟩⟩ (ih restGenerated)
              · cases accepted
        · simp [owner] at accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePreparedPath
/-! Actual route and preparation receipts compose into a path whose index
comparisons are the certified generated comparisons. Catalog identity lookup,
not equality of native mapping carrier types, authenticates each key type. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

inductive PreparedPath (checked : Checked) (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) :
    TypeSystem.Ty → List PlaceProjection → Nat → List PreparedStep → List (ExpressionId × Ty) → TypeSystem.Ty → Prop where
  | nil {type position} : PreparedPath checked source site type [] position [] [] type
  | member {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType)
      (tail : PreparedPath checked source site field projections position steps keys leaf) :
      PreparedPath checked source site root (.member name index :: projections) position (.member identity index branches fieldType :: steps) keys leaf
  | index {root keySource valueSource leaf key layout projections steps position keys comparison missing}
      (certificate : IndexSite checked source root keySource valueSource key layout)
      (generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩)
      (tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf) :
      PreparedPath checked source site root (.index key :: projections) position
        (.index ⟨layout, key, position, comparison, missing⟩ :: steps) ((key, layout.keyType) :: keys) leaf

/-- Every retained index carries its actual raw catalog/site certificate,
generated helper and original missing-reason provider. -/
def Providers {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    (missing : TypeSystem.Ty → Word) {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {position : Nat} {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (_path : PreparedPath checked source site root projections position steps keys leaf) : Prop :=
  ∀ reference, PreparedStep.index reference ∈ steps →
    ∃ actualRoot keySource valueSource,
      IndexSite checked source actualRoot keySource valueSource reference.key reference.layout ∧
      Nonempty (CompatibleMapping.Index checked reference) ∧ reference.missing = missing valueSource

/-- The original static path fold retains its exact output and provider receipts. -/
theorem Path.prepared_with_providers {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (path : Path checked source site root projections steps leaf)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {prepared : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (generated : CompatibleMixedPreparation.Steps checked fuel missing steps position prepared keys) :
    ∃ actual : PreparedPath checked source site root projections position prepared keys leaf, Providers missing actual := by
  induction path generalizing position prepared keys with
  | nil => cases generated; exact ⟨.nil, fun _ member => by cases member⟩
  | member nominal selected certificate tail ih => cases generated with
    | member generated =>
      obtain ⟨actual, providers⟩ := ih generated
      refine ⟨.member nominal selected certificate actual, ?_⟩
      intro reference member
      rcases List.mem_cons.mp member with impossible | member
      · cases impossible
      · exact providers reference member
  | @index root keySource valueSource leaf key layout projections steps certificate tail ih => cases generated with
    | @index _ _ _ _ _ _ _ entry sourceKey recordedValue row sourceEq comparison generated rest =>
      obtain ⟨actualEntry, actualRow, actualSource⟩ := CompatibleEquality.identity_entry certificate.identity
      have entries := Option.some.inj (actualRow.symm.trans row)
      subst actualEntry
      rw [certificate.view, sourceEq] at actualSource
      have sourceKeys := TypeSystem.Ty.mapping.inj actualSource
      obtain ⟨rfl, rfl⟩ := sourceKeys
      obtain ⟨actual, providers⟩ := ih rest
      refine ⟨.index certificate (CompatibleMapping.Index.of_generated generated certificate.keyProjection) actual, ?_⟩
      intro reference member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact ⟨root, _, _, certificate,
          ⟨CompatibleMapping.Index.of_generated generated certificate.keyProjection⟩, rfl⟩
      · exact providers reference member

 theorem Path.prepared {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (path : Path checked source site root projections steps leaf)
    {fuel position : Nat} {missing : TypeSystem.Ty → Word} {prepared : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (generated : CompatibleMixedPreparation.Steps checked fuel missing steps position prepared keys) :
    PreparedPath checked source site root projections position prepared keys leaf := by
  obtain ⟨actual, _⟩ := path.prepared_with_providers generated
  exact actual

/-- Real routeSteps and real prepare success suffice for all static path
receipts. No comparator, key, getter, or setter execution is supplied. -/
theorem prepared_of_success_with_providers {context : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {route : Route}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (routed : routeSteps context.checked context.checked.signatures source site binder root projections = .ok (route.steps, leaf))
    (generated : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      ∃ actual : PreparedPath context.checked source site root projections 0 prepared.steps prepared.keys leaf,
        Providers missing actual := by
  obtain ⟨sameRoute, sameInvalid, preparedSteps⟩ := CompatibleMixedPreparation.of_prepare generated
  exact ⟨sameRoute, sameInvalid, (of_routeSteps routed).prepared_with_providers preparedSteps⟩

theorem prepared_of_success {context : SourceCoreCompatibleDataPlaces.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {route : Route}
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (routed : routeSteps context.checked context.checked.signatures source site binder root projections = .ok (route.steps, leaf))
    (generated : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      PreparedPath context.checked source site root projections 0 prepared.steps prepared.keys leaf := by
  obtain ⟨sameRoute, sameInvalid, actual, _⟩ := prepared_of_success_with_providers routed generated
  exact ⟨sameRoute, sameInvalid, actual⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathArguments
/-! Already evaluated index values are attached to the statically prepared
path in source order. This is a payload relation, not a child evaluation or a
replacement compiler. Native projection equality does not authenticate keys. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload

inductive Arguments (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (values : List Value) :
    {root : TypeSystem.Ty} → {projections : List PlaceProjection} → {position : Nat} →
    {steps : List PreparedStep} → {keys : List (ExpressionId × Ty)} → {leaf : TypeSystem.Ty} →
    PreparedPath checked source site root projections position steps keys leaf → List Dynamic.EvaluatedProjection → Prop where
  | nil {type position} : Arguments checked registry functions mapping world source site values (PreparedPath.nil (type := type) (position := position)) []
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
      {branches : List MemberBranch} {fieldType : Ty} {projections : List PlaceProjection}
      {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
      {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
      {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root) field signature arguments index identity branches fieldType}
      {tail : PreparedPath checked source site field projections position steps keys leaf}
      {resolved : List Dynamic.EvaluatedProjection}
      (rest : Arguments checked registry functions mapping world source site values tail resolved) :
      Arguments checked registry functions mapping world source site values (.member (name := name) nominal selected certificate tail)
        (.member name index :: resolved)
  | index {root keySource valueSource leaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
      {projections : List PlaceProjection} {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {comparison : Expr} {missing : Word}
      {certificate : IndexSite checked source root keySource valueSource key layout}
      {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
      {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
      {lookup : Dynamic.Value} {value : Value} {resolved : List Dynamic.EvaluatedProjection}
      (keyAt : values[position]? = some value)
      (represented : ValueRep checked registry functions mapping world keySource lookup value layout.keyType)
      (rest : Arguments checked registry functions mapping world source site values tail resolved) :
      Arguments checked registry functions mapping world source site values (.index certificate generated tail)
        (.index lookup :: resolved)

def readCost (checked : Checked) : List PreparedStep → Nat
  | [] => 0
  | .member _ _ _ _ :: rest => readCost checked rest
  | .index _ :: rest => checked.catalog.entries.length + 1 + readCost checked rest

def updateCost (checked : Checked) : List PreparedStep → Nat
  | [] => 0
  | .member _ _ _ _ :: rest => updateCost checked rest
  | .index _ :: rest => 2 * (checked.catalog.entries.length + 1) + updateCost checked rest

theorem IndexSite.projection {checked : Checked} {source : TypedSource} {root keySource valueSource : TypeSystem.Ty}
    {key : ExpressionId} {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout) :
    checked.catalog.project root = .ok (SourceCoreMappingWithDefault.type layout) := by
  have identity : checked.catalog.identity? (.mapping keySource valueSource) = some layout.dataType := by
    have normalized : checked.catalog.identity? (SourceCoreRawMetadata.runtimeType root) = checked.catalog.identity? root := by
      simp only [SourceCoreCompatibleCatalog.Catalog.identity?, SourceCoreRawMetadata.runtimeType_idempotent]
    rw [certificate.view] at normalized
    exact normalized.trans certificate.identity
  rw [← checked.catalog.project_runtimeType root, certificate.view]
  exact CompatibleEncoding.mapping_project identity certificate.keyProjection certificate.valueProjection

theorem IndexSite.mappingFields {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {root keySource valueSource : TypeSystem.Ty}
    {key : ExpressionId} {layout : OrderedMapping.Layout}
    (certificate : IndexSite checked source root keySource valueSource key layout)
    {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type) :
    ∃ header nativeEntries fallback,
      value = CompatibleMapping.Transport.carrier header fallback layout nativeEntries ∧
      type = SourceCoreMappingWithDefault.type layout ∧
      keySource = SourceCoreRawMetadata.runtimeType rawKey ∧ valueSource = SourceCoreRawMetadata.runtimeType rawValue ∧
      CompatibleMapping.Fields checked registry functions mapping world rawKey rawValue entries header layout nativeEntries fallback := by
  obtain ⟨header, actual, nativeEntries, fallback, valueEq, typeEq, view, fields⟩ := CompatibleMapping.mapping_fields represented rfl
  have sameType := Except.ok.inj (represented.projection.symm.trans certificate.projection)
  have sameLayout := CompatibleMapping.registered_layout_eq fields.registered certificate.registered (typeEq.symm.trans sameType)
  subst actual
  have types := TypeSystem.Ty.mapping.inj (certificate.view.symm.trans view)
  exact ⟨header, nativeEntries, fallback, valueEq, sameType, types.1, types.2, fields⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathReads
/-! Independent successful source reads and authenticated input/key payloads
construct the semantic tree for the actual prepared selector. No child or
helper Core evaluation is an assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

theorem valueAt_unique {values : List Dynamic.Value} {index : Nat} {a b : Dynamic.Value}
    (first : Dynamic.ValueAt values index a) (second : Dynamic.ValueAt values index b) : a = b := by
  induction first generalizing b with
  | head => cases second; rfl
  | tail _ ih => cases second with | tail rest => exact ih rest

 theorem Arguments.readTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current selected : Dynamic.Value} {value : Value} {type leafCore : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (leafProjected : checked.catalog.project leaf = .ok leafCore)
    (read : Dynamic.ProjectionsRead (some current) resolved (some selected)) (prepared : Prepared) :
    ReadTree checked registry functions mapping world prepared keys leaf leafCore root current value steps resolved selected (readCost checked steps) := by
  induction arguments generalizing current selected value type with
  | nil =>
    cases read
    have same := Except.ok.inj (represented.projection.symm.trans leafProjected)
    subst type
    exact .leaf represented
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases read with
    | member sourceAt tailRead =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      rw [valueEq]
      exact .member fields owner branchAt constructor branchTypes sourceField coreField found coreAt
        (.compatible view (ih (.compatible view.symm childRelated) leafProjected tailRead))
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {child : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (selectedAt : Selected lookup entries rawValue child)
        (tailRead : Dynamic.ProjectionsRead (some child) resolved (some selected)) :
        ReadTree checked registry functions mapping world prepared keys leaf leafCore root
          (.mapping rawKey rawValue entries) value (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
          (.index lookup :: resolved) selected (checked.catalog.entries.length + 1 + readCost checked steps) := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      rw [valueEq]
      refine .compatible (certificate.view.trans (by rw [keyView, valueView]; rfl))
        (.mapping generated fields (.compatible rawKeyView keyRelated) keyAt selectedAt ?_)
      intro native related
      exact .compatible rawValueView (ih (.compatible rawValueView.symm related) leafProjected tailRead)
    cases read with
    | indexFound found tailRead => exact finish represented (.found found) tailRead
    | indexDefault absent defaulted tailRead => exact finish represented (.default absent defaulted) tailRead

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathUpdates
/-! Actual prepared paths automatically produce full update certificates
from independent source updates and authenticated replacement/key payloads.
The relation preserves raw metadata and every untouched sibling/entry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

private theorem replaced_eq_set {values output : List Dynamic.Value} {index : Nat} {replacement : Dynamic.Value}
    (replaced : Dynamic.ValuesReplaceAt values index replacement output) : output = values.set index replacement := by
  induction replaced with
  | head => rfl
  | @tail previous rest index replacement updated replaced ih => exact congrArg (List.cons previous) ih

 theorem Arguments.updateTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current updated replacementSource : Dynamic.Value} {value replacement : Value} {type replacementType : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (replacementRelated : ValueRep checked registry functions mapping world leaf replacementSource replacement replacementType)
    (update : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some current) resolved updated) (prepared : Prepared) :
    UpdateTree checked registry functions mapping world prepared keys replacementSource replacement root current value type steps resolved updated (updateCost checked steps) := by
  induction arguments generalizing current updated value type with
  | nil =>
    cases update with
    | leaf same =>
      subst updated
      have same := Except.ok.inj (represented.projection.symm.trans replacementRelated.projection)
      subst type
      exact .leaf replacementRelated
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases update with
    | member sourceAt tailUpdate replaced =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      rw [valueEq, typeEq, replaced_eq_set replaced]
      exact .member fields owner branchAt constructor branchTypes sourceField coreField found coreAt
        (.compatible view (ih (.compatible view.symm childRelated) replacementRelated tailUpdate))
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries updatedEntries : List (Dynamic.Value × Dynamic.Value)} {child updatedChild : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (selectedAt : Selected lookup entries rawValue child)
        (tailUpdate : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some child) resolved updatedChild)
        (inserted : Dynamic.MappingInsert lookup updatedChild entries updatedEntries) :
        UpdateTree checked registry functions mapping world prepared keys replacementSource replacement root
          (.mapping rawKey rawValue entries) value type (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
          (.index lookup :: resolved) (.mapping rawKey rawValue updatedEntries) (2 * (checked.catalog.entries.length + 1) + updateCost checked steps) := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      rw [valueEq, typeEq]
      refine .compatible (certificate.view.trans (by rw [keyView, valueView]; rfl))
        (.mapping generated fields (.compatible rawKeyView keyRelated) keyAt selectedAt ?_ inserted)
      intro native related
      exact .compatible rawValueView (ih (.compatible rawValueView.symm related) replacementRelated tailUpdate)
    cases update with
    | indexFound found tailUpdate inserted => exact finish represented (.found found) tailUpdate inserted
    | indexDefault absent defaulted tailUpdate inserted => exact finish represented (.default absent defaulted) tailUpdate inserted

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathFaultToken
/-! Fault tokens are determined by the first unavailable raw default and its
authenticated registry ID. This source-level receipt is independent of native
child representations and lets recursive fault trees use one exact token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

inductive FaultToken (checked : Checked) (registry : SourceCoreRawMetadata.Registry) :
    Dynamic.Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {rawKey rawValue lookup entries index steps projections header}
      (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
      (typed : Dynamic.ValueRuntimeTypeMatches lookup rawKey)
      (absent : Dynamic.MappingAbsent lookup entries) (unavailable : ¬ Dynamic.Defaultable rawValue) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        (.missingMappingDefault rawValue) (index.missing.add header) (checked.catalog.entries.length + 1)
  | member {metadata values name position child dataType branches fieldType steps projections reason token count}
      (atField : Dynamic.ValueAt values position child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.constructed metadata values) (.member dataType position branches fieldType :: steps)
        (.member name position :: projections) reason token count
  | found {rawKey rawValue lookup entries index steps projections child reason token count}
      (typed : Dynamic.ValueRuntimeTypeMatches lookup rawKey)
      (found : Dynamic.MappingLookup lookup entries child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        reason token (checked.catalog.entries.length + 1 + count)
  | default {rawKey rawValue lookup entries index steps projections child reason token count}
      (typed : Dynamic.ValueRuntimeTypeMatches lookup rawKey)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue rawValue child)
      (tail : FaultToken checked registry child steps projections reason token count) :
      FaultToken checked registry (.mapping rawKey rawValue entries) (.index index :: steps) (.index lookup :: projections)
        reason token (checked.catalog.entries.length + 1 + count)

 theorem FaultToken.functional {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {source : Dynamic.Value} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    {reason : Dynamic.SemanticFault} {left right : Word} {firstCount secondCount : Nat}
    (first : FaultToken checked registry source steps projections reason left firstCount)
    (second : FaultToken checked registry source steps projections reason right secondCount) :
    left = right ∧ firstCount = secondCount := by
  induction first generalizing right secondCount with
  | missing metadata typed absent unavailable => cases second with
    | missing other _ _ _ => exact ⟨congrArg _ ((metadata.ids_equal_iff other).mpr rfl), rfl⟩
    | found _ found _ => exact (absent.excludes_lookup found).elim
    | default _ _ defaulted _ => exact (unavailable defaulted.defaultable).elim
  | member atField tail ih => cases second with
    | member other second =>
      have same := valueAt_unique atField other
      cases same
      exact ih second
  | found typed found tail ih => cases second with
    | missing _ _ absent _ => exact (absent.excludes_lookup found).elim
    | found _ other second =>
      have same := found.functional other
      cases same
      obtain ⟨token, count⟩ := ih second
      exact ⟨token, congrArg (fun n => _ + n) count⟩
    | default _ absent _ _ => exact (absent.excludes_lookup found).elim
  | default typed absent defaulted tail ih => cases second with
    | missing _ _ _ unavailable => exact (unavailable defaulted.defaultable).elim
    | found _ found _ => exact (absent.excludes_lookup found).elim
    | default _ _ other second =>
      have same := defaulted.functional other
      cases same
      obtain ⟨token, count⟩ := ih second
      exact ⟨token, congrArg (fun n => _ + n) count⟩

 theorem EntriesRep.lookup_payload {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {rawKey rawValue : TypeSystem.Ty} {lookup selected : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries} {keyType valueType : Ty}
    (related : CompatiblePayload.EntriesRep checked registry functions mapping world rawKey rawValue sources entries keyType valueType)
    (found : Dynamic.MappingLookup lookup sources selected) :
    ∃ value, ValueRep checked registry functions mapping world rawValue selected value valueType := by
  induction found generalizing entries with
  | head _ => cases related with | entry key value rest => exact ⟨_, value⟩
  | tail _ found ih => cases related with | entry key value rest => exact ih rest

 theorem Selected.represented {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {rawKey rawValue : TypeSystem.Ty} {lookup selected : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {header : Word} {layout : OrderedMapping.Layout}
    {entries : OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world rawKey rawValue sources header layout entries fallback)
    (selectedAt : Selected lookup sources rawValue selected) :
    ∃ value, ValueRep checked registry functions mapping world rawValue selected value layout.valueType := by
  cases selectedAt with
  | found found => exact EntriesRep.lookup_payload fields.stored found
  | default absent defaulted => cases fields.default with
    | absent unavailable => exact (unavailable defaulted.defaultable).elim
    | present other related =>
      have same := defaulted.functional other
      exact ⟨_, same.symm ▸ related⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathMissingTerminal
/-! The actual unavailable index is a suffix of the same certified path.
Its raw mapping fields, lookup, owning header and static type views remain
attached to that exact Source/site/position and generated native index. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

/-- Membership retains the genuine prepared path receipt at every prefix. -/
inductive IndexInPath {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {terminalRoot terminalLeaf : TypeSystem.Ty} {terminalProjections : List PlaceProjection}
    {terminalPosition : Nat} {terminalSteps : List PreparedStep} {terminalKeys : List (ExpressionId × Ty)}
    (terminal : PreparedPath checked source site terminalRoot terminalProjections terminalPosition
      terminalSteps terminalKeys terminalLeaf) :
    {root : TypeSystem.Ty} → {projections : List PlaceProjection} → {position : Nat} →
    {steps : List PreparedStep} → {keys : List (ExpressionId × Ty)} → {leaf : TypeSystem.Ty} →
    PreparedPath checked source site root projections position steps keys leaf → Prop where
  | here : IndexInPath terminal terminal
  | member {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
      {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
      {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
      {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
        field signature arguments index identity branches fieldType}
      {tail : PreparedPath checked source site field projections position steps keys leaf}
      (found : IndexInPath terminal tail) :
      IndexInPath terminal (.member (name := name) nominal selected certificate tail)
  | index {root keySource valueSource leaf key layout projections steps position keys comparison missing}
      {certificate : IndexSite checked source root keySource valueSource key layout}
      {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
      {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
      (found : IndexInPath terminal tail) : IndexInPath terminal (.index certificate generated tail)

/-- This existential retains the actual terminal mapping and lookup rather
than interpreting arbitrary raw metadata carrying the same numeric token. -/
def MissingTerminal {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    (reason : Dynamic.SemanticFault) (token : Word) : Prop :=
  ∃ terminalRoot keySource valueSource terminalLeaf key layout terminalProjections terminalSteps terminalPosition
      terminalKeys comparison missing,
    ∃ (certificate : IndexSite checked source terminalRoot keySource valueSource key layout)
      (generated : CompatibleMapping.Index checked ⟨layout, key, terminalPosition, comparison, missing⟩)
      (tail : PreparedPath checked source site valueSource terminalProjections (terminalPosition + 1)
        terminalSteps terminalKeys terminalLeaf),
      IndexInPath (.index certificate generated tail) path ∧
      ∃ rawKey rawValue entries header nativeEntries fallback lookup,
        Fields checked registry functions mapping world rawKey rawValue entries header layout nativeEntries fallback ∧
        keySource = SourceCoreRawMetadata.runtimeType rawKey ∧
        valueSource = SourceCoreRawMetadata.runtimeType rawValue ∧
        Dynamic.ValueRuntimeTypeMatches lookup rawKey ∧ Dynamic.MappingAbsent lookup entries ∧
        ¬ Dynamic.Defaultable rawValue ∧ reason = .missingMappingDefault rawValue ∧ token = missing.add header

/-- A genuine member prefix forwards the same terminal witness. -/
theorem MissingTerminal.member {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root field leaf name index signature arguments identity branches fieldType projections steps position keys}
    {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
    {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
    {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
      field signature arguments index identity branches fieldType}
    {tail : PreparedPath checked source site field projections position steps keys leaf}
    {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world tail reason token) :
    MissingTerminal (registry := registry) functions mapping world (.member (name := name) nominal selected certificate tail) reason token := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest, found, raw⟩ := terminal
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest,
    IndexInPath.member (nominal := nominal) (selected := selected) (certificate := certificate) found, raw⟩

/-- A genuine successful index prefix forwards the same terminal witness. -/
theorem MissingTerminal.index {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root keySource valueSource leaf key layout projections steps position keys comparison missing}
    {certificate : IndexSite checked source root keySource valueSource key layout}
    {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
    {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
    {reason : Dynamic.SemanticFault} {token : Word}
    (terminal : MissingTerminal (registry := registry) functions mapping world tail reason token) :
    MissingTerminal (registry := registry) functions mapping world (.index certificate generated tail) reason token := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest, found, raw⟩ := terminal
  exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, terminalCertificate, terminalGenerated, rest,
    IndexInPath.index (certificate := certificate) (generated := generated) found, raw⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
/-! Independent source structural faults determine the exact emitted token
and automatically construct the actual selector/updater fault trees. Normalized key
guards come from the source fault trace; helper execution is never assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CompatibleMapping CompatibleMapping.MixedPaths

 theorem Arguments.faultTree_with_terminal {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current : Dynamic.Value} {value : Value} {type : Ty} {reason : Dynamic.SemanticFault}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (fault : Dynamic.ProjectionsFaults (some current) resolved reason) (prepared : Prepared) :
    ∃ token count, FaultToken checked registry current steps resolved reason token count ∧
      FaultTree checked registry functions mapping world prepared keys current value type steps resolved reason token count ∧
      MissingTerminal (registry := registry) functions mapping world path reason token := by
  induction arguments generalizing current value type with
  | nil => cases fault
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    cases fault with
    | member sourceAt tailFault =>
      obtain ⟨tag, id, values, types, valueEq, typeEq, fields⟩ := constructor_fields represented rfl
      obtain ⟨owner, branch, actual, sourceChild, valueChild, branchAt, constructor, branchTypes,
        sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
      have same := valueAt_unique found sourceAt
      subst sourceChild
      obtain ⟨token, count, receipt, tree, terminal⟩ := ih (.compatible view.symm childRelated) tailFault
      refine ⟨token, count, .member found receipt, ?_, ?_⟩
      · rw [valueEq, typeEq, owner]
        exact .member fields owner branchAt branchTypes sourceField coreField found coreAt tree
      · exact MissingTerminal.member (nominal := nominal) (selected := selectedSignature)
          (certificate := certificate) terminal
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    have finish {rawKey rawValue : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)} {child : Dynamic.Value}
        (represented : ValueRep checked registry functions mapping world root (.mapping rawKey rawValue entries) value type)
        (typed : Dynamic.ValueRuntimeTypeMatches lookup rawKey)
        (selectedAt : Selected lookup entries rawValue child)
        (tailFault : Dynamic.ProjectionsFaults (some child) resolved reason) :
        ∃ token count,
          FaultToken checked registry (.mapping rawKey rawValue entries) (.index ⟨layout, key, position, comparison, missing⟩ :: steps)
            (.index lookup :: resolved) reason token count ∧
          FaultTree checked registry functions mapping world prepared keys (.mapping rawKey rawValue entries) value type
            (.index ⟨layout, key, position, comparison, missing⟩ :: steps) (.index lookup :: resolved) reason token count ∧
          MissingTerminal (registry := registry) functions mapping world (.index certificate generated tail) reason token := by
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      have rawKeyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType keySource := by
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      have rawValueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType valueSource := by
        rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]
      obtain ⟨native, related⟩ := Selected.represented fields selectedAt
      obtain ⟨token, count, receipt, tree, terminal⟩ := ih (.compatible rawValueView.symm related) tailFault
      refine ⟨token, checked.catalog.entries.length + 1 + count, ?_, ?_,
        MissingTerminal.index (certificate := certificate) (generated := generated) terminal⟩
      · cases selectedAt with
        | found found => exact .found typed found receipt
        | default absent defaulted => exact .default typed absent defaulted receipt
      · rw [valueEq, typeEq]
        refine .mapping generated fields (.compatible rawKeyView keyRelated) typed keyAt selectedAt ?_
        intro native related
        obtain ⟨other, otherCount, otherReceipt, otherTree, _⟩ := ih (.compatible rawValueView.symm related) tailFault
        obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
        exact otherTree
    cases fault with
    | indexDefaultUnavailable typed absent unavailable =>
      obtain ⟨header, nativeEntries, fallback, valueEq, typeEq, keyView, valueView, fields⟩ := certificate.mappingFields represented
      refine ⟨missing.add header, checked.catalog.entries.length + 1, .missing fields.metadata typed absent unavailable, ?_, ?_⟩
      · rw [valueEq, typeEq]
        refine .missing generated fields (.compatible ?_ keyRelated) typed keyAt absent unavailable
        rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]
      · exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, certificate, generated, tail, .here,
          _, _, _, header, nativeEntries, fallback, _, fields, keyView, valueView, typed, absent, unavailable, rfl, rfl⟩
    | indexFound typed found tailFault => exact finish represented typed (.found found) tailFault
    | indexDefault typed absent defaulted tailFault => exact finish represented typed (.default absent defaulted) tailFault

 theorem Arguments.faultTree {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {current : Dynamic.Value} {value : Value} {type : Ty} {reason : Dynamic.SemanticFault}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (fault : Dynamic.ProjectionsFaults (some current) resolved reason) (prepared : Prepared) :
    ∃ token count, FaultToken checked registry current steps resolved reason token count ∧
      FaultTree checked registry functions mapping world prepared keys current value type steps resolved reason token count := by
  obtain ⟨token, count, receipt, tree, _⟩ := arguments.faultTree_with_terminal represented fault prepared
  exact ⟨token, count, receipt, tree⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMixedRoute
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
/-! A local live-root receipt for compatible places. It refers to the existing
location map and source heap read, without introducing a competing heap model.
The payload is authenticated independently of native typing. Generated virtual
mapping values leave the actual optional root cell uninitialized. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

structure RootRead (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (heap : Dynamic.Heap) (store : Store) (location : Dynamic.Location) (target : Location)
    (cell : Dynamic.Cell) (optional : Value) (source : Dynamic.Value) (value : Value) : Prop where
  sourceRead : Dynamic.Heap.Reads heap location cell
  reference : ReferenceRepresents mapping world location target prepared.route.rootType
  nativeRead : store.read? target = some optional
  input : RootInput prepared cell optional source value
  payload : ValueRep checked registry functions mapping world cell.type source value prepared.route.rootType

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}

theorem RootRead.initialized {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some source, none⟩)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (native : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world sourceType source value prepared.route.rootType) :
    RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some source, none⟩ (.inRight .unit value) source value :=
  ⟨read, reference, native, .initialized, represented⟩

/-- Actual describe's encoded literal supplies the virtual value and its full
raw-header/default representation; the source and native cells stay absent. -/
theorem RootRead.virtual {context : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {key valueType : TypeSystem.Ty}
    (generated : VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (projected : context.checked.catalog.project (.mapping key valueType) = .ok prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (native : store.read? target = some (.inLeft prepared.route.rootType .unit)) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨header, layout, fallback, fields, input⟩ := generated_root generated functions mapping world extension
  have represented := fields.represents
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  exact ⟨_, read, reference, native, input, same ▸ represented⟩

/-- The helper can append administrative closures, but cannot overwrite the
live root. The finite Core world is recovered from the actual checker proof. -/
theorem RootRead.after_append {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional source value)
    {futureWorld : StoreTyping} {suffix : Store}
    (extension : WorldExtends world futureWorld) :
    RootRead checked registry functions mapping futureWorld prepared heap (store ++ suffix) location target cell optional source value := by
  have bound : target < store.length := (List.getElem?_eq_some_iff.mp root.nativeRead).1
  exact ⟨root.sourceRead, root.reference.extend (.refl _) extension,
    by simpa [Store.read?, List.getElem?_append_left bound] using root.nativeRead,
    root.input, root.payload.extend (.refl _) (.refl _) extension⟩

/-- An actual getter whose input loads the live cell. Its structural recursion
is supplied by the independently constructed tree, never an assumed execution. -/
theorem readTree_at {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot selected : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {leaf : TypeSystem.Ty} {leafCore : Ty} {resolved : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : ReadTree checked registry functions mapping world prepared keys leaf leafCore cell.type sourceRoot rootValue
      prepared.steps resolved selected count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native finalStore administrative,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected) ∧
      ValueRep checked registry functions mapping world leaf selected native leafCore ∧
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨native, finalStore, administrative, meaning, represented, evaluated, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (rootValue :: input :: environment) store (.var 0) (.second (.var 1)) (.var rfl) (.second (.var rfl))
  refine ⟨native, finalStore, administrative, root.input.initial, meaning, represented, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead) (keysSelected.evaluates store))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- Exact missing-default diagnostics from an actual live load, including the
raw metadata word of the inner mapping where selection stopped. -/
theorem faultTree_at {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {resolved : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys sourceRoot rootValue prepared.route.rootType
      prepared.steps resolved reason token count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧ Dynamic.ProjectionsFaults (some sourceRoot) resolved reason ∧
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨finalStore, administrative, meaning, evaluated, _, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (rootValue :: input :: environment) store (.var 0) (.second (.var 1)) (.var 0) (.var rfl) (.second (.var rfl))
  refine ⟨finalStore, administrative, root.input.initial, meaning, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead) (keysSelected.evaluates store))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- An absent ordinary root fails before any projection or helper allocation.
The source observation is root absence, not an invented mapping/default fault. -/
theorem ordinary_absent_at {sourceType : TypeSystem.Ty}
    (ordinary : ∀ key value, sourceType ≠ .mapping key value)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, none, none⟩)
    (native : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (noVirtual : prepared.route.rootMapping = none) (nonempty : prepared.steps ≠ [])
    {keys : Value} (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression keys) :
    Dynamic.Heap.Reads heap location ⟨sourceType, none, none⟩ ∧
      Dynamic.RootInitialValue ⟨sourceType, none, none⟩ none ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
  refine ⟨read, .uninitialized ?_, .of_evaluates ?_⟩
  · rintro ⟨key, value, same⟩
    exact ordinary key value same
  · apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (keysSelected.evaluates store))
    cases steps : prepared.steps with
    | nil => exact (nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSnapshot
/-! Live snapshot observations from real static path receipts and independent
source reads/faults. Only pure reference/key selections are premises; native
load, recursive helpers, sufficient fuel and completed-run reflection are
constructed here. A final checker receipt gives the extended finite world.
This is the local snapshot phase, not an alternate whole-heap relation or a
proof of source key/RHS expression lowering. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

/-- Finite Core preservation accounts for the real helper allocations. Every
old cell, including the live root and prior administrative cells, is unchanged. -/
theorem evaluation_frame {definitions : DataEnvironment} {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {context : Core.Context} {store after : Store} {expression : Expr} {value : Value} {type : Ty}
    (storeTyped : RuntimeStoreHasTypes world store definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (expressionTyped : HasType context expression type definitions)
    (evaluated : Evaluates environment store expression value after)
    {suffix : Store} (appended : after = store ++ suffix) :
    ∃ futureWorld, WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after definitions ∧
      RuntimeValueHasType futureWorld value type definitions ∧ AdministrativePreserved mapping store mapping after := by
  obtain ⟨futureWorld, extension, storeTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluated expressionTyped environmentTyped storeTyped
  refine ⟨futureWorld, extension, storeTyped, valueTyped, ?_⟩
  subst after
  intro index absent bound
  exact ⟨absent, by simp [Store.read?, List.getElem?_append_left bound]⟩

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}
  {leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
  {path : PreparedPath checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {identities : Dynamic.Value → Word → Prop}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}

/-- Successful independent path reads produce actual live-root Core snapshots;
the final root receipt certifies that virtual defaults did not initialize it. -/
theorem read_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType)
    {selected : Dynamic.Value} (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (nonempty : prepared.steps ≠ []) (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (storeTyped : RuntimeStoreHasTypes world store ambient.definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native after administrative futureWorld,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      ValueRep checked registry functions mapping futureWorld leaf selected native prepared.route.leafType ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word (.inRight .unit native)) after ∧
      WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after ambient.definitions ∧
      RuntimeValueHasType futureWorld (.inRight .word (.inRight .unit native))
        (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      AdministrativePreserved mapping store mapping after ∧
      after = store ++ administrative ∧ administrative.length = readCost checked prepared.steps := by
  have tree := arguments.readTree root.payload leafProjected read prepared
  obtain ⟨native, after, administrative, initial, _, represented, evaluated, appended, counted⟩ :=
    readTree_at root tree nonempty faithful functionLeaves keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
  obtain ⟨futureWorld, extension, typedStore, typedValue, frame⟩ :=
    evaluation_frame (mapping := mapping) storeTyped environmentTyped helperTyped evaluated appended
  refine ⟨native, after, administrative, futureWorld, initial,
    represented.extend (.refl _) (.refl _) extension, .of_evaluates evaluated,
    extension, typedStore, typedValue, ?_, frame, appended, counted⟩
  rw [appended]
  exact root.after_append extension

/-- Source structural faults determine the exact raw metadata token and every
completed live getter result. The actual source and native root cells survive. -/
theorem fault_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
    (nonempty : prepared.steps ≠ []) (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (storeTyped : RuntimeStoreHasTypes world store ambient.definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ token count after administrative futureWorld,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken checked registry sourceRoot prepared.steps resolved reason token count ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) after ∧
      WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after ambient.definitions ∧
      RuntimeValueHasType futureWorld (.inLeft prepared.optionalLeaf (.word token))
        (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, initial, _, evaluated, appended, counted⟩ :=
    faultTree_at root tree nonempty faithful functionLeaves keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
  obtain ⟨futureWorld, extension, typedStore, typedValue, frame⟩ :=
    evaluation_frame (mapping := mapping) storeTyped environmentTyped helperTyped evaluated appended
  refine ⟨token, count, after, administrative, futureWorld, initial, receipt, .of_evaluates evaluated,
    extension, typedStore, typedValue, ?_, frame, appended, counted⟩
  rw [appended]
  exact root.after_append extension

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleHeap
/-! The compatible carrier instantiates the existing generic heap relation.
The storage catalog supplies only identical Core definitions and environment
layout. Its strict source projection is never used: the explicit projection
relation is the actual compatible catalog projection. Registry extension
transports authenticated payloads while preserving the same physical store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleHeap
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatiblePlaceLiveRoot

abbrev projects (catalog : SourceCoreCompatibleCatalog.Catalog) : GenericHeap.Projection :=
  fun source payload => catalog.project source = .ok payload

def payloadModel (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :
    GenericHeap.PayloadModel (storageCatalog checked.catalog) (projects checked.catalog) ambient.definitions where
  Represents := ValueRep checked registry functions
  projection := ValueRep.projection
  runtime_hasType := ValueRep.runtime_hasType
  extend := fun related maps worlds => related.extend (.refl _) maps worlds

abbrev HeapRepresents (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) :=
  GenericHeap.HeapRepresents (payloadModel checked registry functions)

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {heap : Dynamic.Heap} {store : Store}

theorem cell_extend_registry {future : SourceCoreRawMetadata.Registry} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (represented : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    GenericHeap.CellRepresents (payloadModel checked future functions) mapping world cell value type := by
  cases represented with
  | uninitialized projected => exact .uninitialized projected
  | initialized related => exact .initialized (related.extend extension (.refl _) (.refl _))

theorem HeapRepresents.extend_registry {future : SourceCoreRawMetadata.Registry}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    HeapRepresents checked future functions mapping world heap store := by
  refine ⟨heaps.length_eq, heaps.injective, heaps.runtime_hasTypes, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, type, read, typed, native, related⟩ := heaps.cells mapped
  exact ⟨cell, value, type, read, typed, native, cell_extend_registry related extension⟩

/-- Recover the exact optional payload at an existing represented reference.
Native world lookup equates payload types; source cell identity comes from the
independent heap read, never from native type equality. -/
theorem HeapRepresents.read_at {location : Dynamic.Location} {target : Location} {type : Ty} {cell : Dynamic.Cell}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell) :
    ∃ value, store.read? target = some value ∧
      GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell value type := by
  obtain ⟨actual, value, payload, sourceRead, typed, native, represented⟩ := heaps.cells reference.mapped
  have same := sourceRead.functional read
  subst actual
  have samePayload : payload = type := by
    simpa [OptionalCell.cellType] using Option.some.inj (typed.symm.trans reference.typed)
  subst payload
  exact ⟨value, native, represented⟩

/-- Live initialized-root facts are consequences of the common heap relation. -/
theorem HeapRepresents.initialized_root {prepared : Prepared} {sourceType : TypeSystem.Ty}
    {location : Dynamic.Location} {target : Location} {sourceRoot : Dynamic.Value}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some sourceRoot, none⟩) :
    ∃ value, RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some sourceRoot, none⟩ (.inRight .unit value) sourceRoot value := by
  obtain ⟨optional, native, represented⟩ := heaps.read_at reference read
  cases represented with
  | initialized related => exact ⟨_, read, reference, native, .initialized, related⟩

/-- The declared mapping remains absent on both heaps while the actual
compiler's encoded empty/default value is supplied to the structural getter. -/
theorem HeapRepresents.virtual_root {context : SourceCoreCompatibleDataPlaces.Context}
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {prepared : Prepared}
    {key valueType : TypeSystem.Ty} {location : Dynamic.Location} {target : Location}
    (heaps : HeapRepresents context.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (generated : CompatibleMapping.VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨optional, native, represented⟩ := heaps.read_at reference read
  cases represented with
  | uninitialized projection => exact RootRead.virtual generated extension projection read reference native

/-- All source cells survive the snapshot's administrative suffix. No new
source location or source heap update is introduced by a virtual read. -/
theorem HeapRepresents.after_snapshot {futureWorld : StoreTyping} {after suffix : Store}
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    (extension : WorldExtends world futureWorld)
    (typed : RuntimeStoreHasTypes futureWorld after ambient.definitions)
    (appended : after = store ++ suffix) :
    HeapRepresents checked registry functions mapping futureWorld heap after := by
  subst after
  exact DataMappingHeap.heap_append heaps extension typed

end Solcore.SourceSemantics.CoreLowering.CompatibleHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
/-! Closed retained types recover source validity in the real residual scope.
Every substitution row, including unused parameters, is checked. These lemmas
never change a source context's residual flag. The actual compiler must supply
the closedness receipts separately; native type tags cannot supply them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
open Frontend SourceInference

theorem no_free_variables (type : TypeSystem.Ty)
    (closed : SourceCoreDataCatalog.closed type = true) : type.freeVariables = [] := by
  induction type with
  | «variable» | «parameter» | error => simp [SourceCoreDataCatalog.closed] at closed
  | constructor => rfl
  | application left right leftIH rightIH
  | function left right leftIH rightIH
  | product left right leftIH rightIH
  | mapping left right leftIH rightIH =>
    simp only [SourceCoreDataCatalog.closed, Bool.and_eq_true] at closed
    simp only [TypeSystem.Ty.freeVariables, leftIH closed.1, rightIH closed.2]
    rfl
  | proxy inner ih | comptime inner ih => exact ih closed

theorem well_formed {context : Context} {type : TypeSystem.Ty}
    (admissible : TypeAdmissible context type) (lexical : context.typeVariables = [])
    (closed : SourceCoreDataCatalog.closed type = true) : TypeWellFormed context type := by
  refine ⟨admissible.binders, ?_⟩
  simpa [admissibleTypeVariables, lexical, no_free_variables type closed] using admissible.typeWellScoped

def ClosedParameterRange (substitution : TypeSystem.ParameterSubstitution) : Prop :=
  ∀ parameter replacement, (parameter, replacement) ∈ substitution →
    SourceCoreDataCatalog.closed replacement = true

theorem range_well_formed {context : Context} {substitution : TypeSystem.ParameterSubstitution}
    (admissible : ParameterSubstitution.RangeAdmissible context substitution)
    (lexical : context.typeVariables = []) (closed : ClosedParameterRange substitution) :
    ParameterSubstitution.RangeWellFormed context substitution := by
  intro parameter replacement member
  exact well_formed (admissible parameter replacement member) lexical (closed parameter replacement member)

theorem declaration_valid {context : Context} {instantiation : DeclarationInstantiation}
    (admissible : DeclarationInstantiation.Admissible context instantiation)
    (lexical : context.typeVariables = [])
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    DeclarationInstantiation.Valid context instantiation := by
  cases admissible with
  | intro signature member declaration domain range type predicates parameterComptime returnComptime =>
    exact .intro signature member declaration domain (range_well_formed range lexical closed)
      type predicates parameterComptime returnComptime

theorem constructor_valid {context : Context} {instantiation : DataConstructorInstantiation}
    (admissible : DataConstructorInstantiation.Admissible context instantiation)
    (lexical : context.typeVariables = [])
    (closed : ClosedParameterRange instantiation.parameterSubstitution) :
    DataConstructorInstantiation.Valid context instantiation := by
  cases admissible with
  | intro data signature member signatureMember owner constructor domain range payload result =>
    exact .intro data signature member signatureMember owner constructor domain
      (range_well_formed range lexical closed) payload result

end Solcore.SourceSemantics.CoreLowering.CompatibleSourceInstantiationClosure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
/-! Independent total path selection on authenticated compatible payloads.
Runtime-compatible raw aliases retain their metadata, ordered entries and raw
default. Actual native helpers are not premises: this source classification
will construct their finite semantic trees and reflect completed executions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleMixedRoute CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces

private theorem source_mapping {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {key result}, SourceCoreRawMetadata.runtimeType sourceType = .mapping key result →
      ∃ rawKey rawResult entries, source = .mapping rawKey rawResult entries := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy => intro _ _ impossible; cases impossible
  | constructed metadata =>
    intro key result view
    have facts := CompatibleConstructorMetadata.facts metadata.authenticated
    cases facts with
    | mk signature constructor arguments _ _ _ _ _ resultType =>
      rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal] at view
      have impossible := congrArg SourceCoreDataCatalog.nominalParts view
      simp only [DataPatternAuthenticity.nominalParts_nominal, SourceCoreDataCatalog.nominalParts, reduceCtorEq] at impossible
  | mappingValue => intro _ _ _; exact ⟨_, _, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (same.symm.trans view)
  | nil | cons | empty | entry | absent | present => trivial

private theorem source_constructor {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

/-- Every represented root and key vector selects one represented leaf or
produces an independent missing-default fault. Function leaves require only
the explicit shallow metadata law, not any function-body evaluation. -/
theorem read_or_fault {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {keys : List Value}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf}
    {resolved : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (functionTypes : FunctionRuntimeViews functions)
    {current : Dynamic.Value} {value : Value} {type leafCore : Ty}
    (represented : ValueRep checked registry functions mapping world root current value type)
    (leafProjected : checked.catalog.project leaf = .ok leafCore) :
    (∃ selected native, Dynamic.ProjectionsRead (some current) resolved (some selected) ∧
      ValueRep checked registry functions mapping world leaf selected native leafCore) ∨
    ∃ reason, Dynamic.ProjectionsFaults (some current) resolved reason := by
  induction arguments generalizing current value type with
  | nil =>
    have same := Except.ok.inj (represented.projection.symm.trans leafProjected)
    exact .inl ⟨current, value, .nil, same ▸ represented⟩
  | @member root field leaf name index signature typeArguments identity branches fieldType projections steps position keySites nominal selectedSignature certificate tail resolved arguments ih =>
    obtain ⟨metadata, payloads, rfl⟩ := source_constructor represented nominal
    obtain ⟨tag, id, values, types, _, _, fields⟩ := constructor_fields represented rfl
    obtain ⟨owner, branch, actual, child, native, branchAt, constructor, branchTypes,
      sourceField, view, coreField, found, coreAt, childRelated⟩ := certificate.select nominal selectedSignature fields
    rcases ih (.compatible view.symm childRelated) leafProjected with ⟨selected, output, read, related⟩ | ⟨reason, fault⟩
    · exact .inl ⟨selected, output, .member found read, related⟩
    · exact .inr ⟨reason, .member found fault⟩
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail lookup keyValue resolved keyAt keyRelated arguments ih =>
    obtain ⟨rawKey, rawValue, entries, rfl⟩ := source_mapping represented certificate.view
    obtain ⟨header, nativeEntries, fallback, _, _, keyView, valueView, fields⟩ := certificate.mappingFields represented
    have rawKeyRelated : ValueRep checked registry functions mapping world rawKey lookup keyValue layout.keyType :=
      .compatible (by rw [keyView, SourceCoreRawMetadata.runtimeType_idempotent]) keyRelated
    have typed := rawKeyRelated.source_runtimeView functionTypes
    have finish {child : Dynamic.Value} (selected : Selected lookup entries rawValue child) :
        (∃ selected native, Dynamic.ProjectionsRead (some (.mapping rawKey rawValue entries)) (.index lookup :: resolved) (some selected) ∧
          ValueRep checked registry functions mapping world leaf selected native leafCore) ∨
        ∃ reason, Dynamic.ProjectionsFaults (some (.mapping rawKey rawValue entries)) (.index lookup :: resolved) reason := by
      obtain ⟨native, related⟩ := CompatibleMixedRoute.Selected.represented fields selected
      have childRelated : ValueRep checked registry functions mapping world valueSource child native layout.valueType :=
        .compatible (by rw [valueView, SourceCoreRawMetadata.runtimeType_idempotent]) related
      rcases ih childRelated leafProjected with ⟨selectedValue, output, read, result⟩ | ⟨reason, fault⟩
      · refine .inl ⟨selectedValue, output, ?_, result⟩
        cases selected with
        | found found => exact .indexFound found read
        | default absent defaulted => exact .indexDefault absent defaulted read
      · refine .inr ⟨reason, ?_⟩
        cases selected with
        | found found => exact .indexFound typed found fault
        | default absent defaulted => exact .indexDefault typed absent defaulted fault
    obtain ⟨found, classification⟩ := lookup_total lookup entries
    cases classification with
    | found found => exact finish (.found found)
    | absent absent =>
      cases fields.default with
      | absent missing => exact .inr ⟨_, .indexDefaultUnavailable typed absent missing⟩
      | present defaulted related => exact finish (.default absent defaulted)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
/-! The final mapped write for the projection-parametric shared heap.
This reuses the source write relation; compatibility changes the payload model,
not the store operation, location map, or administrative frame invariant. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
open Core Frontend SourceInference GeneralHeap DataEquality

/-- Any completed actual storeCell commits precisely the reconstructed source
root once. The mapped heap and old administrative cells are preserved at the
same world; helper allocations have already been reflected before this step. -/
theorem reflects_storeCell {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {type : Ty}
    {sourceValue : Dynamic.Value} {value result : Value}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell)
    (represented : model.Represents mapping world cell.type sourceValue value type)
    {environment : Environment} {referenceExpression valueExpression : Expr}
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType type) target))
    (valueSelected : Selects environment valueExpression value)
    (completed : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) result finalStore) :
    ∃ after, result = .unit ∧ Dynamic.Heap.Writes heap location (some sourceValue) after ∧
      GenericHeap.HeapRepresents model mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧
      finalStore.read? target = some (.inRight .unit value) := by
  have written := DataPlaceCommitReflection.source_writes read sourceValue
  obtain ⟨updated, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read represented written
  obtain ⟨_, optional, _, _, _, coreRead, _⟩ := heaps.cells reference.mapped
  have actual : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) .unit updated :=
    .storeCell (referenceSelected.evaluates store) coreRead (.inRight (valueSelected.evaluates store)) coreWritten
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed actual
  exact ⟨_, rfl, written, finalHeaps, frame, .of_write written, Store.write?_reads_written coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCommitReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
/-! The actual catalog registration supplies closure of its Source entries.
Successful projections then establish raw Source closure, including erased
staging wrappers. Native well-formedness and occurrence graph closure are
separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
open Core Frontend SourceInference SourceCoreCompatibleCatalog CompatibleCatalogRegistrationPrefix

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Canonicalization preserves exactly the closed-type predicate. -/
theorem runtime_closed (type : TypeSystem.Ty) :
    SourceCoreDataCatalog.closed (SourceCoreRawMetadata.runtimeType type) = SourceCoreDataCatalog.closed type := by
  induction type <;> simp_all [SourceCoreDataCatalog.closed, SourceCoreRawMetadata.runtimeType]

/-- The authentic factory starts with no entries and retains Source closure
through the original registration fold and its unchanged checking suffix. -/
theorem prepare_closed {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List SourceCoreRawMetadata.Metadata} {limits : SourceCoreRawMetadata.Limits}
    {profile : Bool} {checked : Checked}
    (accepted : SourceCoreCompatibleCatalog.prepare signatures fuel types metadata limits profile = .ok checked) :
    ClosedSources checked.catalog := by
  unfold SourceCoreCompatibleCatalog.prepare at accepted
  obtain ⟨registered, generated, accepted⟩ := bind_ok accepted
  obtain ⟨catalog, nativeTypes⟩ := registered
  have closed : ClosedSources catalog :=
    ((registered_prefix_with_closed signatures fuel).2 _ _ _ _ generated).closed (by
      intro entry member; cases member)
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  obtain ⟨seen, original⟩ := discovered
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact closed
    · cases accepted

/-- A genuine identity lookup selects a closed original registry entry. -/
theorem identity_closed {catalog : Catalog} (closed : ClosedSources catalog)
    {type : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? type = some identity) : SourceCoreDataCatalog.closed type = true := by
  unfold Catalog.identity? at found
  cases selected : catalog.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) with
  | none => simp only [selected, Option.map_none] at found; cases found
  | some item =>
    have member := List.fst_mem_of_mem_zipIdx (List.mem_of_find?_eq_some selected)
    have same := of_decide_eq_true (List.find?_some (p := fun item : Entry × Nat =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) selected)
    have actual := closed item.1 member
    rw [same, runtime_closed] at actual
    exact actual

/-- Static projection inversion supplies closure of the raw Source type.
This proof traverses type syntax and performs no execution. -/
theorem project_closed {catalog : Catalog} (closed : ClosedSources catalog)
    {type : TypeSystem.Ty} {native : Core.Ty}
    (accepted : catalog.project type = .ok native) : SourceCoreDataCatalog.closed type = true := by
  induction type generalizing native with
  | constructor constructor => rfl
  | product left right leftIH rightIH
  | function left right leftIH rightIH =>
    unfold Catalog.project at accepted
    obtain ⟨first, leftAccepted, remaining⟩ := bind_ok accepted
    obtain ⟨last, rightAccepted, _⟩ := bind_ok remaining
    change (SourceCoreDataCatalog.closed left && SourceCoreDataCatalog.closed right) = true
    rw [leftIH leftAccepted, rightIH rightAccepted]
    rfl
  | comptime inner ih => exact ih accepted
  | mapping key value _ _ =>
    unfold Catalog.project at accepted
    cases found : catalog.identity? (.mapping key value) with
    | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
    | some identity => exact identity_closed closed found
  | «variable» id | parameter id | error | application left right _ _ | proxy inner _ =>
    unfold Catalog.project at accepted
    split at accepted
    · exact identity_closed closed (by assumption)
    · cases accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AmbientHeap
/-! Reindex the common heap/environment relation along an authenticated Core
definition suffix. Source cells and locations are unchanged. Payload semantics
are transferred by a separate model inclusion, not inferred from native typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend GeneralHeap

namespace DataHeap

theorem EnvRepresents.extend_definitions {catalog : SourceCoreDataCatalog.Catalog}
    {before after : DataEnvironment} (extension : before.Extends after)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {scope : SourceCoreLocalCell.Scope} {source : Dynamic.Environment} {environment : Environment}
    (related : EnvRepresents catalog mapping world administrative scope source environment before) :
    EnvRepresents catalog mapping world administrative scope source environment after := by
  induction related with
  | nil values => exact .nil (values.extend_definitions extension)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih

end DataHeap

namespace GenericHeap

def PayloadModel.Includes {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} (initial : PayloadModel catalog projects before)
    (future : PayloadModel catalog projects after) : Prop :=
  ∀ {mapping world sourceType sourceValue value payload},
    initial.Represents mapping world sourceType sourceValue value payload →
      future.Represents mapping world sourceType sourceValue value payload

theorem CellRepresents.map_model {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} {initial : PayloadModel catalog projects before}
    {future : PayloadModel catalog projects after} (includes : initial.Includes future)
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {value : Value} {type : Ty}
    (related : CellRepresents initial mapping world cell value type) :
    CellRepresents future mapping world cell value type := by
  cases related with
  | uninitialized projected => exact .uninitialized projected
  | initialized represented => exact .initialized (includes represented)

theorem HeapRepresents.extend_definitions {catalog : SourceCoreDataCatalog.Catalog} {projects : Projection}
    {before after : DataEnvironment} {initial : PayloadModel catalog projects before}
    {future : PayloadModel catalog projects after} (includes : initial.Includes future)
    (extension : before.Extends after)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (related : HeapRepresents initial mapping world heap store) :
    HeapRepresents future mapping world heap store := by
  refine ⟨related.length_eq, related.injective, related.runtime_hasTypes.extend_definitions extension, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, type, sourceRead, typed, read, payload⟩ := related.cells mapped
  exact ⟨cell, value, type, sourceRead, typed, read, payload.map_model includes⟩

end GenericHeap
end Solcore.SourceSemantics.CoreLowering
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
/-! The compatible carrier uses the common heap relation under the actual full
Core definition table. The base source catalog and metadata registry remain
unchanged; administrative definitions receive no fabricated source types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
open Core Frontend GeneralHeap CompatiblePayload CompatibleEquality

def payloadModel (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :
    GenericHeap.PayloadModel (storageCatalog checked.catalog) (CompatibleHeap.projects checked.catalog) ambient.definitions where
  Represents := ValueRep checked registry functions
  projection := ValueRep.projection
  runtime_hasType := ValueRep.runtime_hasType
  extend := fun represented maps worlds => represented.extend (.refl _) maps worlds

abbrev HeapRepresents (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient) :=
  GenericHeap.HeapRepresents (payloadModel checked registry functions)

theorem model_base {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    (functions : FunctionModel checked.catalog) :
    payloadModel checked registry functions = CompatibleHeap.payloadModel checked registry functions := rfl

/-- Existing source values and physical store are preserved when moving to a
larger native definition table and an explicitly including function model. -/
theorem extend_definitions {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {before after : AmbientDefinitions checked.catalog.definitions}
    {initial : FunctionModel checked.catalog before} {future : FunctionModel checked.catalog after}
    (includes : initial.Includes future) (extension : before.definitions.Extends after.definitions)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (related : HeapRepresents checked registry initial mapping world heap store) :
    HeapRepresents checked registry future mapping world heap store :=
  GenericHeap.HeapRepresents.extend_definitions
    (fun represented => ValueRep.map_functions includes represented) extension related

end Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
end
