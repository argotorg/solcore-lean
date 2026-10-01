import Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedHelpers

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
