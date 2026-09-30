import Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates

/-! Extraction of authenticated member rows from the actual compiler loop.
Exact source field uniformity is explicit: the executable compiler compares
erased types, whereas independent source place typing retains raw types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues DataPlaceMembers

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- A compiler loop whose successful rows always yield preserves a prefix
invariant through the entire input. This is a proof about `forIn`, not another
executable compiler traversal. -/
private theorem forIn_preserves {α β ε : Type} {items : List α} {initial final : β}
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

/-- One emitted row, with its canonical constructor instantiation and exact
source field. Every check here is a compile-time check. -/
structure Row (checked : Checked) (signatures : ProgramSignatures) (site : SourceCoreElaboration.ErrorSite)
    (root field : TypeSystem.Ty) (substitution : TypeSystem.ParameterSubstitution)
    (identity : DataTypeId) (index : Nat) (input : ProgramDataConstructorSignature × Nat)
    (branch : MemberBranch) : Prop where
  authenticated : checked.catalog.resolveConstructor signatures
    ⟨input.1.id, substitution, input.1.payloadTypes.map substitution.apply, root⟩ = .ok branch.constructor
  position : branch.constructor = ⟨identity, input.2⟩
  fieldLookup : (input.1.payloadTypes.map substitution.apply)[index]? = some field
  payloads : (input.1.payloadTypes.map substitution.apply).mapM (project checked site) = .ok branch.payloadTypes

theorem Row.branchCertificate {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {root field : TypeSystem.Ty}
    {substitution : TypeSystem.ParameterSubstitution} {identity : DataTypeId} {index : Nat}
    {input : ProgramDataConstructorSignature × Nat} {branch : MemberBranch}
    (row : Row checked signatures site root field substitution identity index input branch) :
    BranchCertificate checked signatures root field index branch :=
  .intro ⟨input.1.id, substitution, input.1.payloadTypes.map substitution.apply, root⟩ rfl
    row.authenticated row.fieldLookup (mapM_length row.payloads)

/-- Uniformity is stated over the exact retained source payload types. This
is the static condition required to match `UniformMemberProjection`. -/
def Uniform (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty)
    (index : Nat) (field : TypeSystem.Ty) : Prop :=
  ∀ constructor ∈ signature.constructors,
    (constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)))[index]? = some field

/-- Static result of actual member compilation under exact source uniformity. -/
structure Certificate (checked : Checked) (signatures : ProgramSignatures)
    (site : SourceCoreElaboration.ErrorSite) (root field : TypeSystem.Ty)
    (signature : ProgramDataSignature) (arguments : List TypeSystem.Ty) (index : Nat)
    (identity : DataTypeId) (branches : List MemberBranch) (fieldType : Ty) : Prop where
  identityLookup : checked.catalog.identity? root = some identity
  projectedField : project checked site field = .ok fieldType
  rows : ListRel (Row checked signatures site root field (signature.parameters.zip arguments) identity index)
    signature.constructors.zipIdx branches

/-- Exact-field source typing and actual compiler success produce all finite
row certificates automatically. No getter/updater evaluation is assumed. -/
theorem certificate_of_memberStep {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {root field : TypeSystem.Ty}
    {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {index : Nat}
    {step : Step} {selectedField : TypeSystem.Ty}
    (erased : SourceCoreDataCatalog.erase root = root)
    (nominal : SourceCoreDataCatalog.nominalParts root = some (signature.id, arguments))
    (signatureSelected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (uniform : Uniform signature arguments index field)
    (accepted : memberStep checked signatures site binder root index = .ok (step, selectedField)) :
    ∃ identity branches fieldType, selectedField = field ∧ step = .member identity index branches fieldType ∧
      Certificate checked signatures site root field signature arguments index identity branches fieldType := by
  unfold memberStep at accepted
  simp only [erased, nominal, signatureSelected, pure, Except.pure, bind, Except.bind] at accepted
  by_cases valid : signature.parameters.length = arguments.length ∧ signature.constructors ≠ []
  · have count := valid.1
    have nonempty := valid.2
    simp only [count, decide_true, List.isEmpty_eq_false_iff.mpr nonempty, Bool.not_false,
      Bool.and_self, ↓reduceIte] at accepted
    cases identityLookup : checked.catalog.identity? root with
    | none => simp [identityLookup, throw] at accepted
    | some identity =>
      simp only [identityLookup] at accepted
      obtain ⟨state, loopAccepted, accepted⟩ := bind_ok accepted
      let row := Row checked signatures site root field (signature.parameters.zip arguments) identity index
      let invariant := fun (seen : List (ProgramDataConstructorSignature × Nat))
          (state : Option TypeSystem.Ty × List MemberBranch) =>
        (state.1 = none ↔ seen = []) ∧ (state.1 = none ∨ state.1 = some field) ∧ ListRel row seen state.2
      have certified : invariant signature.constructors.zipIdx state := by
        apply forIn_preserves loopAccepted invariant
        · exact ⟨by simp, .inl rfl, .nil⟩
        · intro seen item remaining state outcome decomposition previous rowAccepted
          obtain ⟨constructor, position⟩ := item
          obtain ⟨selected, branches⟩ := state
          obtain ⟨noneIff, selectedValid, rows⟩ := previous
          have member : (constructor, position) ∈ signature.constructors.zipIdx := by
            rw [decomposition]
            simp
          have ctorMember : constructor ∈ signature.constructors := by
            obtain ⟨_, bound, equal⟩ := List.mem_zipIdx member
            simp only [Nat.zero_add, Nat.sub_zero] at bound equal
            rw [equal]
            exact List.getElem_mem bound
          have fieldLookup := uniform constructor ctorMember
          dsimp only at rowAccepted
          simp only [fieldLookup] at rowAccepted
          rcases selectedValid with rfl | rfl
          all_goals
            simp only [↓reduceIte] at rowAccepted
            cases resolved : checked.catalog.resolveConstructor signatures
                ⟨constructor.id, signature.parameters.zip arguments,
                  constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)), root⟩ with
            | error error => simp [resolved, Except.mapError] at rowAccepted
            | ok tag =>
              simp only [resolved, Except.mapError] at rowAccepted
              by_cases tagValid : tag.owner = identity ∧ tag.index = position
              · simp only [tagValid.1, tagValid.2, decide_true, Bool.and_self, ↓reduceIte] at rowAccepted
                obtain ⟨payloadTypes, payloads, rowAccepted⟩ := bind_ok rowAccepted
                simp only [Except.ok.injEq] at rowAccepted
                subst outcome
                refine ⟨_, rfl, ?_⟩
                refine ⟨?_, .inr rfl, DataPatternExecution.ListRel.append rows (.cons ?_ .nil)⟩
                · simp
                · exact ⟨resolved, by cases tag; simp_all, fieldLookup, payloads⟩
              · simp [tagValid, Bool.and_eq_true, throw] at rowAccepted
      obtain ⟨noneIff, selectedValid, rows⟩ := certified
      have selected : state.1 = some field := by
        rcases selectedValid with absent | present
        · exact False.elim (nonempty (List.zipIdx_eq_nil_iff.mp (noneIff.mp absent)))
        · exact present
      simp only [selected] at accepted
      obtain ⟨fieldType, projected, accepted⟩ := bind_ok accepted
      simp only [Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact ⟨identity, state.2, fieldType, rfl, rfl, identityLookup, projected, rows⟩
  · simp [valid, Bool.and_eq_true, throw] at accepted

private theorem relation_at {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : ListRel relation inputs outputs) {index : Nat} {input : α}
    (found : inputs[index]? = some input) : ∃ output, outputs[index]? = some output ∧ relation input output := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih => cases index with
    | zero => cases found; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

/-- The extracted rows cover every authenticated runtime constructor. Coverage
comes from its actual source signature, without assuming that arbitrary Core
constructor tags carry genuine source metadata. -/
theorem Certificate.layout {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {root field : TypeSystem.Ty}
    {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {index : Nat}
    {identity : DataTypeId} {branches : List MemberBranch} {fieldType : Ty}
    (nominal : SourceCoreDataCatalog.nominalParts root = some (signature.id, arguments))
    (signatureSelected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (certificate : Certificate checked signatures site root field signature arguments index identity branches fieldType) :
    MemberLayout checked signatures root field identity index branches := by
  refine ⟨⟨signature.id, arguments, nominal⟩, ?_⟩
  intro metadata tag result authenticated
  obtain ⟨actualSignature, constructor, signatureFound, constructorFound, parameters, sourceResult, payloads⟩ :=
    DataPatternAuthenticity.metadataFacts authenticated
  have signatureMember : actualSignature ∈ signatures.dataTypes.filter
      (fun data => decide (data.id = metadata.constructor.dataType)) := by rw [signatureFound]; simp
  have signatureId : actualSignature.id = metadata.constructor.dataType := by simpa using (List.mem_filter.mp signatureMember).2
  have nominalEqual := congrArg SourceCoreDataCatalog.nominalParts (sourceResult.symm.trans result)
  simp only [DataPatternAuthenticity.nominalParts_nominal, nominal, Option.some.injEq, Prod.mk.injEq] at nominalEqual
  have sameSignature : actualSignature = signature := by
    rw [← signatureId, nominalEqual.1, signatureSelected] at signatureFound
    exact (List.singleton_inj.mp signatureFound).symm
  subst actualSignature
  have substitution : metadata.parameterSubstitution = signature.parameters.zip arguments :=
    List.zip_of_prod parameters nominalEqual.2
  have constructorMember : constructor ∈ signature.constructors.filter
      (fun candidate => decide (candidate.id = metadata.constructor)) := by rw [constructorFound]; simp
  have constructorId : constructor.id = metadata.constructor := by simpa using (List.mem_filter.mp constructorMember).2
  obtain ⟨position, found⟩ := List.getElem?_of_mem (List.mem_filter.mp constructorMember).1
  have zipped : signature.constructors.zipIdx[position]? = some (constructor, position) := by
    simp [List.getElem?_zipIdx, found]
  obtain ⟨branch, branchFound, row⟩ := relation_at certificate.rows zipped
  have canonical : (⟨constructor.id, signature.parameters.zip arguments,
      constructor.payloadTypes.map (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip arguments)), root⟩ :
      DataConstructorInstantiation) = metadata := by
    cases metadata
    simp_all
  have sameTag : branch.constructor = tag := by
    have checked := row.authenticated
    rw [canonical, authenticated] at checked
    exact (Except.ok.inj checked).symm
  have owner : tag.owner = identity := by rw [← sameTag, row.position]
  refine ⟨owner, branch, ?_, sameTag, ?_, ?_⟩
  · have indexEq : tag.index = position := by rw [← sameTag, row.position]
    simpa [indexEq] using branchFound
  · have fields := row.fieldLookup
    have payloadEq := congrArg DataConstructorInstantiation.payloadTypes canonical
    simpa only [← payloadEq] using fields
  · have length := mapM_length row.payloads
    have payloadEq := congrArg DataConstructorInstantiation.payloadTypes canonical
    simpa only [← payloadEq] using length

/-- Static member-only path profile. Exact field uniformity and raw type
identity are retained at every level; index/mapping projections are excluded. -/
inductive Profile (signatures : ProgramSignatures) :
    TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} : Profile signatures type [] type
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {rest : List PlaceProjection}
      (erased : SourceCoreDataCatalog.erase root = root)
      (nominal : SourceCoreDataCatalog.nominalParts root = some (signature.id, arguments))
      (selected : signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (uniform : Uniform signature arguments index field)
      (tail : Profile signatures field rest leaf) :
      Profile signatures root (.member name index :: rest) leaf

inductive RawMembers (checked : Checked) (signatures : ProgramSignatures) :
    TypeSystem.Ty → List Step → List Dynamic.EvaluatedProjection → TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} : RawMembers checked signatures type [] [] type
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch}
      {fieldType : Ty} {name : String} {steps : List Step} {projections : List Dynamic.EvaluatedProjection}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (tail : RawMembers checked signatures field steps projections leaf) :
      RawMembers checked signatures root (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf

/-- Retain member names and indices while dropping no evaluated index values:
this profile contains no index expressions. -/
inductive ProjectionNames : List PlaceProjection → List Dynamic.EvaluatedProjection → Prop where
  | nil : ProjectionNames [] []
  | member {name : String} {index : Nat} {source : List PlaceProjection} {target : List Dynamic.EvaluatedProjection}
      (tail : ProjectionNames source target) : ProjectionNames (.member name index :: source) (.member name index :: target)

theorem routeSteps_members {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {root leaf selectedField : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (profile : Profile signatures root projections leaf)
    (accepted : routeSteps checked signatures source site binder root projections = .ok (steps, selectedField)) :
    selectedField = leaf ∧ ∃ resolved, ProjectionNames projections resolved ∧ RawMembers checked signatures root steps resolved leaf := by
  induction profile generalizing steps selectedField with
  | nil =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨rfl, [], .nil, .nil⟩
  | @member root field leaf name index signature arguments rest erased nominal selected uniform tail ih =>
    simp only [routeSteps] at accepted
    obtain ⟨⟨head, chosen⟩, headAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨identity, branches, coreField, rfl, rfl, certificate⟩ :=
      certificate_of_memberStep erased nominal selected uniform headAccepted
    obtain ⟨⟨remaining, result⟩, tailAccepted, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    obtain ⟨rfl, resolved, names, memberSteps⟩ := ih tailAccepted
    exact ⟨rfl, .member name index :: resolved, .member names,
      .member (Certificate.layout nominal selected certificate) memberSteps⟩

inductive MemberPreparation : List Step → List PreparedStep → Prop where
  | nil : MemberPreparation [] []
  | cons {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {field : Ty}
      {source : List Step} {target : List PreparedStep} (tail : MemberPreparation source target) :
      MemberPreparation (.member dataType index branches field :: source) (.member dataType index branches field :: target)

private theorem MemberPreparation.append {a b : List Step} {x y : List PreparedStep}
    (first : MemberPreparation a x) (second : MemberPreparation b y) : MemberPreparation (a ++ b) (x ++ y) := by
  induction first with
  | nil => exact second
  | cons _ ih => exact .cons ih

private theorem RawMembers.onlyMembers {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List Step} {projections : List Dynamic.EvaluatedProjection}
    (members : RawMembers checked signatures root steps projections leaf) :
    ∀ step ∈ steps, ∃ dataType index branches field, step = .member dataType index branches field := by
  intro step member
  induction members with
  | nil => cases member
  | @member root field leaf dataType index branches fieldType name steps projections layout tail ih =>
    rcases List.mem_cons.mp member with rfl | rest
    · exact ⟨dataType, index, branches, fieldType, rfl⟩
    · exact ih rest

private theorem RawMembers.prepared {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List Step} {projections : List Dynamic.EvaluatedProjection}
    (members : RawMembers checked signatures root steps projections leaf) {prepared : List PreparedStep}
    (generated : MemberPreparation steps prepared) : Members checked signatures root prepared projections leaf := by
  induction members generalizing prepared with
  | nil => cases generated; exact .nil
  | member layout tail ih => cases generated with
    | cons rest => exact .member layout (ih rest)

/-- Member-only preparation copies the already authenticated rows, preserves
the exact route and emits no index expressions. This follows the actual loop. -/
theorem prepare_members {checked : Checked} {signatures : ProgramSignatures} {fuel : Nat}
    {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {root leaf : TypeSystem.Ty} {projections : List Dynamic.EvaluatedProjection}
    (members : RawMembers checked signatures root route.steps projections leaf)
    (accepted : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧ prepared.keys = [] ∧
      Members checked signatures root prepared.steps projections leaf := by
  unfold prepare at accepted
  obtain ⟨state, loopAccepted, accepted⟩ := bind_ok accepted
  let invariant := fun (seen : List Step) (state : List PreparedStep × List (ExpressionId × Ty)) =>
    MemberPreparation seen state.1 ∧ state.2 = []
  have certificate : invariant route.steps state := by
    apply forIn_preserves loopAccepted invariant
    · exact ⟨.nil, rfl⟩
    · intro seen item remaining state outcome decomposition previous rowAccepted
      have member : item ∈ route.steps := by rw [decomposition]; simp
      obtain ⟨dataType, index, branches, field, rfl⟩ := RawMembers.onlyMembers members item member
      simp only [pure, Except.pure, Except.ok.injEq] at rowAccepted
      subst outcome
      exact ⟨_, rfl, MemberPreparation.append previous.1 (.cons .nil), previous.2⟩
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst prepared
  exact ⟨rfl, rfl, certificate.2, RawMembers.prepared members certificate.1⟩

/-- From actual route compilation and actual preparation to the structural
semantic certificate consumed by `Members.getter` and `Members.setter`. -/
theorem route_prepare_members {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {root leaf selectedField : TypeSystem.Ty}
    {projections : List PlaceProjection} {route : Route} {fuel : Nat} {invalid : Word}
    {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (profile : Profile signatures root projections leaf)
    (routed : routeSteps checked signatures source site binder root projections = .ok (route.steps, selectedField))
    (compiled : prepare checked fuel route invalid missing = .ok prepared) :
    selectedField = leaf ∧ prepared.route = route ∧ prepared.invalidProjection = invalid ∧ prepared.keys = [] ∧
      ∃ resolved, ProjectionNames projections resolved ∧ Members checked signatures root prepared.steps resolved leaf := by
  obtain ⟨field, resolved, names, members⟩ := routeSteps_members profile routed
  obtain ⟨sameRoute, token, keys, preparedMembers⟩ := prepare_members members compiled
  exact ⟨field, sameRoute, token, keys, resolved, names, preparedMembers⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates
