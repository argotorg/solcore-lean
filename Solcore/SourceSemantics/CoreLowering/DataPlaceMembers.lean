import Solcore.Frontend.SourceCoreDataPlaces
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity

/-! Finite semantics for the actual generated member getter/updater. The
static layout certificate records constructor-index alignment; it never
assumes an evaluation of a generated child. All nominal input metadata is
authenticated by TypedValueRep. Mapping steps are handled in a separate layer
because their ordinary helper initialization allocates administrative cells. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMembers
open Core Frontend Frontend.SourceInference
open SourceCoreDataPlaces DataEquality DataPatternValues DataPatternExecution DataPatternTypedValues

private theorem ValueAt.lookup {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (selected : Dynamic.ValueAt values index value) : values[index]? = some value := by
  induction selected with
  | head => rfl
  | tail _ ih => exact ih

private theorem valueAt_of_lookup {values : List Dynamic.Value} {index : Nat} {value : Dynamic.Value}
    (selected : values[index]? = some value) : Dynamic.ValueAt values index value := by
  induction values generalizing index with
  | nil => simp at selected
  | cons head tail ih => cases index with
    | zero => cases selected; exact .head
    | succ index => exact .tail (ih selected)

theorem TypedValuesRep.at {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type) :
    ∃ source value, Dynamic.ValueAt sources index source ∧ values[index]? = some value ∧
      TypedValueRep catalog signatures type source value := by
  induction types generalizing sources values index with
  | nil => simp at lookup
  | cons head tail ih =>
    cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact ⟨_, _, .head, rfl, first⟩
      | succ index =>
        obtain ⟨source, value, selected, found, related⟩ := ih rest lookup
        exact ⟨source, value, .tail selected, found, related⟩

private theorem replacement_at {values : List Dynamic.Value} {index : Nat} {previous : Dynamic.Value}
    (selected : Dynamic.ValueAt values index previous) (replacement : Dynamic.Value) :
    Dynamic.ValuesReplaceAt values index replacement (values.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

theorem TypedValuesRep.replace {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type)
    {source : Dynamic.Value} {value : Value} (replacement : TypedValueRep catalog signatures type source value) :
    TypedValuesRep catalog signatures types (sources.set index source) (values.set index value) := by
  induction types generalizing sources values index with
  | nil => simp at lookup
  | cons head tail ih =>
    cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact .cons replacement rest
      | succ index => exact .cons first (ih rest lookup)

private theorem pack_evaluates {environment : Environment} {store : Store}
    {expressions : List Expr} {values : List Value}
    (evaluations : ListRel (fun expression value => Evaluates environment store expression value store) expressions values) :
    Evaluates environment store (pack expressions) (packValues values) store := by
  induction evaluations with
  | nil => exact .unit
  | @cons expression expressions value values first rest ih =>
    cases expressions with
    | nil => cases rest; exact first
    | cons next expressions => cases rest with
      | cons second tail => exact .pair first ih

/-- Reconstruction changes exactly the selected payload and preserves every
other payload value, including references and captured closure environments. -/
theorem replacePacked_evaluates {environment : Environment} {store : Store}
    {index : Nat} {types : List Ty} {values : List Value} {payload replacement : Expr} {value : Value}
    (length : types.length = values.length)
    (selected : Selects environment payload (packValues values))
    (newValue : Selects environment replacement value) :
    Evaluates environment store (replacePacked index types payload replacement)
      (packValues (values.set index value)) store := by
  apply pack_evaluates
  apply ListRel.map (relation := Selects environment) ?_ (fun _ _ path => path.evaluates store)
  apply ListRel.of_lookup (by simpa using length)
  intro position expression actual generated looked
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add, Option.map_map] at generated
  cases typeLookup : types[position]? with
  | none => simp [typeLookup] at generated
  | some type =>
    by_cases same : position = index
    · subst position
      simp [typeLookup] at generated
      subst expression
      have bound : index < values.length := by
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp typeLookup
        omega
      rw [List.getElem?_set_self bound] at looked
      cases looked
      exact newValue
    · simp [typeLookup, same] at generated
      subst expression
      rw [List.getElem?_set_ne (Ne.symm same)] at looked
      exact projectPacked_selects selected length position looked

/-- Static alignment supplied by an authenticated uniform-field route. The
payload projection uses arity, while reconstruction also retains the exact
constructor. There are no runtime evaluation premises in this certificate. -/
structure MemberLayout (checked : Checked) (signatures : ProgramSignatures)
    (root field : TypeSystem.Ty) (dataType : DataTypeId) (index : Nat) (branches : List MemberBranch) : Prop where
  nominal : ∃ declaration arguments, SourceCoreDataCatalog.nominalParts root = some (declaration, arguments)
  constructors : ∀ metadata tag,
    metadata.resultType = root → checked.catalog.resolveConstructor signatures metadata = .ok tag →
    tag.owner = dataType ∧ ∃ branch, branches[tag.index]? = some branch ∧ branch.constructor = tag ∧
      metadata.payloadTypes[index]? = some field ∧ branch.payloadTypes.length = metadata.payloadTypes.length

/-- One finite, authenticated source metadata row for a generated branch. -/
inductive BranchCertificate (checked : Checked) (signatures : ProgramSignatures)
    (root field : TypeSystem.Ty) (index : Nat) (branch : MemberBranch) : Prop where
  | intro (metadata : DataConstructorInstantiation)
      (result : metadata.resultType = root)
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok branch.constructor)
      (fieldLookup : metadata.payloadTypes[index]? = some field)
      (length : branch.payloadTypes.length = metadata.payloadTypes.length) :
      BranchCertificate checked signatures root field index branch

/-- A finite catalog certificate implies layout correctness for every genuine
runtime constructor at the same source type, including recursive values. -/
theorem MemberLayout.of_catalog {checked : Checked} {signatures : ProgramSignatures}
    {root field : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch}
    {definition : DataDefinition}
    (nominal : ∃ declaration arguments, SourceCoreDataCatalog.nominalParts root = some (declaration, arguments))
    (identity : checked.catalog.identity? root = some dataType)
    (registered : checked.catalog.definitions[dataType.index]? = some definition)
    (length : branches.length = definition.constructorPayloadTypes.length)
    (positions : ∀ (position : Nat) (branch : MemberBranch), branches[position]? = some branch → branch.constructor = ⟨dataType, position⟩)
    (certificates : ∀ branch ∈ branches, BranchCertificate checked signatures root field index branch) :
    MemberLayout checked signatures root field dataType index branches := by
  refine ⟨nominal, ?_⟩
  intro metadata tag result authenticated
  have selected := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
  rw [result, identity] at selected
  have owner : tag.owner = dataType := (Option.some.inj selected).symm
  obtain ⟨payloadType, payloadLookup⟩ := SourceCoreDataValues.resolveConstructor_registered authenticated
  have payloadLookup : definition.constructorPayloadTypes[tag.index]? = some payloadType := by
    simpa [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, owner, registered] using payloadLookup
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp payloadLookup
  have branchBound : tag.index < branches.length := by omega
  let branch := branches[tag.index]
  have branchLookup : branches[tag.index]? = some branch := List.getElem?_eq_getElem branchBound
  have sameTag : branch.constructor = tag := by
    rw [positions _ _ branchLookup]
    cases tag
    simp_all
  obtain ⟨canonical, canonicalResult, canonicalAccepted, fieldLookup, payloadLength⟩ :=
    certificates branch (List.mem_of_getElem? branchLookup)
  rw [sameTag] at canonicalAccepted
  have agreement := DataPatternAuthenticity.resolveConstructor_agree authenticated canonicalAccepted (result.trans canonicalResult.symm)
  exact ⟨owner, branch, branchLookup, sameTag, by rw [agreement.payload_types_eq]; exact fieldLookup,
    payloadLength.trans (congrArg List.length agreement.payload_types_eq.symm)⟩

inductive Members (checked : Checked) (signatures : ProgramSignatures) :
    TypeSystem.Ty → List PreparedStep → List Dynamic.EvaluatedProjection → TypeSystem.Ty → Prop where
  | nil {type : TypeSystem.Ty} : Members checked signatures type [] [] type
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch}
      {fieldType : Ty} {name : String} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (tail : Members checked signatures field steps projections leaf) :
      Members checked signatures root (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf


/-- Actual generated selection follows the independent member path and returns
the same leaf. Every child execution is derived by structural induction. -/
theorem Members.select {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    (members : Members checked signatures root steps projections leaf) (prepared : Prepared)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep checked.catalog signatures root sourceValue value) :
    ∃ sourceLeaf coreLeaf, TypedValueRep checked.catalog signatures leaf sourceLeaf coreLeaf ∧
      Dynamic.ProjectionsRead (some sourceValue) projections (some sourceLeaf) ∧
      ∀ environment store current keys, Selects environment current value →
        Evaluates environment store (SourceCoreDataPlaces.select prepared steps current keys)
          (.inRight .word (.inRight .unit coreLeaf)) store := by
  induction members generalizing sourceValue value with
  | nil =>
    exact ⟨sourceValue, value, represented, .nil,
      fun _ store _ _ selected => .inRight (.inRight (selected.evaluates store))⟩
  | @member root field leaf dataType index branches fieldType name steps projections layout tail ih =>
    cases represented with
    | unit | bool | word | integer | product =>
      obtain ⟨_, _, impossible⟩ := layout.nominal
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
    | @constructed type metadata tag declaration typeArguments arguments values nominal result authenticated payloads =>
      obtain ⟨owner, branch, branchLookup, branchConstructor, fieldLookup, payloadLength⟩ := layout.constructors metadata tag result authenticated
      obtain ⟨selectedSource, selectedCore, sourceAt, coreAt, selectedRepresentation⟩ := TypedValuesRep.at payloads fieldLookup
      obtain ⟨sourceLeaf, coreLeaf, leafRepresentation, sourceRead, childExecution⟩ := ih selectedRepresentation
      refine ⟨sourceLeaf, coreLeaf, leafRepresentation, .member sourceAt sourceRead, ?_⟩
      intro environment store current keys selected
      apply Evaluates.matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchLookup, Option.map_some]; rfl)
      exact childExecution _ store _ _
        (projectPacked_selects (Selects.var (index := 0) rfl) (payloadLength.trans (DataPatternTypedValues.TypedValuesRep.length payloads).2) index coreAt)

/-- Actual generated reconstruction uses the current root supplied to this
invocation. It preserves its constructor and all unselected payload values. -/
theorem Members.update {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    (members : Members checked signatures root steps projections leaf) (prepared : Prepared)
    {sourceValue replacementSource : Dynamic.Value} {value replacementValue : Value}
    (represented : TypedValueRep checked.catalog signatures root sourceValue value)
    (replacement : TypedValueRep checked.catalog signatures leaf replacementSource replacementValue) :
    ∃ updatedSource updatedCore, TypedValueRep checked.catalog signatures root updatedSource updatedCore ∧
      Dynamic.ProjectionsUpdate (fun _ updated => updated = replacementSource) (some sourceValue) projections updatedSource ∧
      ∀ environment store type current keys nextValue,
        Selects environment current value → Selects environment nextValue replacementValue →
        Evaluates environment store (SourceCoreDataPlaces.update prepared steps type current keys nextValue)
          (.inRight .word updatedCore) store := by
  induction members generalizing sourceValue value with
  | nil =>
    exact ⟨replacementSource, replacementValue, replacement, .leaf rfl,
      fun _ store _ _ _ _ _ selected => .inRight (selected.evaluates store)⟩
  | @member root field leaf dataType index branches fieldType name steps projections layout tail ih =>
    cases represented with
    | unit | bool | word | integer | product =>
      obtain ⟨_, _, impossible⟩ := layout.nominal
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
    | @constructed sourceType metadata tag declaration typeArguments arguments values nominal result authenticated payloads =>
      obtain ⟨owner, branch, branchLookup, branchConstructor, fieldLookup, payloadLength⟩ := layout.constructors metadata tag result authenticated
      obtain ⟨selectedSource, selectedCore, sourceAt, coreAt, selectedRepresentation⟩ := TypedValuesRep.at payloads fieldLookup
      obtain ⟨updatedChild, updatedValue, updatedRepresentation, sourceUpdate, childExecution⟩ := ih selectedRepresentation replacement
      refine ⟨.constructed metadata (arguments.set index updatedChild),
        .constructed tag (packValues (values.set index updatedValue)),
        .constructed nominal result authenticated (TypedValuesRep.replace payloads fieldLookup updatedRepresentation),
        .member sourceAt sourceUpdate (replacement_at sourceAt updatedChild), ?_⟩
      intro environment store type current keys nextValue selected selectedReplacement
      apply Evaluates.matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchLookup, Option.map_some]; rfl)
      apply Evaluates.caseRight (childExecution _ store _ _ _ _
        (projectPacked_selects (Selects.var (index := 0) rfl) (payloadLength.trans (DataPatternTypedValues.TypedValuesRep.length payloads).2) index coreAt)
        (by simpa [shift] using selectedReplacement.weaken (packValues values)))
      rw [branchConstructor]
      exact .inRight (.construct (replacePacked_evaluates
        (payloadLength.trans (DataPatternTypedValues.TypedValuesRep.length payloads).2) (.var rfl) (.var rfl)))


/-- Closed generated getter on an initialized nominal root. Key bundles are
administrative input here; member paths neither inspect nor evaluate them. -/
theorem Members.getter {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    (members : Members checked signatures root steps projections leaf) (prepared : Prepared)
    (sameSteps : prepared.steps = steps) (notMapping : prepared.route.rootMapping = none)
    {sourceValue : Dynamic.Value} {value : Value}
    (represented : TypedValueRep checked.catalog signatures root sourceValue value) :
    ∃ sourceLeaf coreLeaf, TypedValueRep checked.catalog signatures leaf sourceLeaf coreLeaf ∧
      Dynamic.ProjectionsRead (some sourceValue) projections (some sourceLeaf) ∧
      ∀ environment store keyType keys argument,
        Selects environment argument (.pair (.inRight .unit value) keys) →
        Evaluates environment store (.apply (SourceCoreDataPlaces.getter prepared keyType) argument)
          (.inRight .word (.inRight .unit coreLeaf)) store := by
  cases members with
  | nil =>
    refine ⟨sourceValue, value, represented, .nil, ?_⟩
    intro environment store keyType keys argument argumentSelected
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps, normalizeRoot, notMapping]
    exact .inRight (.first (.var rfl))
  | member layout tail =>
    obtain ⟨sourceLeaf, coreLeaf, leafRep, sourceRead, selected⟩ := Members.select (.member layout tail) prepared represented
    refine ⟨sourceLeaf, coreLeaf, leafRep, sourceRead, ?_⟩
    intro environment store keyType keys argument argumentSelected
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps, normalizeRoot, notMapping]
    apply Evaluates.caseRight (.first (.var rfl))
    exact selected _ store _ _ (.var rfl)

/-- The setter's root argument is the latest root, independently of the getter
snapshot used by compound arithmetic. Only its chosen leaf is replaced. -/
theorem Members.setter {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    (members : Members checked signatures root steps projections leaf) (prepared : Prepared)
    (sameSteps : prepared.steps = steps) (notMapping : prepared.route.rootMapping = none)
    {sourceValue replacementSource : Dynamic.Value} {value replacementValue : Value}
    (represented : TypedValueRep checked.catalog signatures root sourceValue value)
    (replacement : TypedValueRep checked.catalog signatures leaf replacementSource replacementValue) :
    ∃ updatedSource updatedCore, TypedValueRep checked.catalog signatures root updatedSource updatedCore ∧
      Dynamic.ProjectionsUpdate (fun _ updated => updated = replacementSource) (some sourceValue) projections updatedSource ∧
      ∀ environment store keyType keys argument,
        Selects environment argument (.pair (.inRight .unit value) (.pair keys replacementValue)) →
        Evaluates environment store (.apply (SourceCoreDataPlaces.setter prepared keyType) argument) (.inRight .word updatedCore) store := by
  cases members with
  | nil =>
    refine ⟨replacementSource, replacementValue, replacement, .leaf rfl, ?_⟩
    intro environment store keyType keys argument argumentSelected
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps]
    exact .inRight (.second (.second (.var rfl)))
  | member layout tail =>
    obtain ⟨updatedSource, updatedCore, updatedRep, sourceUpdate, updated⟩ := Members.update (.member layout tail) prepared represented replacement
    refine ⟨updatedSource, updatedCore, updatedRep, sourceUpdate, ?_⟩
    intro environment store keyType keys argument argumentSelected
    apply Evaluates.apply .lambda (argumentSelected.evaluates store)
    simp only [sameSteps, normalizeRoot, notMapping]
    apply Evaluates.caseRight (.first (.var rfl))
    exact updated _ store _ _ _ _ (.var rfl) (.second (.second (.var rfl)))

/-- An absent nonmapping root fails before traversing a nonempty member path.
No allocation, RHS evaluation or write occurs in this generated getter. -/
theorem getter_absent {prepared : Prepared} {step : PreparedStep} {steps : List PreparedStep}
    (sameSteps : prepared.steps = step :: steps) (notMapping : prepared.route.rootMapping = none)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : Value) :
    Evaluates (.pair (.inLeft prepared.route.rootType .unit) keys :: environment) store
      (.apply (SourceCoreDataPlaces.getter prepared keyType) (.var 0))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
  apply Evaluates.apply .lambda (.var rfl)
  simp only [sameSteps, normalizeRoot, notMapping]
  exact .caseLeft (.first (.var rfl)) (.inLeft .word)

theorem Members.setter_run {checked : Checked} {signatures : ProgramSignatures}
    {root leaf : TypeSystem.Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection}
    (members : Members checked signatures root steps projections leaf) (prepared : Prepared)
    (sameSteps : prepared.steps = steps) (notMapping : prepared.route.rootMapping = none)
    {sourceValue replacementSource : Dynamic.Value} {value replacementValue : Value}
    (represented : TypedValueRep checked.catalog signatures root sourceValue value)
    (replacement : TypedValueRep checked.catalog signatures leaf replacementSource replacementValue)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : Value) :
    ∃ updatedSource updatedCore, TypedValueRep checked.catalog signatures root updatedSource updatedCore ∧
      Dynamic.ProjectionsUpdate (fun _ updated => updated = replacementSource) (some sourceValue) projections updatedSource ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared keyType) (.var 0))
          (.pair (.inRight .unit value) (.pair keys replacementValue) :: environment) store) = .done (.inRight .word updatedCore) store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared keyType) (.var 0))
          (.pair (.inRight .unit value) (.pair keys replacementValue) :: environment) store) = .done actual finalStore →
        actual = .inRight .word updatedCore ∧ finalStore = store) := by
  obtain ⟨updatedSource, updatedCore, updatedRep, sourceUpdate, updated⟩ := Members.setter members prepared sameSteps notMapping represented replacement
  have evaluated := updated (.pair (.inRight .unit value) (.pair keys replacementValue) :: environment) store keyType keys (.var 0) (.var rfl)
  exact ⟨updatedSource, updatedCore, updatedRep, sourceUpdate, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceMembers
