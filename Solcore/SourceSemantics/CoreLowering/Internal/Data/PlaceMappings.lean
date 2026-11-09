import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.GenericHeaps
import Solcore.SourceSemantics.CoreLowering.Internal.Data.HeapsAndBindings
import Solcore.Frontend.SourceCore.DataPlaces
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.FunctionCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Static

/-!
# Data: places in mappings

Places through mappings and members: preparation, key order, read trees and sequencing of data expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMappingHeap
/-! Mapping helpers extend the existing generic heap relation. They neither
create source aliases for administrative closures nor change source cells.
Runtime typing supplies the extended world, including cyclic closures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMappingHeap
open Core Frontend GeneralHeap GenericHeap

theorem heap_append {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world futureWorld : StoreTyping} {heap : Dynamic.Heap} {store suffix : Store}
    (related : HeapRepresents model mapping world heap store)
    (extension : WorldExtends world futureWorld)
    (typed : RuntimeStoreHasTypes futureWorld (store ++ suffix) definitions) :
    HeapRepresents model mapping futureWorld heap (store ++ suffix) := by
  refine ⟨related.length_eq, related.injective, typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, payload, sourceRead, typeRead, coreRead, represented⟩ := related.cells mapped
  exact ⟨cell, value, payload, sourceRead, extension.lookup typeRead,
    by simpa [Store.read?, List.getElem?_append_left (related.target_lt mapped)] using coreRead,
    represented.extend (.refl _) extension⟩

theorem administrative_append (mapping : LocationMap) (store suffix : Store) :
    AdministrativePreserved mapping store mapping (store ++ suffix) := by
  intro location absent bound
  exact ⟨absent, by simp [Store.read?, List.getElem?_append_left bound]⟩

/-- Combine a proved finite helper evaluation and its exact store suffix with
the actual Core typing proof. The source heap and map remain unchanged. -/
theorem evaluation_preserves_frame {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    (related : HeapRepresents model mapping world heap store)
    {environment : Environment} {context : Core.Context} {expression : Expr} {value : Value} {type : Ty}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (expressionTyped : HasType context expression type definitions)
    (evaluated : Evaluates environment store expression value finalStore)
    {suffix : Store} (extended : finalStore = store ++ suffix) :
    ∃ futureWorld, WorldExtends world futureWorld ∧ HeapRepresents model mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld value type definitions ∧
      AdministrativePreserved mapping store mapping finalStore := by
  subst finalStore
  obtain ⟨futureWorld, extension, storeTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluated expressionTyped environmentTyped related.runtime_hasTypes
  exact ⟨futureWorld, extension, heap_append related extension storeTyped, valueTyped,
    administrative_append mapping store suffix⟩

end Solcore.SourceSemantics.CoreLowering.DataMappingHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMembers
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
    | unit | bool | word | integer | fixed | product =>
      obtain ⟨_, _, impossible⟩ := layout.nominal
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer,
        TypeSystem.Ty.fixed] at impossible
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
    | unit | bool | word | integer | fixed | product =>
      obtain ⟨_, _, impossible⟩ := layout.nominal
      simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer,
        TypeSystem.Ty.fixed] at impossible
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
/-! Receipts from the actual mutable preparation loop. Every emitted mapping
step retains its accepted comparator/default preparation and its ordered key
position. No helper semantics or replacement compiler is assumed here. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
open Core Frontend SourceInference SourceCoreDataPlaces

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

private theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

theorem comparison_sourceType {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreDataEquality.Prepared checked}
    (accepted : SourceCoreDataEquality.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreDataEquality.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

theorem default_sourceType {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreDefaultValue.Prepared checked}
    (accepted : SourceCoreDefaultValue.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreDefaultValue.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

inductive Steps (checked : SourceCoreDataCatalog.Checked) (fuel : Nat) (missing : TypeSystem.Ty → Word) :
    Nat → List Step → List PreparedStep → List (ExpressionId × Ty) → Prop where
  | nil (count : Nat) : Steps checked fuel missing count [] [] []
  | member {count : Nat} {id : DataTypeId} {index : Nat} {branches : List MemberBranch} {field : Ty}
      {source : List Step} {target : List PreparedStep} {keys : List (ExpressionId × Ty)}
      (tail : Steps checked fuel missing count source target keys) :
      Steps checked fuel missing count (.member id index branches field :: source)
        (.member id index branches field :: target) keys
  | index {count : Nat} {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceValue : TypeSystem.Ty}
      {entry : SourceCoreDataCatalog.Entry} {sourceKey registeredValue : TypeSystem.Ty}
      {comparison : SourceCoreDataEquality.Prepared checked} {default : SourceCoreDefaultValue.Prepared checked}
      {source : List Step} {target : List PreparedStep} {keys : List (ExpressionId × Ty)}
      (selected : checked.catalog.entries[layout.dataType.index]? = some entry)
      (mappingType : entry.sourceType = .mapping sourceKey registeredValue)
      (comparisonGenerated : SourceCoreDataEquality.prepare fuel checked sourceKey = .ok comparison)
      (defaultGenerated : SourceCoreDefaultValue.prepare (sourceValue.size + 1) checked sourceValue = .ok default)
      (tail : Steps checked fuel missing (count + 1) source target keys) :
      Steps checked fuel missing count (.index layout key sourceValue :: source)
        (.index ⟨layout, key, count, comparison.expression, default.expression, missing sourceValue⟩ :: target)
        ((key, layout.keyType) :: keys)

theorem Steps.append {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    {count : Nat} {a b : List Step} {x y : List PreparedStep} {left right : List (ExpressionId × Ty)}
    (first : Steps checked fuel missing count a x left)
    (second : Steps checked fuel missing (count + left.length) b y right) :
    Steps checked fuel missing count (a ++ b) (x ++ y) (left ++ right) := by
  induction first with
  | nil => exact second
  | member _ ih => exact .member (ih second)
  | index selected mappingType comparisonGenerated defaultGenerated _ ih =>
    exact .index selected mappingType comparisonGenerated defaultGenerated
      (ih (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second))

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
      intro seen state decomposition valid finished
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at finished
      subst final
      simpa [decomposition] using valid
    | cons item remaining ih =>
      intro seen state decomposition valid finished
      rw [List.forIn_cons] at finished
      obtain ⟨outcome, ran, finished⟩ := bind_ok finished
      obtain ⟨updated, rfl, preserved⟩ := next seen item remaining state outcome decomposition valid ran
      exact ih (seen ++ [item]) updated (by simpa [List.append_assoc] using decomposition) preserved finished
  exact loop items [] initial rfl start accepted

/-- Actual preparation emits exactly the accepted helpers and preserves key
order and all diagnostics through mixed member/index routes. -/
theorem steps_of_prepare {checked : SourceCoreDataCatalog.Checked} {fuel : Nat} {route : Route}
    {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      Steps checked fuel missing 0 route.steps prepared.steps prepared.keys := by
  unfold prepare at accepted
  obtain ⟨state, loopAccepted, accepted⟩ := bind_ok accepted
  let invariant := fun (seen : List Step) (state : List PreparedStep × List (ExpressionId × Ty)) =>
    Steps checked fuel missing 0 seen state.1 state.2
  have certificate : invariant route.steps state := by
    apply forIn_preserves loopAccepted invariant
    · exact .nil 0
    · intro seen item remaining state outcome decomposition previous rowAccepted
      cases item with
      | member dataType index branches field =>
        simp only [pure, Except.pure, Except.ok.injEq] at rowAccepted
        subst outcome
        exact ⟨_, rfl, by simpa using previous.append (.member (id := dataType) (index := index)
          (branches := branches) (field := field) (.nil _))⟩
      | index layout key valueType =>
        cases selected : checked.catalog.entries[layout.dataType.index]? with
        | none => simp [selected, bind, Except.bind, throw] at rowAccepted
        | some entry =>
          cases kind : entry.sourceType <;> simp only [selected, kind, pure, Except.pure, bind, Except.bind, throw] at rowAccepted
          all_goals try cases rowAccepted
          rename_i sourceKey registeredValue
          obtain ⟨comparison, comparisonGenerated, rowAccepted⟩ := bind_ok rowAccepted
          obtain ⟨default, defaultGenerated, rowAccepted⟩ := bind_ok rowAccepted
          simp only [Except.ok.injEq] at rowAccepted
          subst outcome
          refine ⟨_, rfl, previous.append ?_⟩
          simp only [Nat.zero_add]
          exact .index selected kind (mapError_ok comparisonGenerated) (mapError_ok defaultGenerated) (.nil _)
  simp only [pure, Except.pure, Except.ok.injEq] at accepted
  subst prepared
  exact ⟨rfl, rfl, certificate⟩

/-- The optional default's independent meaning and finite execution are
available directly from the retained preparation receipt. -/
theorem default_preserves {checked : SourceCoreDataCatalog.Checked} {source : TypeSystem.Ty}
    {prepared : SourceCoreDefaultValue.Prepared checked}
    (accepted : SourceCoreDefaultValue.prepare (source.size + 1) checked source = .ok prepared)
    (environment : Environment) (store : Store) :
    ∃ value, DataDefaults.ResultRepresents checked.catalog source prepared.type value ∧
      Evaluates environment store prepared.expression value store := by
  have meaning := DataDefaults.prepared_preserves prepared environment store
  rwa [default_sourceType accepted] at meaning

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPreparation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
/-! Correspondence for the production argument/key packing helper. Each child
has a static compilation receipt and a universal semantic theorem. The list
theorems construct the intervening heaps and the actual inserted payload slots;
they do not assume child evaluations at those generated layouts. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning DataPatternValues

inductive Tree (source : TypedSource) (certificate : Certificate) (scope : SourceCoreLocalCell.Scope) :
    List ExpressionId → List TypeSystem.Ty → List SourceCoreBasic.LoweredExpr → Prop where
  | nil : Tree source certificate scope [] [] []
  | single {id node lowered}
      (found : source.lookupExpression? id = some node) (generated : certificate scope id lowered) :
      Tree source certificate scope [id] [node.type] [lowered]
  | cons {id node lowered next ids types nextCode codes}
      (found : source.lookupExpression? id = some node) (generated : certificate scope id lowered)
      (tail : Tree source certificate scope (next :: ids) types (nextCode :: codes)) :
      Tree source certificate scope (id :: next :: ids) (node.type :: types) (lowered :: nextCode :: codes)

/-- A vector of individual static receipts determines the production packing
tree. There is no evaluation or semantic condition in this extraction. -/
theorem Tree.of_children {source : TypedSource} {certificate : Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (children : ListRel (fun id code => ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) ids codes) :
    ∃ types, Tree source certificate scope ids types codes := by
  induction children with
  | nil => exact ⟨[], .nil⟩
  | @cons id code ids codes head tail ih =>
    obtain ⟨node, found, generated⟩ := head
    cases tail with
    | nil => exact ⟨[node.type], .single found generated⟩
    | cons _ _ =>
      obtain ⟨types, rest⟩ := ih
      exact ⟨node.type :: types, .cons found generated rest⟩

/-- Successful effectful list traversal exposes the exact individual compiler
results; callers may retain their metadata/type-validation wrapper in `compile`. -/
theorem Tree.of_mapM {α error : Type} {source : TypedSource} {certificate : Certificate}
    {scope : SourceCoreLocalCell.Scope} (identify : α → ExpressionId)
    (compile : α → Except error SourceCoreBasic.LoweredExpr)
    {inputs : List α} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : inputs.mapM compile = .ok codes)
    (extract : ∀ input code, compile input = .ok code → ∃ node,
      source.lookupExpression? (identify input) = some node ∧ certificate scope (identify input) code) :
    ∃ types, Tree source certificate scope (inputs.map identify) types codes := by
  apply Tree.of_children
  induction inputs generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons input rest ih =>
    cases head : compile input with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at accepted
    | ok code =>
      cases tail : rest.mapM compile with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at accepted
      | ok restCodes =>
        simp only [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst codes
        exact .cons (extract input code head) (ih tail)

inductive Values {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) :
    List TypeSystem.Ty → List Ty → List Dynamic.Value → List Value → Prop where
  | nil : Values model mapping world [] [] [] []
  | cons {sourceType type source value sourceTypes types sources values}
      (head : model.Represents mapping world sourceType source value type)
      (tail : Values model mapping world sourceTypes types sources values) :
      Values model mapping world (sourceType :: sourceTypes) (type :: types) (source :: sources) (value :: values)

theorem Values.extend {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : Values model mapping world sourceTypes types sources values)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Values model futureMapping futureWorld sourceTypes types sources values := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons (model.extend head maps worlds) ih

theorem Values.length {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {types : List Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : Values model mapping world sourceTypes types sources values) :
    types.length = sources.length ∧ types.length = values.length := by
  induction represented with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

theorem pair_rename (leftType rightType : Ty) (left right : Expr) (ξ : Renaming) :
    (LocalSequence.pair leftType rightType left right).rename ξ =
      LocalSequence.pair leftType rightType (left.rename ξ) (right.rename ξ) := by
  simp [LocalSequence.pair, LanguageResult.bind, LanguageResult.success, Expr.rename, Renaming.lift]

abbrev Outcome := Except Dynamic.SemanticFault (List Dynamic.Value)

inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (ids : List ExpressionId) : Outcome → Dynamic.Heap → Prop where
  | values {sources after}
      (evaluated : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
      Trace program context evidence source environment before ids (.ok sources) after
  | fault {reason after}
      (failed : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
      Trace program context evidence source environment before ids (.error reason) after

inductive Result {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (types : List TypeSystem.Ty)
    (codes : List SourceCoreBasic.LoweredExpr) (faults : FaultRep) : Outcome → Value → Prop where
  | values {sources values}
      (represented : Values model mapping world types (codes.map (·.type)) sources values) :
      Result model mapping world types codes faults (.ok sources) (.inRight .word (packValues values))
  | fault {reason token} (represented : faults reason token) :
      Result model mapping world types codes faults (.error reason)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token))

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem Tree.preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue) rest
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

variable {expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost}
  {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem Tree.preserves_fault_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.Preserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata, retained⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, joins.tail head failed retained⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

theorem Tree.preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Tree.preserves_fault_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.Preserves.of_trivial meaning) environments heaps locals layout execution
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed evaluation of the actual generated bundle constructs a
finite source trace. Arbitrary inserted temporary slots are admitted through
the child theorem's explicit renaming; no exact closure weakening is used. -/
theorem Tree.reflects_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.Reflects model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _, trivial⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨.ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, trivial⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨.error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change Evaluates actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout first
      cases represented with
      | fault matched =>
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
          exact ⟨.error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := agree_prefix layout coreValue
        cases execution with
        | value firstSource =>
          cases continuation with
          | caseLeft second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout shifted
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                exact ⟨.error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata,
                  ⟨_, rfl, joins.tail firstSource tailSource (ExpressionFailurePostContracts.ListOutcomePost.fault retained)⟩⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout shifted
            cases result with
            | @values sources values restRep =>
              cases sourceTrace with
              | values tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_success lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                have nonempty : values ≠ [] := by
                  intro absent
                  have lengths := restRep.length.2
                  simp [absent] at lengths
                refine ⟨.ok (sourceValue :: sources), after, finalMap, finalWorld,
                  .values (.cons firstSource tailSource), ?_, finalHeaps,
                  firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata, trivial⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

theorem Tree.reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := Tree.reflects_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.Reflects.of_trivial meaning) environments heaps locals layout evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Tree.preserves_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.Preserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := tree.preserves_values (ExpressionFailurePostContracts.Preserves.forget meaning) environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := tree.preserves_fault_with_post joins meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata, ⟨token, rfl, retained⟩⟩

theorem Tree.preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := tree.preserves_values meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := tree.preserves_fault meaning environments heaps locals layout execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Finiteness comes from the independent source trace. Fuel exhaustion remains
a resumable machine state, rather than a successful or faulting source outcome. -/
theorem Tree.preserves_sufficient_fuel (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.preserves meaning environments heaps locals layout execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem Tree.reflects_done (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  tree.reflects meaning environments heaps locals layout (runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.DataExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
/-! Certificates extracted from accepted place compilation. They expose the
real generated helper, ordered index expressions and RHS, without assuming
any execution of those expressions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

def KeyGenerated (expression : ExpressionLowerer) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word) (key : ExpressionId × Ty)
    (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  expression fuel source scope key.1 reasonAt = .ok lowered ∧ key.2 = lowered.type

theorem keys_generated {expression : ExpressionLowerer} {fuel : Nat} {source : TypedSource}
    {scope : Scope} {reasonAt : ExpressionId → Word} {keys : List (ExpressionId × Ty)}
    {lowered : List SourceCoreBasic.LoweredExpr}
    (accepted : keys.mapM (fun (id, expected) => do
      let key ← expression fuel source scope id reasonAt
      SourceCoreBasic.ensureType (.occurrence id.occurrence) expected key.type
      pure key) = .ok lowered) :
    ListRel (KeyGenerated expression fuel source scope reasonAt) keys lowered := by
  induction keys generalizing lowered with
  | nil => simp [List.mapM_nil, pure, Except.pure] at accepted; subst lowered; exact .nil
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, compiled, accepted⟩ := bind_ok accepted
    obtain ⟨rest, compiledRest, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst lowered
    obtain ⟨actual, generated, compiled⟩ := bind_ok compiled
    obtain ⟨checkedUnit, checked, compiled⟩ := bind_ok compiled
    cases checkedUnit
    simp only [pure, Except.pure, Except.ok.injEq] at compiled
    subst first
    exact .cons ⟨generated, ensureType_ok checked⟩ (ih compiledRest)

inductive RhsGenerated (expression : ExpressionLowerer) (fuel : Nat) (source : TypedSource)
    (scope : Scope) (reasonAt : ExpressionId → Word) (leafType : Ty) : Option ExpressionId → Expr → Prop where
  | absent : RhsGenerated expression fuel source scope reasonAt leafType none (LanguageResult.success .unit)
  | present {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
      (generated : expression fuel source scope id reasonAt = .ok lowered)
      (type : leafType = lowered.type) :
      RhsGenerated expression fuel source scope reasonAt leafType (some id) lowered.expression

inductive Generated (checked : Checked) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Ty) (next : Expr) (reasonAt : ExpressionId → Word)
    (invalidProjection invalidOperand : Word) (missing : TypeSystem.Ty → Word) : Expr → Prop where
  | intro (route : Route) (prepared : Prepared) (index : Nat)
      (keys : List SourceCoreBasic.LoweredExpr) (value : Expr)
      (described : describe checked signatures source site assignment = .ok route)
      (lookup : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType))
      (preparedBy : prepare checked fuel route invalidProjection missing = .ok prepared)
      (keysGenerated : ListRel (KeyGenerated expression fuel source scope reasonAt) prepared.keys keys)
      (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer ∧ operator.wordOnly = false)
      (rhsGenerated : RhsGenerated expression fuel source scope reasonAt route.leafType rhs value) :
      Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
        reasonAt invalidProjection invalidOperand missing
        (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value next outputType
          (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)

/-- The receipt follows actual successful compiler branches. It does not
replace or reinterpret the executable place compiler. -/
theorem generated_of_lower {checked : Checked} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {outputType : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word} {lowered : Expr}
    (accepted : lower checked signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing = .ok lowered) :
    Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
      reasonAt invalidProjection invalidOperand missing lowered := by
  unfold lower at accepted
  obtain ⟨route, described, accepted⟩ := bind_ok accepted
  cases lookup : SourceCoreLocalCell.lookup? scope assignment.target.root with
  | none => simp [lookup, throw, bind, Except.bind] at accepted
  | some pair =>
    obtain ⟨index, storedType⟩ := pair
    simp only [lookup, pure, Except.pure, bind, Except.bind] at accepted
    cases typed : SourceCoreBasic.ensureType site route.rootType storedType with
    | error error => simp [typed] at accepted
    | ok checkedUnit =>
      cases checkedUnit
      have types := ensureType_ok typed
      subst storedType
      simp only [typed] at accepted
      obtain ⟨prepared, preparedBy, accepted⟩ := bind_ok accepted
      obtain ⟨keys, keysCompiled, accepted⟩ := bind_ok accepted
      have keyCertificate := keys_generated keysCompiled
      have finish (operatorValid : operator = .equal ∧ rhs.isNone = false ∨ route.leafType = .word ∨ route.leafType = Core.Ty.integer ∧ operator.wordOnly = false)
          (completed : (show Except SourceCoreBasic.Error Expr from match rhs with
            | none => .ok (execute prepared (.var index) (SourceCoreCalls.packArguments keys)
                (LanguageResult.success .unit) next outputType
                (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)
            | some id => do
                let value ← expression fuel source scope id reasonAt
                SourceCoreBasic.ensureType site route.leafType value.type
                pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) value.expression next outputType
                  (binaryOperator (route.leafType = Core.Ty.integer) operator) rhs.isNone invalidOperand)) = .ok lowered) :
          Generated checked signatures expression fuel source scope site assignment operator rhs outputType next
            reasonAt invalidProjection invalidOperand missing lowered := by
        cases rhs with
        | none =>
          simp only [Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid .absent
        | some id =>
          obtain ⟨value, valueCompiled, completed⟩ := bind_ok completed
          obtain ⟨checkedUnit, typeChecked, completed⟩ := bind_ok completed
          cases checkedUnit
          simp only [pure, Except.pure, Except.ok.injEq] at completed
          subst lowered
          exact .intro route prepared index keys _ described lookup preparedBy keyCertificate operatorValid
            (.present valueCompiled (ensureType_ok typeChecked))
      by_cases same : operator = .equal
      · cases rhs with
        | none =>
          by_cases word : route.leafType = .word
          · apply finish (.inr (.inl word)); simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
          · by_cases integer : route.leafType = Core.Ty.integer
            · apply finish (.inr (.inr ⟨integer, by rw [same]; rfl⟩))
              simpa [same, integer, Syntax.ValueAssignOp.wordOnly, pure, Except.pure, bind, Except.bind] using accepted
            · simp [same, word, integer, throw] at accepted
        | some id =>
          apply finish (.inl ⟨same, rfl⟩)
          simpa [same, pure, Except.pure, bind, Except.bind] using accepted
      · by_cases word : route.leafType = .word
        · apply finish (.inr (.inl word)); cases rhs <;> simpa [same, word, pure, Except.pure, bind, Except.bind] using accepted
        · by_cases integer : route.leafType = Core.Ty.integer
          · cases shift : operator.wordOnly
            · apply finish (.inr (.inr ⟨integer, shift⟩))
              cases rhs <;> simpa [same, integer, shift, pure, Except.pure, bind, Except.bind] using accepted
            · simp [same, integer, shift, throw] at accepted
          · simp [same, word, integer, throw] at accepted

end Solcore.SourceSemantics.CoreLowering.DataPlaceCertificates
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
/-! Ordered index expressions from actual place preparation. The independent
source projection trace is equivalent to evaluating exactly this expression
vector: member projections contribute no expression execution. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataPatternValues

def sourceKeys : List PlaceProjection → List ExpressionId
  | [] => []
  | .member _ _ :: rest => sourceKeys rest
  | .index key :: rest => key :: sourceKeys rest

def stepKeys : List Step → List ExpressionId
  | [] => []
  | .member _ _ _ _ :: rest => stepKeys rest
  | .index _ key _ :: rest => key :: stepKeys rest

/-- A projection vector retains member names and positions while pairing
index positions with their ordered source values. -/
inductive Values : List PlaceProjection → List Dynamic.Value → List Dynamic.EvaluatedProjection → Prop where
  | nil : Values [] [] []
  | member {name index rest values projections} (tail : Values rest values projections) :
      Values (.member name index :: rest) values (.member name index :: projections)
  | index {key rest value values projections} (tail : Values rest values projections) :
      Values (.index key :: rest) (value :: values) (.index value :: projections)

theorem projections_values {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {evaluated : List Dynamic.EvaluatedProjection}
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ values, Values projections values evaluated ∧
      Dynamic.ExpressionsEvaluate program context evidence source environment before (sourceKeys projections) values after := by
  induction projections generalizing before evaluated with
  | nil => cases trace; exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      cases trace with
      | member tail => obtain ⟨values, related, evaluated⟩ := ih tail; exact ⟨values, .member related, evaluated⟩
    | index key =>
      cases trace with
      | index head tail => obtain ⟨values, related, evaluated⟩ := ih tail; exact ⟨_ :: values, .index related, .cons head evaluated⟩

theorem values_projections {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {values : List Dynamic.Value}
    (trace : Dynamic.ExpressionsEvaluate program context evidence source environment before (sourceKeys projections) values after) :
    ∃ evaluated, Values projections values evaluated ∧
      Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after := by
  induction projections generalizing before values with
  | nil => cases trace; exact ⟨[], .nil, .nil⟩
  | cons projection rest ih =>
    cases projection with
    | member name index => obtain ⟨evaluated, related, executed⟩ := ih trace; exact ⟨_, .member related, .member executed⟩
    | index key =>
      cases trace with
      | cons head tail => obtain ⟨evaluated, related, executed⟩ := ih tail; exact ⟨_, .index related, .index head executed⟩

theorem projections_fault {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    Dynamic.ExpressionsFault program context evidence source environment before (sourceKeys projections) reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index => cases trace with
      | memberTail tail => exact ih tail
    | index key => cases trace with
      | indexHead fault => exact .head fault
      | indexTail head tail => exact .tail head (ih tail)

theorem fault_projections {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {projections : List PlaceProjection} {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ExpressionsFault program context evidence source environment before (sourceKeys projections) reason after) :
    Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after := by
  induction projections generalizing before with
  | nil => cases trace
  | cons projection rest ih =>
    cases projection with
    | member name index => exact .memberTail (ih trace)
    | index key => cases trace with
      | head fault => exact .indexHead fault
      | tail head rest => exact .indexTail head (ih rest)

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

private theorem member_shape {checked : Checked} {signatures : ProgramSignatures}
    {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId} {type field : TypeSystem.Ty}
    {index : Nat} {step : Step}
    (accepted : memberStep checked signatures site binder type index = .ok (step, field)) :
    ∃ identity branches coreType, step = .member identity index branches coreType := by
  unfold memberStep at accepted
  dsimp only at accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨state, _, accepted⟩ := bind_ok accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨coreType, _, accepted⟩ := bind_ok accepted
  cases accepted
  exact ⟨_, _, coreType, rfl⟩

/-- The successful route traversal keeps exactly the source index occurrences,
including repeated occurrences and indices separated by nominal members. -/
theorem routeSteps_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {binder : Resolved.LocalId}
    {type field : TypeSystem.Ty} {projections : List PlaceProjection} {steps : List Step}
    (accepted : routeSteps checked signatures source site binder type projections = .ok (steps, field)) :
    stepKeys steps = sourceKeys projections := by
  induction projections generalizing type steps field with
  | nil =>
    simp only [routeSteps, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    rfl
  | cons projection rest ih =>
    cases projection with
    | member name index =>
      rw [routeSteps.eq_def] at accepted
      dsimp only at accepted
      obtain ⟨selected, first, accepted⟩ := bind_ok accepted
      obtain ⟨step, selectedType⟩ := selected
      obtain ⟨remaining, tail, accepted⟩ := bind_ok accepted
      obtain ⟨remainingSteps, finalType⟩ := remaining
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      obtain ⟨identity, branches, coreType, rfl⟩ := member_shape first
      simpa only [stepKeys, sourceKeys] using (ih (steps := remainingSteps) tail)
    | index key =>
      rw [routeSteps.eq_def] at accepted
      dsimp only at accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      obtain ⟨keyType, _, accepted⟩ := bind_ok accepted
      obtain ⟨projectedKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
      cases checkedUnit
      obtain ⟨valueType, _, accepted⟩ := bind_ok accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
      obtain ⟨remaining, tail, accepted⟩ := bind_ok accepted
      obtain ⟨remainingSteps, finalType⟩ := remaining
      cases accepted
      exact congrArg (key :: ·) (ih tail)

/-- The preparation loop's real key table keeps route order. Comparator and
default preparation introduce no additional source expression occurrences. -/
theorem prepared_keys {checked : Checked} {fuel : Nat} {route : Route}
    {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.keys.map Prod.fst = stepKeys route.steps := by
  obtain ⟨_, _, generated⟩ := DataPlaceMappingPreparation.steps_of_prepare accepted
  have ordered : ∀ {count steps targets keys},
      DataPlaceMappingPreparation.Steps checked fuel missing count steps targets keys →
        keys.map Prod.fst = stepKeys steps := by
    intro count steps targets keys generated
    induction generated with
    | nil => rfl
    | member _ ih => exact ih
    | index _ _ _ _ _ ih => exact congrArg (_ :: ·) ih
  exact ordered generated

theorem described_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {route : Route}
    (accepted : describe checked signatures source site assignment = .ok route) :
    stepKeys route.steps = sourceKeys assignment.target.projections := by
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> (try simp only [pure, Except.pure, bind, Except.bind, throw] at accepted) <;> try cases accepted
  obtain ⟨binder, _, accepted⟩ := bind_ok accepted
  obtain ⟨rootType, _, accepted⟩ := bind_ok accepted
  obtain ⟨routed, routedBy, accepted⟩ := bind_ok accepted
  obtain ⟨steps, field⟩ := routed
  split at accepted <;> try cases accepted
  dsimp only [bind, Except.bind, pure, Except.pure] at accepted
  repeat' first | split at accepted | cases accepted
  all_goals exact routeSteps_keys routedBy

theorem prepared_source_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared) :
    prepared.keys.map Prod.fst = sourceKeys assignment.target.projections :=
  (prepared_keys preparedBy).trans (described_keys described)

/-- Actual accepted child compilations and exact key-type checks automatically
produce the vector certificate used by the semantic sequence theorems. -/
theorem tree_of_generated_keys {checked : Checked} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    {expression : ExpressionLowerer} {scope : Scope} {reasonAt : ExpressionId → Word}
    {codes : List SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (described : describe checked signatures source site assignment = .ok route)
    (preparedBy : prepare checked fuel route invalid missing = .ok prepared)
    (generated : ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) prepared.keys codes)
    (extract : ∀ id code, expression fuel source scope id reasonAt = .ok code → ∃ node,
      source.lookupExpression? id = some node ∧ certificate scope id code) :
    ∃ types, DataExpressionSequence.Tree source certificate scope (sourceKeys assignment.target.projections) types codes ∧
      prepared.keyTypes = codes.map (·.type) := by
  have collect : ∀ {keys codes},
      ListRel (DataPlaceCertificates.KeyGenerated expression fuel source scope reasonAt) keys codes →
      ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code)
        (keys.map Prod.fst) codes ∧ keys.map Prod.snd = codes.map (·.type) := by
    intro keys codes generated
    induction generated with
    | nil => exact ⟨.nil, rfl⟩
    | cons head tail ih => exact ⟨.cons (extract _ _ head.1) ih.1, by simp only [List.map_cons, head.2, ih.2]⟩
  have receipts := collect generated
  obtain ⟨types, tree⟩ := DataExpressionSequence.Tree.of_children receipts.1
  rw [prepared_source_keys described preparedBy] at tree
  exact ⟨types, tree, receipts.2⟩

open GeneralHeap GenericExpressionMeaning

/-- Index effects are evaluated exactly once in source projection order. The
generated values remain fully represented after later index effects. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, shaped, executed⟩ := projections_values trace
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.preserves_values meaning environments heaps locals layout executed
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  tree.preserves_fault meaning environments heaps locals layout (projections_fault trace)

inductive OutcomeTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (projections : List PlaceProjection) : DataExpressionSequence.Outcome → Dynamic.Heap → Prop where
  | values {values evaluated after} (shaped : Values projections values evaluated)
      (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
      OutcomeTrace program context evidence source environment before projections (.ok values) after
  | fault {reason after}
      (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
      OutcomeTrace program context evidence source environment before projections (.error reason) after

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      OutcomeTrace program context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := tree.reflects meaning environments heaps locals layout evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata⟩
  cases sourceTrace with
  | values trace => obtain ⟨evaluated, shaped, sourceTrace⟩ := values_projections trace; exact .values shaped sourceTrace
  | fault trace => exact .fault (fault_projections trace)

end Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
/-! Actual generated index selection, including its optional default and
missing-default fault. Source lookup/default relations are independent of Core
execution. The comparator and default supply their own finite evaluations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataEqualityValues

structure Index (checked : SourceCoreDataCatalog.Checked) (sourceValue : TypeSystem.Ty) (index : PreparedIndex) where
  comparison : SourceCoreDataEquality.Prepared checked
  default : SourceCoreDefaultValue.Prepared checked
  comparisonExpression : index.comparison = comparison.expression
  defaultExpression : index.default = default.expression
  keyType : index.layout.keyType = comparison.type
  valueType : index.layout.valueType = default.type
  defaultSource : default.sourceType = sourceValue

def Index.of_generated {checked : SourceCoreDataCatalog.Checked} {fuel count : Nat}
    {sourceKey sourceValue : TypeSystem.Ty} {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {missing : Word}
    {comparison : SourceCoreDataEquality.Prepared checked} {default : SourceCoreDefaultValue.Prepared checked}
    (comparisonGenerated : SourceCoreDataEquality.prepare fuel checked sourceKey = .ok comparison)
    (defaultGenerated : SourceCoreDefaultValue.prepare (sourceValue.size + 1) checked sourceValue = .ok default)
    (keyProjection : checked.catalog.project sourceKey = .ok layout.keyType)
    (valueProjection : checked.catalog.project sourceValue = .ok layout.valueType) :
    Index checked sourceValue ⟨layout, key, count, comparison.expression, default.expression, missing⟩ where
  comparison := comparison
  default := default
  comparisonExpression := rfl
  defaultExpression := rfl
  keyType := by
    have projected := comparison.projection
    rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projected
    exact Except.ok.inj (keyProjection.symm.trans projected)
  valueType := by
    have projected := default.projection
    rw [DataPlaceMappingPreparation.default_sourceType defaultGenerated] at projected
    exact Except.ok.inj (valueProjection.symm.trans projected)
  defaultSource := DataPlaceMappingPreparation.default_sourceType defaultGenerated

inductive Reads (key : Dynamic.Value) (entries : List (Dynamic.Value × Dynamic.Value))
    (type : TypeSystem.Ty) (value : Dynamic.Value) : Prop where
  | found (lookup : Dynamic.MappingLookup key entries value) : Reads key entries type value
  | default (absent : Dynamic.MappingAbsent key entries) (valueDefault : Dynamic.DefaultValue type value) :
      Reads key entries type value

theorem Reads.projections {key value : Dynamic.Value} {entries : List (Dynamic.Value × Dynamic.Value)}
    {type : TypeSystem.Ty} (read : Reads key entries type value) (keyType : TypeSystem.Ty) :
    Dynamic.ProjectionsRead (some (.mapping keyType type entries)) [.index key] (some value) := by
  cases read with
  | found lookup => exact .indexFound lookup .nil
  | default absent valueDefault => exact .indexDefault absent valueDefault .nil

theorem Reads.update {key selected replacement : Dynamic.Value} {entries updated : List (Dynamic.Value × Dynamic.Value)}
    {type : TypeSystem.Ty} (read : Reads key entries type selected)
    (inserted : Dynamic.MappingInsert key replacement entries updated) (keyType : TypeSystem.Ty) :
    Dynamic.ProjectionsUpdate (fun _ value => value = replacement) (some (.mapping keyType type entries))
      [.index key] (.mapping keyType type updated) := by
  cases read with
  | found lookup => exact .indexFound lookup (.leaf rfl) inserted
  | default absent valueDefault => exact .indexDefault absent valueDefault (.leaf rfl) inserted

abbrev KeyRep {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) := DataMappingComparison.KeyRep certificate.comparison signatures identities

def selectedStore {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  DataMappingComparison.lookupStore certificate.comparison index.layout environment store entries key

theorem selectedIndex_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceSelected)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value, valueRel sourceSelected value ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, represented, evaluated⟩ := DataMappingComparison.lookup_found certificate.comparison index.layout
    certificate.keyType faithful keyRep related found environment store current _ mappingSelected keySelected
  refine ⟨value, represented, ?_⟩
  unfold selectedIndex
  rw [certificate.comparisonExpression]
  exact LanguageResult.bind_success _ evaluated (.caseRight (.var rfl) (.inRight (.var rfl)))

theorem selectedIndex_default {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceDefault : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources) (defaulted : Dynamic.DefaultValue sourceValue sourceDefault)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value expression, DataDefaults.Tree checked.catalog sourceValue sourceDefault value expression ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  have lookup := DataMappingComparison.lookup_absent certificate.comparison index.layout certificate.keyType faithful
    keyRep related absent environment store current _ mappingSelected keySelected
  obtain ⟨defaultValue, represented, defaultEvaluation⟩ := DataDefaults.prepared_preserves certificate.default
    (.unit :: .inLeft index.layout.valueType .unit :: environment) (selectedStore certificate environment store entries key)
  rw [certificate.defaultSource] at represented
  cases represented with
  | absent missing => exact False.elim (missing sourceDefault defaulted)
  | @present source value expression tree =>
    have same := tree.meaning.functional defaulted
    subst source
    refine ⟨value, expression, tree, ?_⟩
    unfold selectedIndex
    rw [certificate.comparisonExpression, certificate.defaultExpression]
    exact LanguageResult.bind_success _ lookup
      (.caseLeft (.var rfl) (.caseRight defaultEvaluation (.inRight (.var rfl))))

theorem selectedIndex_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    Evaluates environment store (selectedIndex prepared index current keys) (.inLeft index.layout.valueType (.word index.missing))
      (selectedStore certificate environment store entries key) := by
  have lookup := DataMappingComparison.lookup_absent certificate.comparison index.layout certificate.keyType faithful
    keyRep related absent environment store current _ mappingSelected keySelected
  obtain ⟨defaultValue, represented, defaultEvaluation⟩ := DataDefaults.prepared_preserves certificate.default
    (.unit :: .inLeft index.layout.valueType .unit :: environment) (selectedStore certificate environment store entries key)
  rw [certificate.defaultSource] at represented
  cases represented with
  | present tree => exact False.elim (missing tree.meaning.defaultable)
  | absent =>
    unfold selectedIndex
    rw [certificate.comparisonExpression, certificate.defaultExpression]
    exact LanguageResult.bind_success _ lookup
      (.caseLeft (.var rfl) (.caseLeft defaultEvaluation (.inLeft .word)))

theorem selectedStore_extension {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) :
    ∃ administrative, selectedStore certificate environment store entries key = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  DataMappingComparison.helper_store_extension certificate.comparison environment store _ _ _ _

theorem selectedIndex_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value, (valueRel sourceSelected value ∨ ∃ expression, DataDefaults.Tree checked.catalog sourceValue sourceSelected value expression) ∧
      Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word value)
        (selectedStore certificate environment store entries key) := by
  cases read with
  | found lookup =>
    obtain ⟨value, related, evaluated⟩ := selectedIndex_found certificate prepared faithful keyRep related lookup
      environment store current keys mappingSelected keySelected
    exact ⟨value, .inl related, evaluated⟩
  | default absent valueDefault =>
    obtain ⟨value, expression, represented, evaluated⟩ := selectedIndex_default certificate prepared faithful keyRep related
      absent valueDefault environment store current keys mappingSelected keySelected
    exact ⟨value, .inr ⟨expression, represented⟩, evaluated⟩

/-- A real single-index preparation supplies the comparator/default certificate.
The two projection equations authenticate its declared layout, separately from
the preparation loop, which only reads the catalog key type. -/
theorem single_index_of_prepare {checked : SourceCoreDataCatalog.Checked} {fuel : Nat}
    {route : Route} {prepared : Prepared} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceKey sourceValue registeredValue : TypeSystem.Ty}
    {entry : SourceCoreDataCatalog.Entry}
    (accepted : prepare checked fuel route invalid missing = .ok prepared)
    (routeSteps : route.steps = [.index layout key sourceValue])
    (selected : checked.catalog.entries[layout.dataType.index]? = some entry)
    (mappingType : entry.sourceType = .mapping sourceKey registeredValue)
    (keyProjection : checked.catalog.project sourceKey = .ok layout.keyType)
    (valueProjection : checked.catalog.project sourceValue = .ok layout.valueType) :
    ∃ index, Nonempty (Index checked sourceValue index) ∧ prepared.steps = [.index index] ∧
      prepared.keys = [(key, layout.keyType)] ∧ index.layout = layout ∧ index.keyPosition = 0 ∧
      index.missing = missing sourceValue := by
  rcases prepared with ⟨preparedRoute, preparedSteps, preparedKeys, preparedInvalid⟩
  obtain ⟨_, _, generated⟩ := DataPlaceMappingPreparation.steps_of_prepare accepted
  rw [routeSteps] at generated
  cases generated with
  | index selected' mappingType' comparisonGenerated defaultGenerated tail =>
    have sameEntry := Option.some.inj (selected'.symm.trans selected)
    subst sameEntry
    have sameTypes := mappingType'.symm.trans mappingType
    cases sameTypes
    cases tail
    exact ⟨_, ⟨Index.of_generated comparisonGenerated defaultGenerated keyProjection valueProjection⟩,
      rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingIndex
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
/-! One generated mapping path step, including reconstruction of the latest
root. Comparators/defaults are evaluated from their actual preparation receipts.
The source mapping list remains ordered and duplicate keys are preserved. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPlaceMappingIndex

private theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
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

theorem select_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceSelected)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value, valueRel sourceSelected value ∧
      Evaluates environment store (select prepared [.index index] current keys) (.inRight .word (.inRight .unit value))
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, represented, evaluated⟩ := selectedIndex_found certificate prepared faithful keyRep related found
    environment store current keys mappingSelected keySelected
  exact ⟨value, represented, LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))⟩

theorem select_default {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceDefault : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (absent : Dynamic.MappingAbsent sourceKey sources) (defaulted : Dynamic.DefaultValue sourceValue sourceDefault)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ value expression, DataDefaults.Tree checked.catalog sourceValue sourceDefault value expression ∧
      Evaluates environment store (select prepared [.index index] current keys) (.inRight .word (.inRight .unit value))
        (selectedStore certificate environment store entries key) := by
  obtain ⟨value, expression, represented, evaluated⟩ := selectedIndex_default certificate prepared faithful keyRep related
    absent defaulted environment store current keys mappingSelected keySelected
  exact ⟨value, expression, represented, LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))⟩

theorem update_after_selection {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store middle : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement)
    {selected : Value}
    (selection : Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word selected) middle) :
    ∃ output, OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output)
        (DataMappingComparison.insertStore certificate.comparison index.layout (replacement :: selected :: environment)
          middle entries key replacement) := by
  have shiftedKey : Selects (replacement :: selected :: environment)
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) key := by
    simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken selected).weaken replacement
  obtain ⟨output, represented, evaluated⟩ := DataMappingComparison.insert_preserves certificate.comparison index.layout
    certificate.keyType faithful keyRep replacementRep related inserted (replacement :: selected :: environment) middle
    (shift 2 current) _ (.var 0)
    (by simpa [shift, List.range_succ] using (mappingSelected.weaken selected).weaken replacement) shiftedKey (.var rfl)
  refine ⟨output, represented, LanguageResult.bind_success _ selection ?_⟩
  apply LanguageResult.bind_success _ (.inRight (by simpa [shift, List.range_succ] using (replacementSelected.weaken selected).evaluates middle))
  simpa only [certificate.comparisonExpression] using evaluated

theorem update_found {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ output finalStore administrative,
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output) finalStore ∧ finalStore = store ++ administrative ∧
      administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  obtain ⟨selected, _, selectedEvaluation⟩ := selectedIndex_found certificate prepared faithful keyRep related found
    environment store current keys mappingSelected keySelected
  obtain ⟨output, represented, evaluated⟩ := update_after_selection certificate prepared faithful keyRep replacementRep related
    inserted environment store _ current keys replacementExpression mappingSelected keySelected replacementSelected selectedEvaluation
  obtain ⟨firstCells, firstStore, firstCount⟩ := selectedStore_extension certificate environment store entries key
  obtain ⟨secondCells, secondStore, secondCount⟩ := DataMappingComparison.helper_store_extension certificate.comparison
    (replacement :: selected :: environment) (selectedStore certificate environment store entries key) _ _ _ _
  refine ⟨output, _, firstCells ++ secondCells, represented, evaluated, ?_, ?_⟩
  · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
    rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from secondStore, firstStore, List.append_assoc]
  · simp only [List.length_append, firstCount, secondCount]
    omega

theorem update_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (related : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRel sources entries)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (current keys replacementExpression : Expr)
    (mappingSelected : Selects environment current (Core.OrderedMapping.encode index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ output finalStore administrative,
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (update prepared [.index index] index.layout.type current keys replacementExpression)
        (.inRight .word output) finalStore ∧ finalStore = store ++ administrative ∧
      administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  obtain ⟨selected, _, selectedEvaluation⟩ := selectedIndex_preserves certificate prepared faithful keyRep related read
    environment store current keys mappingSelected keySelected
  obtain ⟨output, represented, evaluated⟩ := update_after_selection certificate prepared faithful keyRep replacementRep related
    inserted environment store _ current keys replacementExpression mappingSelected keySelected replacementSelected selectedEvaluation
  obtain ⟨firstCells, firstStore, firstCount⟩ := selectedStore_extension certificate environment store entries key
  obtain ⟨secondCells, secondStore, secondCount⟩ := DataMappingComparison.helper_store_extension certificate.comparison
    (replacement :: selected :: environment) (selectedStore certificate environment store entries key) _ _ _ _
  refine ⟨output, _, firstCells ++ secondCells, represented, evaluated, ?_, ?_⟩
  · change DataMappingComparison.insertStore _ _ _ _ _ _ _ = _
    rw [show DataMappingComparison.insertStore _ _ _ _ _ _ _ = _ from secondStore, firstStore, List.append_assoc]
  · simp only [List.length_append, firstCount, secondCount]
    omega

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingPath
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
/-! Closed ordinary getter/setter execution for a single mapping projection.
An absent mapping root is a virtual empty value; the helper does not write it
back. A setter reconstructs the supplied latest root and returns the new value.
The enclosing assignment performs the eventual source-cell write separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

/-- A helper's optional-root argument. This is a structural input certificate,
not a new heap relation; heap/world preservation uses GenericHeap. -/
inductive RootInput (layout : Core.OrderedMapping.Layout) (sourceKey sourceValue : TypeSystem.Ty)
    (keyRel valueRel : OrderedMapping.Relation) :
    Dynamic.Cell → Value → List (Dynamic.Value × Dynamic.Value) → Core.OrderedMapping.Entries → Prop where
  | initialized {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      (represented : OrderedMapping.EntriesRel keyRel valueRel sources entries) :
      RootInput layout sourceKey sourceValue keyRel valueRel
        ⟨.mapping sourceKey sourceValue, some (.mapping sourceKey sourceValue sources), none⟩
        (.inRight .unit (Core.OrderedMapping.encode layout entries)) sources entries
  | absent : RootInput layout sourceKey sourceValue keyRel valueRel
      ⟨.mapping sourceKey sourceValue, none, none⟩ (.inLeft layout.type .unit) [] []

theorem RootInput.initial {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries) :
    Dynamic.RootInitialValue cell (some (.mapping sourceKey sourceValue sources)) := by
  cases input with
  | initialized => exact .initialized
  | absent => exact .emptyMapping _ _

theorem RootInput.entries {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries) :
    OrderedMapping.EntriesRel keyRel valueRel sources entries := by
  cases input with
  | initialized represented => exact represented
  | absent => exact .nil

theorem RootInput.normalize {layout : Core.OrderedMapping.Layout} {sourceKey sourceValue : TypeSystem.Ty}
    {keyRel valueRel : OrderedMapping.Relation} {cell : Dynamic.Cell} {optional : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput layout sourceKey sourceValue keyRel valueRel cell optional sources entries)
    (prepared : Prepared) (rootMapping : prepared.route.rootMapping = some layout)
    {environment : Environment} {expression : Expr} (selected : Selects environment expression optional) (store : Store) :
    Evaluates environment store (normalizeRoot prepared expression)
      (.inRight .unit (Core.OrderedMapping.encode layout entries)) store := by
  simp only [normalizeRoot, rootMapping]
  cases input with
  | initialized => exact .caseRight (selected.evaluates store) (.inRight (.var rfl))
  | absent => exact .caseLeft (selected.evaluates store) (.inRight (.construct .unit))

theorem getter_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey sourceSelected : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ value finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsRead (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey] (some sourceSelected) ∧
      (valueRel sourceSelected value ∨ ∃ expression, DataDefaults.Tree checked.catalog sourceValue sourceSelected value expression) ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (.inRight .word (.inRight .unit value)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (packValues keys) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨value, represented, evaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep input.entries read
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨value, _, administrative, input.initial, read.projections sourceKeyType, represented, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))

theorem setter_preserves {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey sourceSelected sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key) (replacementRep : valueRel sourceReplacement replacement)
    (read : Reads sourceKey sources sourceValue sourceSelected)
    (inserted : Dynamic.MappingInsert sourceKey sourceReplacement sources updated)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ output finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = sourceReplacement)
        (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey] (.mapping sourceKeyType sourceValue updated) ∧
      OrderedMapping.ValueRel index.layout (KeyRep certificate signatures identities) valueRel updated output ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) (.inRight .word output) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (.pair (packValues keys) replacement) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨output, finalStore, administrative, represented, evaluated, extension, count⟩ :=
    DataPlaceMappingPath.update_preserves certificate prepared faithful keyRep replacementRep input.entries read inserted
      bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
      (.var rfl) keySelected (.second (.second (.var rfl)))
  refine ⟨output, finalStore, administrative, input.initial, read.update inserted sourceKeyType, represented, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact evaluated

/-- A missing default stops the getter after its lookup. It neither creates a
virtual source mapping cell nor evaluates a leaf continuation. -/
theorem getter_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (packValues keys))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey]
        (.missingMappingDefault sourceValue) ∧
      Evaluates environment store (.apply (getter prepared keyType) argument)
        (.inLeft prepared.optionalLeaf (.word index.missing)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (packValues keys) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  have evaluated := selectedIndex_missing certificate prepared faithful keyRep input.entries absent missing
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨_, administrative, input.initial, .indexDefaultUnavailable keyTyped absent missing, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_failure _ evaluated

/-- The updater checks the path before replacing its leaf. Missing defaults
therefore stop before insertion, including a constant replacement. -/
theorem setter_missing {checked : SourceCoreDataCatalog.Checked} {sourceValue : TypeSystem.Ty} {index : PreparedIndex}
    (certificate : Index checked sourceValue index) (prepared : Prepared)
    (steps : prepared.steps = [.index index]) (rootMapping : prepared.route.rootMapping = some index.layout)
    {signatures : ProgramSignatures} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {valueRel : OrderedMapping.Relation}
    {sourceKeyType : TypeSystem.Ty} {cell : Dynamic.Cell} {optional : Value}
    {sourceKey : Dynamic.Value} {key replacement : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (input : RootInput index.layout sourceKeyType sourceValue (KeyRep certificate signatures identities) valueRel cell optional sources entries)
    (keyRep : KeyRep certificate signatures identities sourceKey key)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches sourceKey sourceKeyType)
    (absent : Dynamic.MappingAbsent sourceKey sources) (missing : ¬ Dynamic.Defaultable sourceValue)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement))) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some (.mapping sourceKeyType sourceValue sources)) ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKeyType sourceValue sources)) [.index sourceKey]
        (.missingMappingDefault sourceValue) ∧
      Evaluates environment store (.apply (setter prepared keyType) argument)
        (.inLeft index.layout.type (.word index.missing)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let bodyEnvironment := Core.OrderedMapping.encode index.layout entries :: .pair optional (.pair (packValues keys) replacement) :: environment
  have keySelected : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  have evaluated := selectedIndex_missing certificate prepared faithful keyRep input.entries absent missing
    bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.var rfl) keySelected
  obtain ⟨administrative, extension, count⟩ := selectedStore_extension certificate bodyEnvironment store entries key
  refine ⟨_, administrative, input.initial, .indexDefaultUnavailable keyTyped absent missing, ?_, extension, count⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (input.normalize prepared rootMapping (.first (.var rfl)) store)
  exact LanguageResult.bind_failure _ evaluated

end Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree
/-! Finite observations of mixed member/mapping paths. Certificates contain
structural source/Core data and compiler receipts, never evaluations of child
code. They observe the selected path only; a complete heap payload relation
must additionally authenticate unselected siblings and function bodies. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues DataPlaceMappingIndex

inductive Tree (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) (prepared : Prepared) (keys : List Value)
    (resultRelation : OrderedMapping.Relation) :
    Dynamic.Value → Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {source : Dynamic.Value} {value : Value} (represented : resultRelation source value) :
      Tree checked signatures identities prepared keys resultRelation source value [] [] source 0
  | member {metadata : DataConstructorInstantiation} {tag : ConstructorId}
      {sources : List Dynamic.Value} {values : List Value} {branch : MemberBranch}
      {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch} {fieldType : Ty} {name : String}
      {sourceChild sourceLeaf : Dynamic.Value} {valueChild : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (authenticated : checked.catalog.resolveConstructor signatures metadata = .ok tag)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag)
      (sourceArity : metadata.payloadTypes.length = sources.length)
      (coreArity : branch.payloadTypes.length = values.length)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : Tree checked signatures identities prepared keys resultRelation sourceChild valueChild steps projections sourceLeaf count) :
      Tree checked signatures identities prepared keys resultRelation
        (.constructed metadata sources) (.constructed tag (packValues values))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) sourceLeaf count
  | mapping {sourceKeyType sourceValueType : TypeSystem.Ty} {index : PreparedIndex}
      (certificate : Index checked sourceValueType index)
      {valueRelation : OrderedMapping.Relation} {sourceKey sourceChild sourceLeaf : Dynamic.Value}
      {key : Value} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
      {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (keyRep : KeyRep certificate signatures identities sourceKey key)
      (keyAt : keys[index.keyPosition]? = some key)
      (entriesRep : OrderedMapping.EntriesRel (KeyRep certificate signatures identities) valueRelation sources entries)
      (selected : Reads sourceKey sources sourceValueType sourceChild)
      (tail : ∀ value, (valueRelation sourceChild value ∨
          ∃ expression, DataDefaults.Tree checked.catalog sourceValueType sourceChild value expression) →
        Tree checked signatures identities prepared keys resultRelation sourceChild value steps projections sourceLeaf count) :
      Tree checked signatures identities prepared keys resultRelation
        (.mapping sourceKeyType sourceValueType sources) (Core.OrderedMapping.encode index.layout entries)
        (.index index :: steps) (.index sourceKey :: projections) sourceLeaf
        (checked.catalog.entries.length + 1 + count)

/-- Every certificate executes the actual recursive selector, deriving all
comparison/default/child evaluations and preserving the entire input store
prefix. Each mapping selection contributes its own ordinary helper cells. -/
theorem Tree.preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {prepared : Prepared} {keys : List Value}
    {resultRelation : OrderedMapping.Relation} {source : Dynamic.Value} {value : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {sourceLeaf : Dynamic.Value} {count : Nat}
    (tree : Tree checked signatures identities prepared keys resultRelation source value steps projections sourceLeaf count)
    (faithful : IdentityFaithful identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ leaf finalStore administrative,
      Dynamic.ProjectionsRead (some source) projections (some sourceLeaf) ∧ resultRelation sourceLeaf leaf ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inRight .word (.inRight .unit leaf)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression with
  | leaf represented => exact ⟨_, store, [], .nil, represented, .inRight (.inRight (selected.evaluates store)), by simp, rfl⟩
  | @member metadata tag sources values branch dataType index branches fieldType name sourceChild sourceLeaf valueChild steps projections count authenticated owner branchAt constructor sourceArity coreArity sourceAt coreAt tail ih =>
    obtain ⟨leaf, finalStore, administrative, read, represented, evaluated, extended, counted⟩ :=
      ih (packValues values :: environment) store _ _
        (projectPacked_selects (Selects.var (index := 0) rfl) coreArity index coreAt)
        (by simpa [shift] using keysSelected.weaken (packValues values))
    exact ⟨leaf, finalStore, administrative, .member sourceAt read, represented,
      .matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) evaluated,
      extended, counted⟩
  | @mapping sourceKeyType sourceValueType index certificate valueRelation sourceKey sourceChild sourceLeaf key sources entries steps projections count keyRep keyAt entriesRep read tail ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyRep entriesRep read
      environment store current keyExpression selected keySelected
    obtain ⟨leaf, finalStore, after, tailRead, represented, tailEvaluated, extended, counted⟩ :=
      ih child childRep (child :: environment) _ (.var 0) (shift 1 keyExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken child)
    obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
    refine ⟨leaf, finalStore, before ++ after, ?_, represented,
      LanguageResult.bind_success _ childEvaluated tailEvaluated, ?_, ?_⟩
    · cases read with
      | found lookup => exact .indexFound lookup tailRead
      | default absent defaulted => exact .indexDefault absent defaulted tailRead
    · rw [extended, beforeExtended, List.append_assoc]
    · simp only [List.length_append, beforeCounted, counted]

end Solcore.SourceSemantics.CoreLowering.DataPlaceReadTree
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
/-! Typed actual-environment composition for the real argument packing helper.
Static trees, source traces and payload results are shared with the unrestricted
sequence theory. Each inserted payload receives its type from the represented
result, and the existing environment is transported along the actual world
extension before the next child executes. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
open GenericExpressionMeaning (Certificate FaultRep agree_prefix rename_prefix)
open DataPatternValues DataExpressionSequence

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr}

/-- Successful evaluation keeps left-to-right effects and every represented
payload, including captured references inside earlier argument values. -/
theorem preserves_values (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsEvaluate program context evidence source environment before ids sources after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction tree generalizing mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata⟩ := meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | value payload =>
        exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
          finalHeaps, maps, worlds, frame, metadata⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
          maps, worlds, frame, metadata⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) rest
        have nonempty : values ≠ [] := by
          intro absent
          have lengths := restRep.length.2
          simp [absent] at lengths
        refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
          .cons (model.extend payload maps worlds) restRep, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [rename_prefix] at second
        have combined := LocalSequence.pair_success lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
        simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

variable {expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost}
  {listPost : ExpressionFailurePostContracts.ExpressionsFaultPost}

/-- A source fault evaluates only its successful prefix. The generated helper
propagates the exact token without evaluating later arguments. -/
theorem preserves_fault_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedPreserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      listPost program context evidence source environment before ids reason after token finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched,
          finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped (.fault failed)
      cases represented with
      | fault matched =>
        refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps, worlds, frame, metadata, joins.head failed (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type evaluated
    | tail head failed =>
      obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout actualTyped (.value head)
      cases represented with
      | @value sourceValue coreValue payload =>
        obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
          maps, worlds, frame, metadata, retained⟩ := ih
            (environments.extend firstMaps firstWorlds) middleHeaps
            (locals.mono firstMetadata) (agree_prefix layout coreValue)
            (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) failed
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, joins.tail head failed retained⟩
        rw [rename_prefix] at second
        simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
          (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

theorem preserves_fault (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Dynamic.ExpressionsFault program context evidence source environment before ids reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := preserves_fault_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedPreserves.of_trivial meaning) environments heaps locals layout actualTyped execution
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed evaluation of the actual generated bundle constructs a
finite source trace. Typed inserted temporary slots are admitted through
the child theorem's explicit renaming; no exact closure weakening is used. -/
theorem reflects_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedReflects model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  induction tree generalizing mapping world actual actualContext before store ξ value finalStore with
  | nil =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (show Evaluates actual store
      ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
    exact ⟨.ok [], before, mapping, world, .values .nil, .values (values := []) .nil, heaps,
      .refl _, .refl _, .refl _ _, .refl _, trivial⟩
  | single found generated =>
    obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped evaluated
    cases represented with
    | value payload =>
      cases execution with
      | value trace => exact ⟨.ok [_], after, finalMap, finalWorld,
          .values (.cons trace .nil), .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata, trivial⟩
    | fault matched =>
      cases execution with
      | fault trace => exact ⟨.error _, after, finalMap, finalWorld,
          .fault (.head trace), .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    change Evaluates actual store ((LocalSequence.pair lowered.type
      (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
      (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
    rw [pair_rename] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft first _ =>
      obtain ⟨outcome, after, finalMap, finalWorld, execution, represented, finalHeaps,
        maps, worlds, frame, metadata, retained⟩ := meaning generated found environments heaps locals layout actualTyped first
      cases represented with
      | fault matched =>
        cases execution with
        | fault trace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.pair_left_failure lowered.type
            (SourceCoreCalls.packArguments (nextCode :: codes)).type first)
          exact ⟨.error _, after, finalMap, finalWorld, .fault (.head trace), .fault matched,
            finalHeaps, maps, worlds, frame, metadata, ⟨_, rfl, joins.head trace (ExpressionFailurePostContracts.OutcomePost.fault retained)⟩⟩
    | caseRight first continuation =>
      obtain ⟨outcome, middle, middleMap, middleWorld, execution, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, _firstPost⟩ :=
        meaning generated found environments heaps locals layout actualTyped first
      cases represented with
      | @value sourceValue coreValue payload =>
        rename_i middleStore coreValue
        have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
            (coreValue :: actual) := agree_prefix layout coreValue
        cases execution with
        | value firstSource =>
          cases continuation with
          | caseLeft second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) shifted
            cases result with
            | fault matched =>
              cases sourceTrace with
              | fault tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_right_failure lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                exact ⟨.error _, after, finalMap, finalWorld, .fault (.tail firstSource tailSource), .fault matched,
                  finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata,
                  ⟨_, rfl, joins.tail firstSource tailSource (ExpressionFailurePostContracts.ListOutcomePost.fault retained)⟩⟩
          | caseRight second _ =>
            have shifted := second
            rw [← rename_prefix] at shifted
            obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, result, finalHeaps,
              maps, worlds, frame, metadata, retained⟩ := ih (environments.extend firstMaps firstWorlds) middleHeaps
                (locals.mono firstMetadata) nextLayout
                (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds)) shifted
            cases result with
            | @values sources values restRep =>
              cases sourceTrace with
              | values tailSource =>
                obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete
                  (LocalSequence.pair_success lowered.type
                    (SourceCoreCalls.packArguments (nextCode :: codes)).type first second)
                have nonempty : values ≠ [] := by
                  intro absent
                  have lengths := restRep.length.2
                  simp [absent] at lengths
                refine ⟨.ok (sourceValue :: sources), after, finalMap, finalWorld,
                  .values (.cons firstSource tailSource), ?_, finalHeaps,
                  firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans metadata, trivial⟩
                simpa [packValues, nonempty] using
                  Result.values (codes := lowered :: nextCode :: codes)
                    (.cons (model.extend payload maps worlds) restRep)

theorem reflects (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, _⟩ := reflects_with_post tree
    (ExpressionFailurePostContracts.trivial_sequence_joins program context evidence source)
    (ExpressionFailurePostContracts.TypedReflects.of_trivial meaning) environments heaps locals layout actualTyped evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_with_post (tree : Tree source certificate scope ids sourceTypes codes)
    (joins : ExpressionFailurePostContracts.SequenceJoins expressionPost listPost program context evidence source)
    (meaning : ExpressionFailurePostContracts.TypedPreserves model program context evidence source certificate faults expressionPost)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ExpressionFailurePostContracts.ListOutcomePost listPost program context evidence source environment before ids
        (SourceCoreCalls.packArguments codes).type outcome after value finalMap finalWorld finalStore := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values tree (ExpressionFailurePostContracts.TypedPreserves.forget meaning) environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata, trivial⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, retained⟩ := preserves_fault_with_post tree joins meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata, ⟨token, rfl, retained⟩⟩

theorem preserves (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases execution with
  | values execution =>
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_values tree meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .values represented,
      finalHeaps, maps, worlds, frame, metadata⟩
  | fault execution =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata⟩ := preserves_fault tree meaning environments heaps locals layout actualTyped execution
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault represented,
      finalHeaps, maps, worlds, frame, metadata⟩

/-- Finiteness comes from the independent source trace. Fuel exhaustion remains
a resumable machine state, rather than a successful or faulting source outcome. -/
theorem preserves_sufficient_fuel (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Outcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (execution : Trace program context evidence source environment before ids outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → runStateful fuel
        (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := preserves tree meaning environments heaps locals layout actualTyped execution
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required, runs, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_done (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value} {fuel : Nat}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (completed : runStateful fuel
      (.initial ((SourceCoreCalls.packArguments codes).expression.rename ξ) actual store) = .done value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  reflects tree meaning environments heaps locals layout actualTyped (runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder
/-! Typed argument packing for place keys reuses the independent projection
traces and their established ordering. Actual inserted operands may include
closures; their runtime types come from the complete represented payloads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPlaceKeyOrder
open GenericExpressionMeaning (FaultRep)
open SourceCoreLocalCell (Scope)

/-- Index effects are evaluated exactly once in source projection order. The
generated values remain fully represented after later index effects. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, shaped, executed⟩ := projections_values trace
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := TypedDataExpressionSequence.preserves_values tree meaning environments heaps locals layout actualTyped executed
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  TypedDataExpressionSequence.preserves_fault tree meaning environments heaps locals layout actualTyped (projections_fault trace)

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      OutcomeTrace program context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := TypedDataExpressionSequence.reflects tree meaning environments heaps locals layout actualTyped evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata⟩
  cases sourceTrace with
  | values trace => obtain ⟨evaluated, shaped, sourceTrace⟩ := values_projections trace; exact .values shaped sourceTrace
  | fault trace => exact .fault (fault_projections trace)

end Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
/-! A readable independent projection path can install a fixed replacement.
This is a structural source theorem: it does not evaluate a compiler or compare
Core values, and first-match lookup determines the replaced mapping position. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
open Solcore.SourceSemantics.Dynamic

private theorem replace_found {key selected replacement : Value} {entries : List (Value × Value)}
    (found : MappingLookup key entries selected) : ∃ updated, MappingUpdate key replacement entries updated := by
  induction found with
  | head equal => exact ⟨_, .head equal⟩
  | tail different found ih => obtain ⟨updated, changed⟩ := ih; exact ⟨_, .tail different changed⟩

private theorem replace_at {values : List Value} {index : Nat} {selected replacement : Value}
    (found : ValueAt values index selected) : ∃ updated, ValuesReplaceAt values index replacement updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail found ih => obtain ⟨updated, changed⟩ := ih; exact ⟨_, .tail changed⟩

/-- Every selected path supports one fixed, already computed replacement. The
replacement never affects key evaluation or reconstruction of earlier nodes. -/
theorem read_update {initial selected : Option Value} {projections : List EvaluatedProjection}
    (read : ProjectionsRead initial projections selected) (replacement : Value) :
    ∃ updated, ProjectionsUpdate (fun _ value => value = replacement) initial projections updated := by
  induction read with
  | nil => exact ⟨replacement, .leaf rfl⟩
  | indexFound found read ih =>
    obtain ⟨child, changed⟩ := ih
    obtain ⟨entries, inserted⟩ := replace_found (replacement := child) found
    exact ⟨_, .indexFound found changed (.update inserted)⟩
  | indexDefault absent defaulted read ih =>
    obtain ⟨child, changed⟩ := ih
    exact ⟨_, .indexDefault absent defaulted changed (.append absent)⟩
  | member found read ih =>
    obtain ⟨child, changed⟩ := ih
    obtain ⟨values, replaced⟩ := replace_at (replacement := child) found
    exact ⟨_, .member found changed replaced⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
/-! Source ordering facts used when reflecting the Core modifier before the
latest-root setter. An absent snapshot has no projections, and a successfully
resolved nonempty ordinary root cannot become uninitialized during the RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

theorem read_none {initial : Option Value} {projections : List EvaluatedProjection}
    (read : ProjectionsRead initial projections none) : initial = none ∧ projections = [] := by
  have aux : ∀ {current : Option Value} {path : List EvaluatedProjection} {selected : Option Value},
      ProjectionsRead current path selected → selected = none → current = none ∧ path = [] := by
    intro current path selected selectedBy
    induction selectedBy with
    | nil => intro absent; exact ⟨absent, rfl⟩
    | indexFound _ _ ih => intro absent; cases (ih absent).1
    | indexDefault _ _ _ ih => intro absent; cases (ih absent).1
    | member _ _ ih => intro absent; cases (ih absent).1
  exact aux read rfl

theorem resolve_none {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (resolve : SourcePlaceResolves program context evidence source environment before place target after)
    (absent : target.selected = none) : target.projections = [] := by
  cases resolve with
  | intro lookup initialRead keys currentRead root selection =>
    simp only at absent
    rw [absent] at selection
    exact (read_none selection).2

/-- The resolved target retains the declaration type of the original root.
Index expression effects may change its value, but preserve this metadata. -/
theorem resolve_root_type {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (resolve : SourcePlaceResolves program context evidence source environment before place target after)
    (metadata : HeapMetadataExtend before after) {location : Location} {cell : Cell}
    (lookup : Environment.LooksUp environment place.root location)
    (read : Heap.Reads before location cell) : target.rootType = cell.type := by
  cases resolve with
  | intro actualLookup initialRead keys currentRead root selection =>
    have same := lookup.functional actualLookup
    subst_vars
    obtain ⟨current, selected, sameType, _⟩ := metadata _ _ read
    have same := currentRead.functional selected
    subst_vars
    exact sameType

/-- Latest-root absence contradicts a successfully resolved nonempty path.
Virtual empty mappings are handled separately by their retained source type;
the initialized-location invariant is derived from the actual RHS trace. -/
theorem latest_uninitialized_impossible {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before targetHeap after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace} {id : ExpressionId} {right : Value}
    (resolve : SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (rhs : ExpressionEvaluates program context evidence source environment targetHeap id right after)
    {current : Cell} (read : Heap.Reads after target.location current)
    (sameType : current.type = target.rootType) (absent : RootInitialValue current none)
    (nonempty : target.projections ≠ []) : False := by
  cases resolve with
  | intro lookup initialRead keys oldRead oldRoot selection =>
    cases absent with
    | uninitialized notMapping =>
      cases oldRoot with
      | initialized =>
        obtain ⟨latest, latestRead, present⟩ := rhs.initialization_extends _ _ oldRead (by simp)
        have same := read.functional latestRead
        subst latest
        exact present rfl
      | emptyMapping key value => exact notMapping ⟨key, value, sameType⟩
      | uninitialized => cases selection; exact nonempty rfl

end Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
/-! Original mapping-index paths determine their declared root from the exact
stored key types and selected leaf. This supports genuine Source typing without
assuming that an arbitrary lexical context matches compiler binder metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
open Core Frontend SourceInference

inductive Route (source : TypedSource) : TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil {type} : Route source type [] type
  | index {key node keyType valueType rest leaf}
      (found : source.lookupExpression? key = some node)
      (same : node.type = keyType)
      (tail : Route source valueType rest leaf) :
      Route source (.mapping keyType valueType) (.index key :: rest) leaf

/-- The original key nodes and final leaf fix every mapping layer. -/
theorem Route.root_type {source : TypedSource} {context : SourceSemantics.Context}
    {declared actual leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (unique : NodeOccurrencesUnique source) (route : Route source declared projections leaf)
    (typed : SourceProjectionsHaveType source context actual projections leaf) : actual = declared := by
  induction route generalizing actual with
  | nil => cases typed; rfl
  | index found same tail ih =>
      cases typed with
      | index keyTyped restTyped =>
          obtain ⟨original, contains, stored⟩ := keyTyped.stored_type
          cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
          cases stored.symm.trans same
          cases ih restTyped
          rfl

theorem Route.key_found {source : TypedSource} {root leaf : TypeSystem.Ty}
    {projections : List PlaceProjection} (route : Route source root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ node, source.lookupExpression? id = some node := by
  induction route with
  | nil => cases member
  | @index key node keyType valueType rest leaf found same tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨node, equal ▸ found⟩
      · exact ih member

theorem Route.key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (unique : NodeOccurrencesUnique source) (route : Route source root projections leaf)
    (typed : SourceProjectionsHaveType source context root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type := by
  induction route with
  | nil => cases member
  | index found same tail ih =>
      cases typed with
      | index keyTyped restTyped =>
          rcases List.mem_cons.mp member with equal | member
          · subst id
            obtain ⟨original, contains, stored⟩ := keyTyped.stored_type
            cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
            exact ⟨_, found, stored.symm ▸ keyTyped⟩
          · exact ih restTyped member

/-- This check follows the retained source path; members are outside this profile. -/
def check (source : TypedSource) (root : TypeSystem.Ty) (projections : List PlaceProjection)
    (leaf : TypeSystem.Ty) : Option (PLift (Route source root projections leaf)) :=
  match projections with
  | [] => if same : root = leaf then some ⟨same ▸ .nil⟩ else none
  | .member _ _ :: _ => none
  | .index key :: rest =>
      match root with
      | .mapping keyType valueType => do
          match found : source.lookupExpression? key with
          | none => none
          | some node =>
              if same : node.type = keyType then do
                let ⟨tail⟩ ← check source valueType rest leaf
                pure ⟨.index found same tail⟩
              else none
      | _ => none

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
end
