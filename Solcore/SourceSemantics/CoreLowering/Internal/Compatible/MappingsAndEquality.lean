import Solcore.Frontend.SourceCoreCompatibleDataEquality
import Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Payloads
import Solcore.SourceSemantics.CoreLowering.DataEqualityValues
import Solcore.SourceSemantics.CoreLowering.DataEqualityCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Encoding
import Solcore.SourceSemantics.CoreLowering.OrderedMapping
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.CoreLowering.DataPatternAuthenticity
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming
import Solcore.Frontend.SourceCoreCompatibleDataPlaces
import Solcore.SourceSemantics.CoreLowering.DataPlaceMembers
import Solcore.SourceSemantics.Dynamic.RuntimeType
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.Frontend.SourceCorePublicOutputShapes

/-!
# Compatible profile: mappings and equality

Mapping entries, views, execution, updates and mixed paths, and generated equality.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityInstalled
/-! Exact initialization of the actual compatible comparator helpers. The
adapter below is used only by generic allocation/closure-storage lemmas. It
never reuses a strict projection or a strict semantic preparation receipt. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality

/-- Same administrative layout, with no claim about strict data semantics. -/
def storageCatalog (catalog : Catalog) : SourceCoreDataCatalog.Catalog :=
  ⟨catalog.entries, catalog.callableContracts⟩

theorem allocate_storage (catalog : Catalog) (next : Expr) :
    allocate catalog next = SourceCoreDataEquality.allocate (storageCatalog catalog) next := rfl

theorem install_storage (catalog : Catalog) (bodies : List Expr) (next : Expr) :
    install catalog bodies next = SourceCoreDataEquality.install (storageCatalog catalog) bodies next := rfl

private theorem mapM_length {α β ε : Type} (function : α → Except ε β) {inputs : List α} {outputs : List β}
    (generated : inputs.mapM function = .ok outputs) : outputs.length = inputs.length := by
  induction inputs generalizing outputs with
  | nil => cases generated; rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at generated
    obtain ⟨first, _, generated⟩ := DataEqualityGeneration.bind_ok generated
    obtain ⟨rest, remaining, generated⟩ := DataEqualityGeneration.bind_ok generated
    cases generated
    exact congrArg Nat.succ (ih remaining)

theorem bodies_length {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) : bodies.length = catalog.entries.length := by
  simpa using mapM_length (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩) generated

abbrev Installed (catalog : Catalog) := DataEqualityInstalled.Installed (storageCatalog catalog)

def preparedClosure {checked : Checked} (prepared : Prepared checked) (environment : Environment) (base : Nat) : Value :=
  .closure (.product prepared.type prepared.type) .bool
    (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
    (DataEqualityInstalled.captured prepared.bodies.length
      (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) base environment))

def preparedStore {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) : Store :=
  store ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies

theorem prepared_evaluates_exact {checked : Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Evaluates environment store prepared.expression (preparedClosure prepared environment store.length)
      (preparedStore prepared environment store) := by
  rw [prepared.expression_eq, allocate_storage, install_storage, DataEqualityInstalled.allocate_eq_types]
  apply DataEqualityInstalled.allocate_types_evaluates
  apply DataEqualityInstalled.install_evaluates (storageCatalog checked.catalog) _ store _ prepared.bodies
  · exact DataEqualityInstalled.allocated_references _ _ _
  · simp [DataEqualityInstalled.emptyCells, DataEqualityInstalled.catalogTypes_length, storageCatalog, bodies_length prepared.bodiesGenerated]
  · exact Nat.le_of_eq (bodies_length prepared.bodiesGenerated)

theorem prepared_installed {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) :
    Installed checked.catalog prepared.bodies store.length environment (preparedStore prepared environment store) := by
  intro index body found
  simpa [preparedStore, Store.read?, List.getElem?_append_right] using
    (DataEqualityInstalled.cells_lookup
      (environment := DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) found)

theorem prepared_run {checked : Checked} (prepared : Prepared checked) (environment : Environment) (store : Store) :
    (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel (.initial prepared.expression environment store) =
      .done (preparedClosure prepared environment store.length) (preparedStore prepared environment store)) ∧
    (∀ fuel value finalStore, runStateful fuel (.initial prepared.expression environment store) = .done value finalStore →
      value = preparedClosure prepared environment store.length ∧ finalStore = preparedStore prepared environment store) :=
  ⟨evaluation_runStateful_complete_with_sufficient_fuel (prepared_evaluates_exact prepared environment store),
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) (prepared_evaluates_exact prepared environment store)⟩

/-- Lookup in the actual compatible helper generator, retaining each body. -/
theorem helperBodies_lookup {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) {index : Nat} (bound : index < catalog.entries.length) :
    ∃ body, bodies[index]? = some body ∧ helperBody fuel catalog ⟨index⟩ = .ok body :=
  DataEqualityGeneration.mapM_lookup
    (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩) generated
    (input := (catalog.entries[index], index)) (by simp [List.getElem?_zipIdx, List.getElem?_eq_getElem bound])

theorem nominalBody_branches {fuel : Nat} {catalog : Catalog} {id : DataTypeId}
    {payloads : List Ty} {body : Expr} (generated : nominalBody fuel catalog id payloads = .ok body)
    {leftIndex rightIndex : Nat} {leftType rightType : Ty}
    (leftSelected : payloads[leftIndex]? = some leftType) (rightSelected : payloads[rightIndex]? = some rightType) :
    ∃ branches rightBranches branch,
      body = .matchData id .bool (.first (.var 0)) branches ∧
      branches[leftIndex]? = some (.matchData id .bool (.second (.var 1)) rightBranches) ∧
      rightBranches[rightIndex]? = some branch ∧
      (if leftIndex = rightIndex then compareType fuel catalog 3 leftType (.var 1) (.var 0)
       else .ok (.bool false)) = .ok branch := by
  unfold nominalBody at generated
  obtain ⟨branches, generatedBranches, generated⟩ := DataEqualityGeneration.bind_ok generated
  cases generated
  obtain ⟨leftBranch, selectedBranch, generatedLeft⟩ := DataEqualityGeneration.mapM_lookup _ generatedBranches
    (index := leftIndex) (input := (leftType, leftIndex)) (by simp [List.getElem?_zipIdx, leftSelected])
  obtain ⟨rightBranches, generatedRight, generatedLeft⟩ := DataEqualityGeneration.bind_ok generatedLeft
  cases generatedLeft
  obtain ⟨branch, selectedRight, generatedBranch⟩ := DataEqualityGeneration.mapM_lookup _ generatedRight
    (index := rightIndex) (input := (rightType, rightIndex)) (by simp [List.getElem?_zipIdx, rightSelected])
  exact ⟨branches, rightBranches, branch, rfl, selectedBranch, selectedRight, generatedBranch⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityTree
/-! Finite comparison traces for the compatible templates. Transport premises
are pure statements about independent source equality. They carry no evaluator
or child execution premise; authenticated metadata will establish them. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend DataEquality

inductive Tree (identities : Dynamic.Value → Word → Prop) (store : Store) :
    Environment → Expr → Dynamic.Value → Dynamic.Value → Bool → Prop where
  | base {environment expression left right result}
      (tree : DataEquality.Tree identities store environment expression left right result) :
      Tree identities store environment expression left right result
  | product {environment : Environment} {left right : Expr} {a b c d : Dynamic.Value} {first second : Bool}
      (firstTree : Tree identities store environment left a c first)
      (secondTree : Tree identities store environment right b d second) :
      Tree identities store environment (.ifE left right (.bool false)) (.product a b) (.product c d) (first && second)
  | invoke {environment captured : Environment} {reference left right body : Expr}
      {leftValue rightValue : Value} {location : Nat} {type : Core.Ty} {a b : Dynamic.Value} {result : Bool}
      (referenceSelected : Selects environment reference
        (.cellRef (OptionalCell.cellType (SourceCoreDataEquality.comparatorType type)) location))
      (leftSelected : Selects environment left leftValue)
      (rightSelected : Selects environment right rightValue)
      (installed : store[location]? = some (.inRight .unit (.closure (.product type type) .bool body captured)))
      (comparison : Tree identities store (.pair leftValue rightValue :: captured) body a b result) :
      Tree identities store environment (SourceCoreDataEquality.invoke reference left right) a b result
  | dataSame {environment : Environment} {left right : Expr} {branches rightBranches : List Expr} {body : Expr}
      {id : DataTypeId} {index : Nat} {leftPayload rightPayload : Value}
      {leftSource rightSource leftPacked rightPacked : Dynamic.Value} {result : Bool}
      (leftSelected : Selects environment left (.constructed ⟨id, index⟩ leftPayload))
      (rightSelected : Selects environment right (.constructed ⟨id, index⟩ rightPayload))
      (leftBranch : branches[index]? = some (.matchData id .bool (right.weakenAt 0) rightBranches))
      (rightBranch : rightBranches[index]? = some body)
      (meaning : Dynamic.ValueEquivalent leftPacked rightPacked ↔ Dynamic.ValueEquivalent leftSource rightSource)
      (payload : Tree identities store (rightPayload :: leftPayload :: environment) body leftPacked rightPacked result) :
      Tree identities store environment (.matchData id .bool left branches) leftSource rightSource result
  | dataDifferent {environment : Environment} {left right : Expr} {branches rightBranches : List Expr}
      {id : DataTypeId} {leftIndex rightIndex : Nat} {leftPayload rightPayload : Value}
      {leftSource rightSource : Dynamic.Value}
      (distinct : leftSource ≠ rightSource)
      (leftSelected : Selects environment left (.constructed ⟨id, leftIndex⟩ leftPayload))
      (rightSelected : Selects environment right (.constructed ⟨id, rightIndex⟩ rightPayload))
      (leftBranch : branches[leftIndex]? = some (.matchData id .bool (right.weakenAt 0) rightBranches))
      (rightBranch : rightBranches[rightIndex]? = some (.bool false)) :
      Tree identities store environment (.matchData id .bool left branches) leftSource rightSource false

theorem Tree.meaning {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {store : Store} {environment : Environment} {expression : Expr} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    result = true ↔ Dynamic.ValueEquivalent left right := by
  induction tree with
  | base tree => exact tree.meaning faithful
  | product _ _ left right => simpa [Bool.and_eq_true, product_equivalent] using and_congr left right
  | invoke _ _ _ _ _ ih => exact ih
  | dataSame _ _ _ _ meaning _ ih => exact ih.trans meaning
  | dataDifferent distinct _ _ _ _ =>
      constructor
      · intro impossible; cases impossible
      · intro equivalent; exact False.elim (distinct equivalent.1)

theorem Tree.evaluates {identities : Dynamic.Value → Word → Prop}
    {store : Store} {environment : Environment} {expression : Expr} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    Evaluates environment store expression (.bool result) store := by
  induction tree with
  | base tree => exact tree.evaluates
  | @product environment left right a b c d first second _ _ leftIH rightIH =>
      cases first
      · exact .ifFalse leftIH .bool
      · exact .ifTrue leftIH rightIH
  | invoke reference left right installed _ ih =>
      exact .caseRight (.loadCell (reference.evaluates store) installed)
        (.apply (.var rfl) (.pair ((left.weaken _).evaluates store) ((right.weaken _).evaluates store)) ih)
  | dataSame left right leftBranch rightBranch _ _ ih =>
      exact .matchData (left.evaluates store) rfl leftBranch
        (.matchData ((right.weaken _).evaluates store) rfl rightBranch ih)
  | dataDifferent _ left right leftBranch rightBranch =>
      exact .matchData (left.evaluates store) rfl leftBranch
        (.matchData ((right.weaken _).evaluates store) rfl rightBranch .bool)

theorem Tree.run {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {store : Store} {environment : Environment} {expression : Expr} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    (result = true ↔ Dynamic.ValueEquivalent left right) ∧
    (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel (.initial expression environment store) = .done (.bool result) store) ∧
    (∀ fuel value finalStore, runStateful fuel (.initial expression environment store) = .done value finalStore →
      value = .bool result ∧ finalStore = store) :=
  ⟨tree.meaning faithful, evaluation_runStateful_complete_with_sufficient_fuel tree.evaluates,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) tree.evaluates⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityValues
/-! Finite equality observations retain raw metadata authentication. Mapping
entries/defaults are opaque to equality; their full representation remains in
CompatiblePayload. Callable identities are explicit semantic receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceInference DataEquality CompatiblePayload
abbrev Catalog := SourceCoreCompatibleCatalog.Catalog
abbrev Registry := SourceCoreRawMetadata.Registry

inductive DataMeaning (registry : Registry) (catalog : Catalog) : ConstructorId → Dynamic.Value → Dynamic.Value → Prop where
  | proxy {inner : TypeSystem.Ty} {id : DataTypeId} {word : Word}
      (metadata : MetadataRep registry (.proxy inner) word)
      (selected : catalog.identity? (.proxy inner) = some id) :
      DataMeaning registry catalog ⟨id, 0⟩ (.proxy inner) (.word word)
  | constructed {metadata : DataConstructorInstantiation} {id : Word} {tag : ConstructorId}
      {sources : List Dynamic.Value} {packed : Dynamic.Value}
      (authenticated : MetadataRep registry (.constructor metadata) id)
      (selected : catalog.constructor? metadata = some tag)
      (arity : sources.length = metadata.payloadTypes.length)
      (packing : Dynamic.ValuesPack sources packed) :
      DataMeaning registry catalog tag (.constructed metadata sources) (.product (.word id) packed)

theorem DataMeaning.tags_equal {registry : Registry} {catalog : Catalog}
    {leftTag rightTag : ConstructorId} {source left right : Dynamic.Value}
    (a : DataMeaning registry catalog leftTag source left) (b : DataMeaning registry catalog rightTag source right) : leftTag = rightTag := by
  cases a with
  | proxy leftAuth leftSelected =>
    cases b with
    | proxy rightAuth rightSelected =>
      exact congrArg (fun id => ConstructorId.mk id 0) (Option.some.inj (leftSelected.symm.trans rightSelected))
  | constructed leftAuth leftSelected leftArity leftPacking =>
    cases b with
    | constructed rightAuth rightSelected rightArity rightPacking =>
      exact Option.some.inj (leftSelected.symm.trans rightSelected)

/-- Raw IDs distinguish aliases even when the native catalog owner is shared. -/
theorem DataMeaning.equivalent {registry : Registry} {catalog : Catalog}
    {leftTag rightTag : ConstructorId} {left right leftPayload rightPayload : Dynamic.Value}
    (a : DataMeaning registry catalog leftTag left leftPayload)
    (b : DataMeaning registry catalog rightTag right rightPayload) :
    Dynamic.ValueEquivalent leftPayload rightPayload ↔ Dynamic.ValueEquivalent left right := by
  cases a with
  | @proxy leftInner leftId leftWord leftAuth leftSelected =>
    cases b with
    | @proxy rightInner rightId rightWord rightAuth rightSelected =>
      constructor
      · rintro ⟨same, _⟩
        have words := Dynamic.Value.word.inj same
        have raw := (leftAuth.ids_equal_iff rightAuth).mp words
        have inners := SourceCoreRawMetadata.Metadata.proxy.inj raw
        subst rightInner
        exact ⟨rfl, .proxy _⟩
      · rintro ⟨same, _⟩
        have inners := Dynamic.Value.proxy.inj same
        subst rightInner
        have words := (leftAuth.ids_equal_iff rightAuth).mpr rfl
        subst rightWord
        exact ⟨rfl, .word _⟩
    | constructed => constructor <;> rintro ⟨same, _⟩ <;> cases same
  | @constructed leftMetadata leftId leftTag leftSources leftPacked leftAuth leftSelected leftArity leftPacking =>
    cases b with
    | proxy => constructor <;> rintro ⟨same, _⟩ <;> cases same
    | @constructed rightMetadata rightId rightTag rightSources rightPacked rightAuth rightSelected rightArity rightPacking =>
      rw [product_equivalent]
      constructor
      · rintro ⟨⟨ids, _⟩, fields⟩
        have raw := (leftAuth.ids_equal_iff rightAuth).mp (Dynamic.Value.word.inj ids)
        have metadata := SourceCoreRawMetadata.Metadata.constructor.inj raw
        subst rightMetadata
        have fields := (pack_equivalent leftPacking rightPacking (leftArity.trans rightArity.symm)).mp fields
        rcases fields with ⟨rfl, comparable⟩
        exact ⟨rfl, .constructed _ _ comparable⟩
      · rintro ⟨same, comparable⟩
        obtain ⟨metadata, values⟩ := Dynamic.Value.constructed.inj same
        subst rightMetadata
        subst rightSources
        have ids := (leftAuth.ids_equal_iff rightAuth).mpr rfl
        subst rightId
        cases comparable with
        | constructed _ _ fields =>
          exact ⟨⟨rfl, .word _⟩, (pack_equivalent leftPacking rightPacking rfl).mpr ⟨rfl, fields⟩⟩

inductive Carrier (profile : Bool) : Ty → Prop where
  | unit : Carrier profile .unit
  | bool : Carrier profile .bool
  | word : Carrier profile .word
  | integer : Carrier profile .integer
  | product {left right} (a : Carrier profile left) (b : Carrier profile right) : Carrier profile (.product left right)
  | namedData (id : DataTypeId) : Carrier profile (.namedData id)
  | mapping (id : DataTypeId) (value : Ty) : Carrier profile (.product .word (.product (.sum .unit value) (.namedData id)))
  | function (parameter result : Ty) (plain : profile = false) : Carrier profile (TaggedFunction.functionType parameter result)
  | contracted (parameter result : Ty) (marked : profile = true) : Carrier profile (CallableContract.functionType parameter result)

theorem Carrier.not_sum {profile : Bool} {left right : Ty} : ¬ Carrier profile (.sum left right) := by
  intro impossible; cases impossible

theorem Carrier.not_mapping_tail {profile : Bool} {value : Ty} {id : DataTypeId} :
    ¬ Carrier profile (.product (.sum .unit value) (.namedData id)) := by
  intro impossible
  cases impossible with
  | product first => exact first.not_sum

theorem Carrier.not_tagged_contract {parameter result : Ty} :
    ¬ Carrier true (TaggedFunction.functionType parameter result) := by
  intro impossible
  cases impossible with
  | product first => exact first.not_sum
  | function _ _ impossible => cases impossible

theorem Carrier.product_not_mapping {catalog : Catalog} {left right : Ty}
    (second : Carrier catalog.callableContracts right) :
    SourceCoreCompatibleDataEquality.isMappingCarrier catalog (.product left right) = false := by
  cases left <;> try rfl
  cases right <;> try rfl
  rename_i head tail
  cases head <;> try rfl
  rename_i a b
  cases a <;> try rfl
  cases tail <;> try rfl
  exact False.elim second.not_mapping_tail

theorem Carrier.product_contract_shape {profile : Bool} {left right : Ty}
    (first : Carrier profile left) :
    (profile && SourceCoreDataEquality.isCallableContractType (.product left right)) = false := by
  cases profile with
  | false => rfl
  | true =>
    cases first with
    | unit | bool | word | integer | namedData | mapping | contracted => rfl
    | function _ _ impossible => cases impossible
    | product head tail =>
      cases head with
      | unit | bool | word | integer | product | namedData | mapping | contracted => rfl
      | function _ _ impossible => cases impossible

inductive Observation (catalog : Catalog) (registry : Registry) (identities : Dynamic.Value → Word → Prop) :
    Ty → Dynamic.Value → Value → Prop where
  | unit : Observation catalog registry identities .unit .unit .unit
  | bool (value : Bool) : Observation catalog registry identities .bool (.bool value) (.bool value)
  | word (value : Word) : Observation catalog registry identities .word (.word value) (.word value)
  | integer (value : Int) : Observation catalog registry identities .integer (.integer value) (.integer value)
  | product {leftType rightType : Ty} {left right : Dynamic.Value} {a b : Value}
      (first : Observation catalog registry identities leftType left a)
      (second : Observation catalog registry identities rightType right b) :
      Observation catalog registry identities (.product leftType rightType) (.product left right) (.pair a b)
  | mapping (id : DataTypeId) (valueType : Ty)
      (recognized : SourceCoreCompatibleDataEquality.isMappingCarrier catalog
        (.product .word (.product (.sum .unit valueType) (.namedData id))) = true)
      (key value : TypeSystem.Ty) (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
      Observation catalog registry identities (.product .word (.product (.sum .unit valueType) (.namedData id)))
        (.mapping key value entries) carrier
  | identified {source : Dynamic.Value} {identity : Word} (parameter result : Ty) (code : Value)
      (meaning : identities source identity) (profile : catalog.callableContracts = false) :
      Observation catalog registry identities (TaggedFunction.functionType parameter result)
        source (.pair (.inRight .unit (.word identity)) code)
  | anonymous (source : Dynamic.Closure) (parameter result : Ty) (code : Value)
      (profile : catalog.callableContracts = false) :
      Observation catalog registry identities (TaggedFunction.functionType parameter result)
        (.closure source) (.pair (.inLeft .word .unit) code)
  | contractedIdentified {source : Dynamic.Value} {identity : Word} (parameter result : Ty)
      (code : Value) (contract : Word) (meaning : identities source identity)
      (profile : catalog.callableContracts = true) :
      Observation catalog registry identities (CallableContract.functionType parameter result)
        source (.pair (.pair (.inRight .unit (.word identity)) code) (.word contract))
  | contractedAnonymous (source : Dynamic.Closure) (parameter result : Ty)
      (code : Value) (contract : Word) (profile : catalog.callableContracts = true) :
      Observation catalog registry identities (CallableContract.functionType parameter result)
        (.closure source) (.pair (.pair (.inLeft .word .unit) code) (.word contract))
  | data {id : DataTypeId} {index : Nat} {entry : SourceCoreDataCatalog.Entry}
      {source packed : Dynamic.Value} {payloadType : Ty} {payload : Value}
      (selected : catalog.entries[id.index]? = some entry)
      (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
      (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType)
      (meaning : DataMeaning registry catalog ⟨id, index⟩ source packed)
      (representation : Observation catalog registry identities payloadType packed payload) :
      Observation catalog registry identities (.namedData id) source (.constructed ⟨id, index⟩ payload)

theorem Observation.carrier {catalog : Catalog} {registry : Registry}
    {identities : Dynamic.Value → Word → Prop} {type : Ty} {source : Dynamic.Value} {value : Value}
    (observed : Observation catalog registry identities type source value) : Carrier catalog.callableContracts type := by
  induction observed with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .product first second
  | mapping => exact .mapping _ _
  | identified _ _ _ _ profile | anonymous _ _ _ _ profile => exact .function _ _ profile
  | contractedIdentified _ _ _ _ _ profile | contractedAnonymous _ _ _ _ _ profile => exact .contracted _ _ profile
  | data => exact .namedData _

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityGeneration
/-! Static extraction from actual compatible comparator generation, following
finite equality observations. Recursive calls follow the represented payload,
so generated recursive helper references introduce no termination assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality DataEquality DataEqualityGeneration

abbrev ReferencesAt (catalog : Catalog) := DataEqualityCertificates.ReferencesAt (storageCatalog catalog)

theorem data_compareType {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
    {fuel depth : Nat} {left right compiled : Expr}
    (accepted : compareType fuel catalog depth (.namedData id) left right = .ok compiled) :
    compiled = SourceCoreDataEquality.invoke (.var (referenceIndex catalog depth id)) left right := by
  cases fuel with
  | zero => simp [compareType] at accepted
  | succ fuel =>
    cases kind : entry.sourceType <;>
      simp only [compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, selected, kind,
        bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    all_goals first | exact accepted.symm | exact False.elim (notMapping _ _ kind)

theorem data_helperBody {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
    {fuel : Nat} {body : Expr} (accepted : helperBody fuel catalog id = .ok body) :
    ∃ definition, entry.definition = some definition ∧
      nominalBody fuel catalog id definition.constructorPayloadTypes = .ok body := by
  have next : (match entry.definition with
      | some definition => nominalBody fuel catalog id definition.constructorPayloadTypes
      | none => .error (.missingDefinition id)) = .ok body := by
    cases kind : entry.sourceType <;>
      simp only [helperBody, selected, kind, bind, Except.bind, pure, Except.pure] at accepted
    all_goals first | exact accepted | exact False.elim (notMapping _ _ kind)
  cases found : entry.definition with
  | none => simp [found] at next
  | some definition => exact ⟨definition, rfl, by simpa [found] using next⟩

theorem registered_payload {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry) {definition : DataDefinition}
    (definitionSelected : entry.definition = some definition) {index : Nat} {payloadType : Ty}
    (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType) :
    definition.constructorPayloadTypes[index]? = some payloadType := by
  simpa [SourceCoreCompatibleCatalog.Catalog.definitions, DataEnvironment.lookupConstructorPayloadType?,
    DataEnvironment.lookupDataType?, selected, definitionSelected] using registered

theorem tree_of_compareType {catalog : Catalog} {registry : Registry}
    {identities : Dynamic.Value → Word → Prop} {helperFuel : Nat} {bodies : List Expr}
    (generatedHelpers : helperBodies helperFuel catalog = .ok bodies)
    {base : Nat} {ambient : Environment} {store : Store}
    (installed : Installed catalog bodies base ambient store)
    {type : Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation catalog registry identities type sourceLeft leftValue)
    (rightObserved : Observation catalog registry identities type sourceRight rightValue)
    {fuel depth : Nat} {leftExpression rightExpression compiled : Expr}
    (accepted : compareType fuel catalog depth type leftExpression rightExpression = .ok compiled)
    (environment : Environment) (mapping : Renaming)
    (references : ReferencesAt catalog base depth mapping environment)
    (leftSelected : Selects environment (leftExpression.rename mapping) leftValue)
    (rightSelected : Selects environment (rightExpression.rename mapping) rightValue) :
    ∃ result, Tree identities store environment (compiled.rename mapping) sourceLeft sourceRight result := by
  induction leftObserved generalizing sourceRight rightValue fuel depth leftExpression rightExpression compiled environment mapping with
  | unit | bool | word | integer =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases rightObserved
      first | exact ⟨true, .base .unit⟩ | exact ⟨_, .base (.bool leftSelected rightSelected)⟩ |
        exact ⟨_, .base (.word leftSelected rightSelected)⟩ | exact ⟨_, .base (.integer leftSelected rightSelected)⟩
  | @product leftType rightType a b x y first second firstIH secondIH =>
    cases rightObserved with
    | mapping => exact False.elim second.carrier.not_mapping_tail
    | identified => exact False.elim first.carrier.not_sum
    | anonymous => exact False.elim first.carrier.not_sum
    | contractedIdentified _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | contractedAnonymous _ _ _ _ _ profile =>
        exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
    | product otherFirst otherSecond =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        have generated : (show Except Error Expr from do
            let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
            let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
            pure (.ifE left right (.bool false))) = .ok compiled := by
          have carrier := first.carrier
          have noMap := second.carrier.product_not_mapping (left := leftType)
          have shape := Carrier.product_contract_shape (right := rightType) carrier
          cases leftType <;> try cases carrier
          all_goals simpa only [compareType, noMap, shape, Bool.false_eq_true, ↓reduceIte] using accepted
        obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
        obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
        cases generated
        obtain ⟨leftResult, leftTree⟩ := firstIH otherFirst leftCompiled environment mapping references (.first leftSelected) (.first rightSelected)
        obtain ⟨rightResult, rightTree⟩ := secondIH otherSecond rightCompiled environment mapping references (.second leftSelected) (.second rightSelected)
        exact ⟨_, .product leftTree rightTree⟩
  | @mapping id valueType recognized key value entries carrier =>
    cases rightObserved with
    | product _ otherSecond => exact False.elim otherSecond.carrier.not_mapping_tail
    | mapping =>
      cases fuel with
      | zero => simp [compareType] at accepted
      | succ fuel =>
        simp only [compareType, recognized, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
        subst compiled
        exact ⟨false, .base (.mapping _ _ _ _ _ _)⟩
  | @identified source identity parameter result code meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim first.carrier.not_sum
      | identified _ _ _ other _ => exact ⟨_, .base (.identified meaning other leftSelected rightSelected)⟩
      | anonymous source => exact ⟨false, .base (.anonymousRight _ source leftSelected rightSelected)⟩
  | @anonymous source parameter result code profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [TaggedFunction.functionType, TaggedFunction.identityType, LanguageResult.resultType,
        compareType, isMappingCarrier, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim first.carrier.not_sum
      | identified | anonymous => exact ⟨false, .base (.anonymousLeft source _ leftSelected rightSelected)⟩
  | @contractedIdentified source identity parameter result code contract meaning profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isMappingCarrier, SourceCoreDataEquality.isCallableContractType, profile,
        Bool.false_eq_true, Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified _ _ _ _ other _ => exact ⟨_, .base (.identified meaning other (.first leftSelected) (.first rightSelected))⟩
      | contractedAnonymous source => exact ⟨false, .base (.anonymousRight _ source (.first leftSelected) (.first rightSelected))⟩
  | @contractedAnonymous source parameter result code contract profile =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [CallableContract.functionType, TaggedFunction.functionType, TaggedFunction.identityType,
        LanguageResult.resultType, compareType, isMappingCarrier, SourceCoreDataEquality.isCallableContractType, profile,
        Bool.false_eq_true, Bool.true_and, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      rw [functionEqual_rename]
      cases rightObserved with
      | product first => exact False.elim (Carrier.not_tagged_contract (by simpa only [profile] using first.carrier))
      | contractedIdentified | contractedAnonymous => exact ⟨false, .base (.anonymousLeft source _ (.first leftSelected) (.first rightSelected))⟩
  | @data id index entry source packed payloadType payload selected notMapping registered meaning representation ih =>
    rw [data_compareType selected notMapping accepted, invoke_rename]
    cases rightObserved with
    | @data _ otherIndex otherEntry otherSource otherPacked otherPayloadType otherPayload
        otherSelected otherNotMapping otherRegistered otherMeaning otherRepresentation =>
      have entries := Option.some.inj (selected.symm.trans otherSelected)
      subst otherEntry
      have bound : id.index < catalog.entries.length := List.getElem?_eq_some_iff.mp selected |>.1
      obtain ⟨body, bodySelected, generatedBody⟩ := CompatibleEquality.helperBodies_lookup generatedHelpers bound
      obtain ⟨definition, definitionSelected, generatedNominal⟩ := data_helperBody selected notMapping generatedBody
      have leftPayload := CompatibleEquality.registered_payload selected definitionSelected registered
      have rightPayload := CompatibleEquality.registered_payload selected definitionSelected otherRegistered
      obtain ⟨branches, rightBranches, branch, bodyEq, leftBranch, rightBranch, branchGenerated⟩ :=
        CompatibleEquality.nominalBody_branches generatedNominal leftPayload rightPayload
      let captured := DataEqualityInstalled.captured id.index (DataEqualityInstalled.allocatedEnvironment (storageCatalog catalog) base ambient)
      let pair := Value.pair (.constructed ⟨id, index⟩ payload) (.constructed ⟨id, otherIndex⟩ otherPayload)
      let shift := (DataEqualityInstalled.offset id.index).lift
      have helperReferences : ReferencesAt catalog base 3 shift.lift.lift (otherPayload :: payload :: pair :: captured) :=
        (DataEqualityCertificates.installedReferences (storageCatalog catalog) base ambient id.index pair).lift payload |>.lift otherPayload
      have installedBody := installed id.index body bodySelected
      have renamedLeft := renameList_lookup leftBranch shift.lift
      have renamedRight := renameList_lookup rightBranch shift.lift.lift
      by_cases same : index = otherIndex
      · subst otherIndex
        have payloadTypes := Option.some.inj (leftPayload.symm.trans rightPayload)
        subst otherPayloadType
        simp only [↓reduceIte] at branchGenerated
        obtain ⟨result, payloadTree⟩ := ih otherRepresentation branchGenerated _ shift.lift.lift helperReferences
          (.var rfl) (.var rfl)
        refine ⟨result, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ result
        rw [bodyEq]
        apply Tree.dataSame (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft) renamedRight
          (meaning.equivalent otherMeaning) payloadTree
      · have branchEq : branch = .bool false := by simpa [same] using branchGenerated.symm
        have distinct : source ≠ sourceRight := by
          intro sourceSame
          subst sourceRight
          exact same (ConstructorId.mk.inj (meaning.tags_equal otherMeaning)).2
        refine ⟨false, .invoke (.var (references id.index bound)) leftSelected rightSelected installedBody ?_⟩
        change Tree identities store (pair :: captured) (body.rename shift) _ _ false
        rw [bodyEq]
        apply Tree.dataDifferent distinct (.first (.var rfl)) (.second (.var rfl))
          (by simpa [Expr.rename, Expr.weakenAt, shift, Renaming.lift] using renamedLeft)
          (by simpa [branchEq, Expr.rename] using renamedRight)

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityPayload
/-! Equality observations automatically extracted from independent full
compatible payloads. Function models must separately authenticate callable
identities/code shape; data-only models discharge that boundary vacuously. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceInference CompatiblePayload DataPatternValues DataEqualityGeneration

 theorem identity_entry {catalog : Catalog} {type : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? type = some id) :
    ∃ entry, catalog.entries[id.index]? = some entry ∧ entry.sourceType = SourceCoreRawMetadata.runtimeType type := by
  unfold SourceCoreCompatibleCatalog.Catalog.identity? at selected
  cases found : catalog.entries.zipIdx.find? (fun item => decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) with
  | none => simp [found] at selected
  | some item =>
    have member := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
    have same : item.1.sourceType = SourceCoreRawMetadata.runtimeType type := by simpa using List.find?_some found
    simp only [found, Option.map_some, Option.some.injEq] at selected
    subst id
    exact ⟨item.1, member, same⟩

 theorem constructor_identity {catalog : Catalog} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) : catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identity : catalog.identity? metadata.resultType with
  | none => simp [identity] at selected
  | some id =>
    cases row : catalog.entries[id.index]? with
    | none => simp [identity, row] at selected
    | some entry =>
      cases ctor : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identity, row, ctor] at selected
      | some item =>
        simp only [identity, row, ctor, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        rfl

private theorem native_beq_self (type : Ty) : (type == type) = true := by
  induction type <;> simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]

theorem mapping_recognized {catalog : Catalog} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (identity : catalog.identity? (.mapping key value) = some layout.dataType)
    (keyProjection : catalog.project key = .ok layout.keyType)
    (valueProjection : catalog.project value = .ok layout.valueType) :
    SourceCoreCompatibleDataEquality.isMappingCarrier catalog (SourceCoreMappingWithDefault.type layout) = true := by
  obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
  have projection : catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout) := by
    simp only [SourceCoreCompatibleCatalog.Catalog.project, identity, keyProjection, valueProjection,
      bind, Except.bind, pure, Except.pure]
  have entryProjection : catalog.project entry.sourceType = .ok (SourceCoreMappingWithDefault.type layout) := by
    rw [sourceType, SourceCoreCompatibleCatalog.Catalog.project_runtimeType]
    exact projection
  have sourceKind : entry.sourceType = .mapping (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value) := sourceType
  change (match catalog.entries[layout.dataType.index]? with
    | some entry => match entry.sourceType with
      | .mapping _ _ => match catalog.project entry.sourceType with
        | .ok projected => projected == SourceCoreMappingWithDefault.type layout
        | .error _ => false
      | _ => false
    | none => false) = true
  rw [selected]
  simp only [sourceKind] at entryProjection ⊢
  rw [entryProjection]
  exact native_beq_self _

theorem named_project_not_mapping {catalog : Catalog} {source : TypeSystem.Ty} {id : DataTypeId}
    (projected : catalog.project source = .ok (.namedData id)) : ∀ key value, source ≠ .mapping key value := by
  intro key value same
  subst source
  unfold SourceCoreCompatibleCatalog.Catalog.project at projected
  cases identity : catalog.identity? (.mapping key value) <;>
    simp only [identity, bind, Except.bind, pure, Except.pure] at projected
  · cases projected
  · cases keyProjection : catalog.project key <;> simp only [keyProjection] at projected
    · cases projected
    · cases valueProjection : catalog.project value <;> simp only [valueProjection] at projected
      all_goals cases projected

/-- Static function leaf obligations, independent of runtime comparisons. -/
def FunctionObservations (catalog : Catalog) {ambient : AmbientDefinitions catalog.definitions} (functions : FunctionModel catalog ambient)
    (identities : Dynamic.Value → Word → Prop) : Prop :=
  ∀ {registry mapping world sourceType source value type},
    functions.Represents registry mapping world sourceType source value type →
      Observation catalog registry identities type source value

theorem ValueRep.observation {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    Observation checked.catalog registry identities type source value := by
  induction related using ValueRep.rec
    (motive_2 := fun _ sources values types _ => ∃ packed, Dynamic.ValuesPack sources packed ∧
      Observation checked.catalog registry identities (SourceCoreCompatibleCatalog.packTypes types) packed (packValues values))
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second => exact .product first second
  | function related => exact functionLeaves related
  | @proxy inner owner id metadata identity registered =>
    obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
    apply Observation.data selected (fun key value impossible => by rw [sourceType] at impossible; cases impossible)
      registered (.proxy metadata identity) (.word id)
  | @constructed metadata id tag sources values types metadataRep owner selected projected registered payloads ih =>
    obtain ⟨packed, packing, observed⟩ := ih
    obtain ⟨entry, found, sourceType⟩ := identity_entry (constructor_identity selected)
    have projectedEntry : checked.catalog.project entry.sourceType = .ok (.namedData tag.owner) := by
      rw [sourceType, SourceCoreCompatibleCatalog.Catalog.project_runtimeType]
      exact projected
    exact Observation.data found (named_project_not_mapping projectedEntry) registered
      (.constructed metadataRep selected payloads.length.1.symm packing) (.product (.word id) observed)
  | @mappingValue keyType valueType id layout sources entries fallback metadata identity keyProjection valueProjection registered stored defaultValue _ _ =>
    exact .mapping layout.dataType layout.valueType (mapping_recognized identity keyProjection valueProjection)
      keyType valueType sources _
  | compatible _ _ ih => exact ih
  | nil => exact ⟨.unit, .nil, .unit⟩
  | @cons sourceType source value type sourceTypes sources values types head tail first rest =>
    obtain ⟨packed, packing, observed⟩ := rest
    cases tail with
    | nil => exact ⟨source, .singleton source, first⟩
    | cons second remaining => exact ⟨.product source packed, .cons packing, .product first observed⟩
  | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
/-! Actual compatible comparator initialization/application preserves and
reflects independent source equality. All recursive comparison traces are
extracted from generated code plus independent represented values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatiblePayload

def comparison {checked : Checked} (prepared : Prepared checked) (left right : Expr) : Expr :=
  .letE prepared.expression (.apply (.var 0) (.pair (left.weakenAt 0) (right.weakenAt 0)))

theorem installed_append {catalog : Catalog} {bodies : List Expr} {base : Nat}
    {environment : Environment} {store : Store}
    (installed : Installed catalog bodies base environment store) (suffix : Store) :
    Installed catalog bodies base environment (store ++ suffix) :=
  DataEqualityCertificates.installed_append installed suffix

theorem prepared_tree {checked : Checked} (prepared : Prepared checked) {registry : Registry}
    {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog registry identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog registry identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, Tree identities store
      (.pair leftValue rightValue :: DataEqualityInstalled.captured prepared.bodies.length
        (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) initialStore.length environment))
      (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift) sourceLeft sourceRight result := by
  apply tree_of_compareType prepared.bodiesGenerated installed leftObserved rightObserved prepared.bodyGenerated
  · exact DataEqualityCertificates.installedReferences _ _ _ _ _
  · exact .first (.var rfl)
  · exact .second (.var rfl)

/-- Installed compatible helpers supply an ordinary ordered-mapping comparator.
Appending administrative cells does not require reinstalling the helpers. -/
theorem prepared_compares {checked : Checked} (prepared : Prepared checked) {registry : Registry}
    (layout : OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog registry identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog registry identities prepared.type sourceRight rightValue)
    (environment : Environment) (initialStore store : Store)
    (installed : Installed checked.catalog prepared.bodies initialStore.length environment store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      OrderedMapping.Compares layout (preparedClosure prepared environment initialStore.length) leftValue rightValue result store := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment initialStore store installed
  refine ⟨result, tree.meaning faithful, ?_⟩
  exact ⟨_, _, by simp only [preparedClosure, keyType], tree.evaluates⟩

theorem prepared_compare_preserves {checked : Checked} (prepared : Prepared checked) {registry : Registry}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftObserved : Observation checked.catalog registry identities prepared.type sourceLeft leftValue)
    (rightObserved : Observation checked.catalog registry identities prepared.type sourceRight rightValue)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store (comparison prepared leftExpression rightExpression) (.bool result)
        (preparedStore prepared environment store) := by
  obtain ⟨result, tree⟩ := prepared_tree prepared leftObserved rightObserved environment store _
    (prepared_installed prepared environment store)
  refine ⟨result, tree.meaning faithful, .letE (prepared_evaluates_exact prepared environment store) ?_⟩
  exact .apply (.var rfl) (.pair ((leftSelected.weaken _).evaluates _) ((rightSelected.weaken _).evaluates _)) tree.evaluates

/-- Raw aliases may use different original source types while sharing one
native type. Their actual metadata still determines source equality. -/
theorem represented_compare_preserves {checked : Checked} (prepared : Prepared checked) {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {leftType rightType : TypeSystem.Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (left : ValueRep checked registry functions mapping world leftType sourceLeft leftValue prepared.type)
    (right : ValueRep checked registry functions mapping world rightType sourceRight rightValue prepared.type)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store (comparison prepared leftExpression rightExpression) (.bool result)
        (preparedStore prepared environment store) :=
  prepared_compare_preserves prepared faithful (ValueRep.observation functionLeaves left) (ValueRep.observation functionLeaves right)
    environment store leftExpression rightExpression leftSelected rightSelected

theorem represented_compare_run {checked : Checked} (prepared : Prepared checked) {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {leftType rightType : TypeSystem.Ty} {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (left : ValueRep checked registry functions mapping world leftType sourceLeft leftValue prepared.type)
    (right : ValueRep checked registry functions mapping world rightType sourceRight rightValue prepared.type)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial (comparison prepared leftExpression rightExpression) environment store) =
          .done (.bool result) (preparedStore prepared environment store)) ∧
      (∀ fuel actual actualStore,
        runStateful fuel (.initial (comparison prepared leftExpression rightExpression) environment store) = .done actual actualStore →
          actual = .bool result ∧ actualStore = preparedStore prepared environment store) := by
  obtain ⟨result, meaning, evaluated⟩ := represented_compare_preserves prepared faithful functionLeaves left right
    environment store leftExpression rightExpression leftSelected rightSelected
  exact ⟨result, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
/-! Instantiate the ordinary mapping library with the actual prepared source
comparator. Mathematical predicate witnesses occur only inside proofs. Executed
comparisons use the generated Core closure, whose finite evaluations are
derived from represented keys and installed helper cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatibleEquality

abbrev KeyRep {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (registry : SourceCoreRawMetadata.Registry) (identities : Dynamic.Value → Word → Prop) :=
  Observation checked.catalog registry identities prepared.type

def comparator {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Value :=
  .closure (.product prepared.type prepared.type) .bool
    (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
    (DataEqualityInstalled.captured prepared.bodies.length
      (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment))

def comparisonStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) : Store :=
  store ++ DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies

/-- Two equality observations of the same Core values agree on source
equivalence. This follows from the actual comparator's deterministic finite
execution, without assuming injectivity of unobserved mapping contents/code. -/
theorem equivalent_coherent {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {a b c d : Dynamic.Value} {left right : Value}
    (aRep : KeyRep prepared registry identities a left) (bRep : KeyRep prepared registry identities b right)
    (cRep : KeyRep prepared registry identities c left) (dRep : KeyRep prepared registry identities d right) :
    Dynamic.ValueEquivalent a b ↔ Dynamic.ValueEquivalent c d := by
  have installed := CompatibleEquality.prepared_installed prepared [] []
  obtain ⟨first, firstTree⟩ := prepared_tree prepared aRep bRep [] [] _ installed
  obtain ⟨second, secondTree⟩ := prepared_tree prepared cRep dRep [] [] _ installed
  have same := Value.bool.inj (evaluation_deterministic firstTree.evaluates secondTree.evaluates).1
  exact (firstTree.meaning faithful).symm.trans (same ▸ secondTree.meaning faithful)

theorem exists_predicate_correct {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (registry : SourceCoreRawMetadata.Registry) {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) :
    ∃ equal : Core.OrderedMapping.Predicate,
      OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal := by
  classical
  let equal : Core.OrderedMapping.Predicate := fun left right => decide
    (∃ a b, KeyRep prepared registry identities a left ∧ KeyRep prepared registry identities b right ∧
      Dynamic.ValueEquivalent a b)
  refine ⟨equal, ?_⟩
  constructor
  intro sourceKey sourceStored key stored keyRep storedRep
  simp only [equal, decide_eq_true_eq]
  constructor
  · rintro ⟨a, b, aRep, bRep, equivalent⟩
    exact (equivalent_coherent prepared faithful aRep bRep keyRep storedRep).mp equivalent
  · intro equivalent
    exact ⟨_, _, keyRep, storedRep, equivalent⟩

theorem entries_key {keyRel valueRel : OrderedMapping.Relation}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : OrderedMapping.EntriesRel keyRel valueRel sources entries)
    {key value : Value} (member : (key, value) ∈ entries) :
    ∃ sourceKey sourceValue, keyRel sourceKey key ∧ valueRel sourceValue value := by
  induction related with
  | nil => simp at member
  | cons keyRep valueRep tail ih =>
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ⟨_, _, keyRep, valueRep⟩
    · exact ih remaining

theorem comparisons {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (initialStore store : Store)
    (installed : CompatibleEquality.Installed checked.catalog prepared.bodies initialStore.length environment store) :
    Core.OrderedMapping.Comparisons layout (comparator prepared environment initialStore)
      equal key entries store := by
  intro stored value member
  obtain ⟨sourceStored, _, storedRep, _⟩ := entries_key related member
  obtain ⟨result, meaning, compared⟩ := prepared_compares prepared layout keyType faithful keyRep storedRep
    environment initialStore store installed
  have equivalent := correct.equivalent keyRep storedRep
  have same : result = equal key stored := by
    cases result <;> cases generated : equal key stored <;> simp_all
  subst result
  exact compared

def lookupStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.lookupParameter layout.lookupResult (Core.OrderedMapping.lookupBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair key (comparator prepared environment store))) environment

def insertStore {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store)
    (entries : Core.OrderedMapping.Entries) (key value : Value) : Store :=
  Core.OrderedMapping.installedStore (comparisonStore prepared environment store)
    layout.insertParameter layout.type (Core.OrderedMapping.insertBody layout)
    (.pair (Core.OrderedMapping.encode layout entries) (.pair (.pair key value) (comparator prepared environment store))) environment

theorem lookup_evaluates {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression mapping keyExpression)
      (.inRight .word (Core.OrderedMapping.optionValue layout.valueType
        (Core.OrderedMapping.lookupEntries equal key entries)))
      (lookupStore prepared layout environment store entries key) := by
  apply Core.OrderedMapping.lookup_evaluates entries key (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (CompatibleEquality.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (CompatibleEquality.prepared_installed prepared environment store) _

theorem insert_evaluates {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : SourceCoreRawMetadata.Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation}
    {sourceKey : Dynamic.Value} {key value : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression mapping keyExpression valueExpression)
      (.inRight .word (Core.OrderedMapping.encode layout
        (Core.OrderedMapping.insertEntries equal key value entries)))
      (insertStore prepared layout environment store entries key value) := by
  apply Core.OrderedMapping.insert_evaluates entries key value (comparator prepared environment store)
    equal (mappingSelected.evaluates store) (keySelected.evaluates store)
    (valueSelected.evaluates store) (CompatibleEquality.prepared_evaluates_exact prepared environment store)
  apply comparisons prepared layout keyType faithful equal correct keyRep related
  exact installed_append (CompatibleEquality.prepared_installed prepared environment store) _

/-- A helper appends comparator cells followed by exactly one recursive
mapping helper cell. Existing source and administrative cells are unchanged. -/
theorem helper_store_extension {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) (parameter result : Ty) (body : Expr) (input : Value) :
    ∃ administrative,
      Core.OrderedMapping.installedStore (comparisonStore prepared environment store) parameter result body input environment =
        store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  refine ⟨DataEqualityInstalled.cells
    (DataEqualityInstalled.allocatedEnvironment (storageCatalog checked.catalog) store.length environment) prepared.bodies ++
    [.inRight .unit (Core.WordMapping.closure parameter result body
      (comparisonStore prepared environment store).length (input :: environment))], ?_, ?_⟩
  · simp [Core.OrderedMapping.installedStore, Core.WordMapping.installedStore, comparisonStore, List.append_assoc]
  · simp [DataEqualityInstalled.cells, CompatibleEquality.bodies_length prepared.bodiesGenerated]

end Solcore.SourceSemantics.CoreLowering.CompatibleMappingComparison
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingEntries
/-! Ordered source entries keep full compatible payload receipts throughout
lookup and replacement. Equality observations never replace those receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality

abbrev Payload {checked : SourceCoreCompatibleCatalog.Checked} (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) : OrderedMapping.Relation :=
  fun source value => ValueRep checked registry functions mapping world sourceType source value type

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
  {sourceKey sourceValue : TypeSystem.Ty} {keyType valueType : Ty}

 theorem entries_related {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    OrderedMapping.EntriesRel (Payload registry functions mapping world sourceKey keyType)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value tail => exact .cons key value (ih tail)

 theorem entries_of_related {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : OrderedMapping.EntriesRel (Payload registry functions mapping world sourceKey keyType)
      (Payload registry functions mapping world sourceValue valueType) sources entries) :
    EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType := by
  induction related with
  | nil => exact .empty _ _ _ _
  | cons key value tail ih => exact .entry key value ih

 theorem entries_observed (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyProjected : keyType = prepared.type)
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType) :
    OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities)
      (Payload registry functions mapping world sourceValue valueType) sources entries := by
  subst keyType
  induction sources generalizing entries with
  | nil => cases related; exact .nil
  | cons head tail ih => cases related with
    | entry key value tail => exact .cons (CompatibleEquality.ValueRep.observation functionLeaves key) value (ih tail)

 theorem predicate_correct (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    {identities : Dynamic.Value → Word → Prop}
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (keyProjected : keyType = prepared.type) {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal) :
    OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal := by
  subst keyType
  exact ⟨fun a b => correct.equivalent
    (CompatibleEquality.ValueRep.observation functionLeaves a) (CompatibleEquality.ValueRep.observation functionLeaves b)⟩

/-- Classification of real mathematical ordered lookup, independent of any
source evaluator or native helper. -/
inductive Lookup (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) : Option Dynamic.Value → Prop where
  | found {value} (found : Dynamic.MappingLookup key sources value) : Lookup key sources (some value)
  | absent (absent : Dynamic.MappingAbsent key sources) : Lookup key sources none

 theorem lookup_total (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) : ∃ found, Lookup key sources found := by
  classical
  induction sources with
  | nil => exact ⟨none, .absent .nil⟩
  | cons entry rest ih =>
    by_cases same : Dynamic.ValueEquivalent key entry.1
    · exact ⟨some entry.2, .found (.head same)⟩
    · obtain ⟨found, ih⟩ := ih
      cases ih with
      | found found => exact ⟨_, .found (.tail same found)⟩
      | absent absent => exact ⟨_, .absent (.cons same absent)⟩

 theorem insert_total (key value : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value)) :
    ∃ updated, Dynamic.MappingInsert key value sources updated := by
  classical
  induction sources with
  | nil => exact ⟨_, .append .nil⟩
  | cons entry rest ih =>
    by_cases same : Dynamic.ValueEquivalent key entry.1
    · exact ⟨_, .update (.head same)⟩
    · obtain ⟨updated, ih⟩ := ih
      cases ih with
      | update replacement => exact ⟨_, .update (.tail same replacement)⟩
      | append absent => exact ⟨_, .append (.cons same absent)⟩

 theorem lookup_preserves {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal)
    {sourceLookup sourceResult : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : Payload registry functions mapping world sourceKey keyType sourceLookup key)
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType)
    (found : Dynamic.MappingLookup sourceLookup sources sourceResult) :
    ∃ result, Core.OrderedMapping.lookupEntries equal key entries = some result ∧
      Payload registry functions mapping world sourceValue valueType sourceResult result :=
  OrderedMapping.lookup_related correct keyRep (entries_related related) found

 theorem insert_preserves {equal : Core.OrderedMapping.Predicate}
    (correct : OrderedMapping.KeyEqualityCorrect (Payload registry functions mapping world sourceKey keyType) equal)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : Payload registry functions mapping world sourceKey keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue valueType sourceReplacement replacement)
    (related : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries keyType valueType)
    (inserted : Dynamic.MappingInsert sourceLookup sourceReplacement sources updated) :
    EntriesRep checked registry functions mapping world sourceKey sourceValue updated
      (Core.OrderedMapping.insertEntries equal key replacement entries) keyType valueType :=
  entries_of_related (OrderedMapping.insert_related correct keyRep replacementRep (entries_related related) inserted)

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingView
/-! Inversion of a full compatible mapping value. The extracted fields retain
its original key/value types, exact header, ordered entries, and raw default;
the expected source type remains an explicit compatible view. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality

structure Fields (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceKey sourceValue : TypeSystem.Ty) (sources : List (Dynamic.Value × Dynamic.Value))
    (header : Word) (layout : Core.OrderedMapping.Layout) (entries : Core.OrderedMapping.Entries) (fallback : Option Value) : Prop where
  metadata : MetadataRep registry (.mapping sourceKey sourceValue) header
  identity : checked.catalog.identity? (.mapping sourceKey sourceValue) = some layout.dataType
  keyProjection : checked.catalog.project sourceKey = .ok layout.keyType
  valueProjection : checked.catalog.project sourceValue = .ok layout.valueType
  registered : layout.Registered checked.catalog.definitions
  stored : EntriesRep checked registry functions mapping world sourceKey sourceValue sources entries layout.keyType layout.valueType
  default : DefaultRep checked registry functions mapping world sourceValue fallback layout.valueType

 theorem Fields.represents {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {layout : Core.OrderedMapping.Layout} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback) :
    ValueRep checked registry functions mapping world (.mapping sourceKey sourceValue) (.mapping sourceKey sourceValue sources)
      (SourceCoreMappingWithDefault.value header fallback layout entries) (SourceCoreMappingWithDefault.type layout) :=
  .mappingValue fields.metadata fields.identity fields.keyProjection fields.valueProjection fields.registered fields.stored fields.default

 theorem mapping_fields {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {sourceKey sourceValue sources}, source = .mapping sourceKey sourceValue sources →
      ∃ header layout entries fallback,
        value = SourceCoreMappingWithDefault.value header fallback layout entries ∧
        type = SourceCoreMappingWithDefault.type layout ∧
        SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.mapping sourceKey sourceValue) ∧
        Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed => intro _ _ _ impossible; cases impossible
  | function related =>
    intro _ _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | mappingValue metadata identity key value registered stored fallback _ _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, rfl, ⟨metadata, identity, key, value, registered, stored, fallback⟩⟩
  | compatible same related ih =>
    intro _ _ _ source
    obtain ⟨header, layout, entries, fallback, value, type, view, fields⟩ := ih source
    exact ⟨header, layout, entries, fallback, value, type, same.trans view, fields⟩
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers
/-! Full compatible constructor payload selection and replacement. Original
constructor metadata and its raw ID remain unchanged, as do every sibling and
nested mapping/default carrier. No evaluation or comparison premise occurs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend SourceInference GeneralHeap DataPatternValues
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

theorem ValuesRep.at {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type) :
    ∃ source value coreType, Dynamic.ValueAt sources index source ∧ values[index]? = some value ∧
      coreTypes[index]? = some coreType ∧ ValueRep checked registry functions mapping world type source value coreType := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact ⟨_, _, _, .head, rfl, rfl, first⟩
      | succ index =>
        obtain ⟨source, value, type, selected, found, typed, represented⟩ := ih rest lookup
        exact ⟨source, value, type, .tail selected, found, typed, represented⟩

theorem ValuesRep.replace {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} {coreType : Ty} (lookup : types[index]? = some type)
    (coreLookup : coreTypes[index]? = some coreType)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep checked registry functions mapping world type source value coreType) :
    ValuesRep checked registry functions mapping world types (sources.set index source) (values.set index value) coreTypes := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; cases coreLookup; exact .cons replacement rest
      | succ index => exact .cons first (ih rest lookup coreLookup)

theorem ValuesRep.projection {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep checked registry functions mapping world types sources values coreTypes) :
    types.mapM checked.catalog.project = .ok coreTypes := by
  induction types generalizing sources values coreTypes with
  | nil => cases represented; rfl
  | cons head tail ih => cases represented with
    | cons first rest => simp [List.mapM_cons, first.projection, ih rest, bind, Except.bind]

structure ConstructorFields (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (expected : TypeSystem.Ty) (metadata : DataConstructorInstantiation) (tag : ConstructorId) (id : Word)
    (sources : List Dynamic.Value) (values : List Value) (types : List Ty) : Prop where
  metadataRep : MetadataRep registry (.constructor metadata) id
  registryOwner : registry.signatures = checked.signatures
  selected : checked.catalog.constructor? metadata = some tag
  projected : checked.catalog.project metadata.resultType = .ok (.namedData tag.owner)
  registered : checked.catalog.definitions.lookupConstructorPayloadType? tag =
    some (.product .word (SourceCoreCompatibleCatalog.packTypes types))
  payloads : ValuesRep checked registry functions mapping world metadata.payloadTypes sources values types
  view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType metadata.resultType

theorem ConstructorFields.represents {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types) :
    ValueRep checked registry functions mapping world expected (.constructed metadata sources)
      (.constructed tag (.pair (.word id) (packValues values))) (.namedData tag.owner) :=
  .compatible fields.view (.constructed fields.metadataRep fields.registryOwner fields.selected fields.projected fields.registered fields.payloads)

theorem ConstructorFields.resolved {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types) :
    checked.resolveConstructor metadata = .ok tag := by
  have authentic := constructor_authenticated fields.metadataRep fields.registryOwner
  simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, fields.selected, fields.payloads.projection, fields.registered, bind, Except.bind, pure, Except.pure]

theorem ConstructorFields.replace {expected : TypeSystem.Ty} {metadata : DataConstructorInstantiation}
    {tag : ConstructorId} {id : Word} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
    (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
    {index : Nat} {sourceType : TypeSystem.Ty} {type : Ty}
    (sourceAt : metadata.payloadTypes[index]? = some sourceType) (typeAt : types[index]? = some type)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep checked registry functions mapping world sourceType source value type) :
    ConstructorFields checked registry functions mapping world expected metadata tag id (sources.set index source) (values.set index value) types :=
  { fields with payloads := fields.payloads.replace sourceAt typeAt replacement }

theorem constructor_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {metadata sources}, source = .constructed metadata sources →
      ∃ tag id values types,
        value = .constructed tag (.pair (.word id) (packValues values)) ∧ type = .namedData tag.owner ∧
        ConstructorFields checked registry functions mapping world expected metadata tag id sources values types := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | mappingValue => intro _ _ impossible; cases impossible
  | function related =>
    intro _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | constructed metadata owner selected projected registered payloads _ =>
    intro _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, ⟨metadata, owner, selected, projected, registered, payloads, rfl⟩⟩
  | compatible same related ih =>
    intro _ _ source
    obtain ⟨tag, id, values, types, value, type, fields⟩ := ih source
    exact ⟨tag, id, values, types, value, type, { fields with view := same.trans fields.view }⟩
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
/-! Runtime-compatible constructor metadata remains authenticated by its raw
signature reconstruction. These static facts compare normalized payload types
without equating original constructor metadata or raw registry IDs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
open Core Frontend SourceInference TypeSystem CompatiblePayload

/-- A lookup retains the exact source constructor at the returned index. -/
theorem constructor_lookup {catalog : SourceCoreCompatibleCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    ∃ entry, catalog.entries[tag.owner.index]? = some entry ∧
      entry.constructors[tag.index]? = some metadata.constructor := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        have found := List.mem_of_find?_eq_some constructorLookup
        have same : item.1 = metadata.constructor := by simpa using List.find?_some constructorLookup
        have found := List.mk_mem_zipIdx_iff_getElem?.mp found
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        refine ⟨entry, entryLookup, ?_⟩
        simpa [same] using found

theorem constructor_identity {catalog : SourceCoreCompatibleCatalog.Catalog}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (selected : catalog.constructor? metadata = some tag) :
    catalog.identity? metadata.resultType = some tag.owner := by
  unfold SourceCoreCompatibleCatalog.Catalog.constructor? at selected
  cases identityEq : catalog.identity? metadata.resultType with
  | none => simp [identityEq] at selected
  | some identity =>
    cases entryLookup : catalog.entries[identity.index]? with
    | none => simp [identityEq, entryLookup] at selected
    | some entry =>
      cases constructorLookup : entry.constructors.zipIdx.find? (fun item => decide (item.1 = metadata.constructor)) with
      | none => simp [identityEq, entryLookup, constructorLookup] at selected
      | some item =>
        simp only [identityEq, entryLookup, constructorLookup, bind, Option.bind, pure, Option.some.injEq] at selected
        subst tag
        rfl

theorem constructor_eq_of_same_tag {catalog : SourceCoreCompatibleCatalog.Catalog}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftSelected : catalog.constructor? left = some tag)
    (rightSelected : catalog.constructor? right = some tag) : left.constructor = right.constructor := by
  obtain ⟨leftEntry, leftLookup, leftConstructor⟩ := constructor_lookup leftSelected
  obtain ⟨rightEntry, rightLookup, rightConstructor⟩ := constructor_lookup rightSelected
  have entries := leftLookup.symm.trans rightLookup
  cases entries
  exact Option.some.inj (leftConstructor.symm.trans rightConstructor)

theorem constructor_lookup_congr (catalog : SourceCoreCompatibleCatalog.Catalog)
    {left right : DataConstructorInstantiation}
    (constructor : left.constructor = right.constructor)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    catalog.constructor? left = catalog.constructor? right := by
  simp only [SourceCoreCompatibleCatalog.Catalog.constructor?, SourceCoreCompatibleCatalog.Catalog.identity?, constructor, result]

inductive Facts (signatures : ProgramSignatures) (metadata : DataConstructorInstantiation) : Prop where
  | mk (signature : ProgramDataSignature) (constructor : ProgramDataConstructorSignature) (arguments : List TypeSystem.Ty)
      (signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature])
      (constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor])
      (parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters)
      (argumentsSelected : signature.parameters.mapM metadata.parameterSubstitution.lookup? = some arguments)
      (payloads : metadata.payloadTypes = constructor.payloadTypes.map metadata.parameterSubstitution.apply)
      (result : metadata.resultType = TypeSystem.Ty.nominal signature.id arguments) : Facts signatures metadata

 theorem facts {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation}
    (authentic : SourceCoreRawMetadata.constructorAuthentic signatures metadata = true) : Facts signatures metadata := by
  unfold SourceCoreRawMetadata.constructorAuthentic at authentic
  split at authentic <;> try cases authentic
  rename_i signature signatureLookup
  have signatureSelected : signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) = [signature] := by
    change (match signatures.dataTypes.filter (fun item => decide (item.id = metadata.constructor.dataType)) with
      | [one] => some one | _ => none) = some signature at signatureLookup
    split at signatureLookup <;> try cases signatureLookup
    next one selected => exact selected
  split at authentic <;> try cases authentic
  rename_i constructor constructorLookup
  have constructorSelected : signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) = [constructor] := by
    change (match signature.constructors.filter (fun item => decide (item.id = metadata.constructor)) with
      | [one] => some one | _ => none) = some constructor at constructorLookup
    split at constructorLookup <;> try cases constructorLookup
    next one selected => exact selected
  split at authentic <;> try cases authentic
  rename_i parameters
  have parameters : metadata.parameterSubstitution.map Prod.fst = signature.parameters := by simpa using parameters
  split at authentic <;> try cases authentic
  rename_i arguments argumentsSelected
  simp only [Bool.and_eq_true, decide_eq_true_eq] at authentic
  exact .mk signature constructor arguments signatureSelected constructorSelected parameters argumentsSelected authentic.1 authentic.2

 theorem runtimeType_applyMany (head : TypeSystem.Ty) (arguments : List TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.applyMany head arguments) =
      TypeSystem.Ty.applyMany (SourceCoreRawMetadata.runtimeType head) (arguments.map SourceCoreRawMetadata.runtimeType) := by
  induction arguments generalizing head with
  | nil => rfl
  | cons first rest ih => simpa only [TypeSystem.Ty.applyMany, List.foldl_cons, List.map_cons, SourceCoreRawMetadata.runtimeType] using ih (.application head first)

 theorem runtimeType_nominal (declaration : Resolved.DeclarationId) (arguments : List TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (TypeSystem.Ty.nominal declaration arguments) =
      TypeSystem.Ty.nominal declaration (arguments.map SourceCoreRawMetadata.runtimeType) := runtimeType_applyMany _ _

private theorem lookup_none (substitution : ParameterSubstitution) (parameter : TypeParameterId)
    (missing : parameter ∉ substitution.map Prod.fst) : substitution.lookup? parameter = none := by
  induction substitution with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨other, type⟩ := head
    simp only [List.map_cons, List.mem_cons, not_or] at missing
    simp only [ParameterSubstitution.lookup?, if_neg (Ne.symm missing.1)]
    exact ih missing.2

private theorem mapped_lookup_congr (left right : ParameterSubstitution)
    {parameters : List TypeParameterId} {a b : List TypeSystem.Ty}
    (first : parameters.mapM left.lookup? = some a) (second : parameters.mapM right.lookup? = some b)
    (same : a.map SourceCoreRawMetadata.runtimeType = b.map SourceCoreRawMetadata.runtimeType) :
    ∀ parameter ∈ parameters, (left.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.lookup? parameter).map SourceCoreRawMetadata.runtimeType := by
  induction parameters generalizing a b with
  | nil => simp
  | cons head tail ih =>
    rw [List.mapM_cons] at first second
    obtain ⟨leftType, leftFound, first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨leftTypes, leftTail, first⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨rightType, rightFound, second⟩ := Option.bind_eq_some_iff.mp second
    obtain ⟨rightTypes, rightTail, second⟩ := Option.bind_eq_some_iff.mp second
    cases first
    cases second
    simp only [List.map_cons, List.cons.injEq] at same
    intro parameter member
    rcases List.mem_cons.mp member with rfl | member
    · simpa only [leftFound, rightFound, Option.map_some] using congrArg some same.1
    · exact ih leftTail rightTail same.2 parameter member

 theorem substitution_apply_congr (left right : ParameterSubstitution)
    (lookups : ∀ parameter, (left.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.lookup? parameter).map SourceCoreRawMetadata.runtimeType) (type : TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType (left.apply type) = SourceCoreRawMetadata.runtimeType (right.apply type) := by
  induction type with
  | parameter parameter =>
    have same := lookups parameter
    cases first : left.lookup? parameter <;> cases second : right.lookup? parameter <;>
      simp_all [ParameterSubstitution.apply, SourceCoreRawMetadata.runtimeType]
  | _ => simp_all [ParameterSubstitution.apply, SourceCoreRawMetadata.runtimeType]

 theorem payloads_runtimeType {signatures : ProgramSignatures} {left right : DataConstructorInstantiation}
    (first : SourceCoreRawMetadata.constructorAuthentic signatures left = true)
    (second : SourceCoreRawMetadata.constructorAuthentic signatures right = true)
    (constructor : left.constructor = right.constructor)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    left.payloadTypes.map SourceCoreRawMetadata.runtimeType = right.payloadTypes.map SourceCoreRawMetadata.runtimeType := by
  obtain ⟨leftSignature, leftConstructor, leftArguments, leftData, leftCtor, leftKeys, leftMapped, leftPayloads, leftResult⟩ := facts first
  obtain ⟨rightSignature, rightConstructor, rightArguments, rightData, rightCtor, rightKeys, rightMapped, rightPayloads, rightResult⟩ := facts second
  rw [constructor] at leftData leftCtor
  have sameSignature := (List.cons.inj (leftData.symm.trans rightData)).1
  subst rightSignature
  have sameConstructor := (List.cons.inj (leftCtor.symm.trans rightCtor)).1
  subst rightConstructor
  rw [leftResult, rightResult, runtimeType_nominal, runtimeType_nominal] at result
  have sameArguments : leftArguments.map SourceCoreRawMetadata.runtimeType = rightArguments.map SourceCoreRawMetadata.runtimeType := by
    have same := congrArg SourceCoreDataCatalog.nominalParts result
    simpa only [DataPatternAuthenticity.nominalParts_nominal, Option.some.injEq, Prod.mk.injEq, true_and] using same
  have lookups : ∀ parameter, (left.parameterSubstitution.lookup? parameter).map SourceCoreRawMetadata.runtimeType =
      (right.parameterSubstitution.lookup? parameter).map SourceCoreRawMetadata.runtimeType := by
    intro parameter
    by_cases member : parameter ∈ leftSignature.parameters
    · exact mapped_lookup_congr _ _ leftMapped rightMapped sameArguments parameter member
    · rw [lookup_none _ _ (by simpa only [leftKeys] using member), lookup_none _ _ (by simpa only [rightKeys] using member)]
  rw [leftPayloads, rightPayloads, List.map_map, List.map_map]
  apply List.map_congr_left
  intro type _
  exact substitution_apply_congr _ _ lookups type

/-- Native projection erases staging; the authenticated raw metadata does not. -/
theorem projectList_runtimeType (catalog : SourceCoreCompatibleCatalog.Catalog) (types : List TypeSystem.Ty) :
    (types.map SourceCoreRawMetadata.runtimeType).mapM catalog.project = types.mapM catalog.project := by
  induction types with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.mapM_cons, catalog.project_runtimeType, ih]

theorem resolved_facts {checked : SourceCoreCompatibleCatalog.Checked}
    {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : checked.resolveConstructor metadata = .ok tag) :
    SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true ∧
      checked.catalog.constructor? metadata = some tag := by
  by_cases authentic : SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true
  · simp only [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, ↓reduceIte,
      bind, Except.bind, pure, Except.pure] at accepted
    cases selected : checked.catalog.constructor? metadata with
    | none => simp [selected, throw] at accepted
    | some selectedTag =>
      simp only [selected] at accepted
      cases payloads : metadata.payloadTypes.mapM checked.catalog.project with
      | error error => simp [payloads] at accepted
      | ok payloadTypes =>
        simp only [payloads] at accepted
        split at accepted
        · cases accepted; exact ⟨authentic, rfl⟩
        · cases accepted
  · simp [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, throw, bind, Except.bind] at accepted

/-- Equal normalized result types and equal authenticated tags determine the
projected payload list, while retaining distinct raw IDs and source metadata. -/
theorem resolved_payloads_project {checked : SourceCoreCompatibleCatalog.Checked}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (first : checked.resolveConstructor left = .ok tag)
    (second : checked.resolveConstructor right = .ok tag)
    (result : SourceCoreRawMetadata.runtimeType left.resultType = SourceCoreRawMetadata.runtimeType right.resultType) :
    left.payloadTypes.mapM checked.catalog.project = right.payloadTypes.mapM checked.catalog.project := by
  obtain ⟨leftAuthentic, leftSelected⟩ := resolved_facts first
  obtain ⟨rightAuthentic, rightSelected⟩ := resolved_facts second
  have same := payloads_runtimeType leftAuthentic rightAuthentic
    (constructor_eq_of_same_tag leftSelected rightSelected) result
  calc
    _ = (left.payloadTypes.map SourceCoreRawMetadata.runtimeType).mapM checked.catalog.project := (projectList_runtimeType _ _).symm
    _ = (right.payloadTypes.map SourceCoreRawMetadata.runtimeType).mapM checked.catalog.project := congrArg (List.mapM checked.catalog.project) same
    _ = _ := projectList_runtimeType _ _

end Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingExecution
/-! Finite evaluation of the actual metadata/default transport wrappers.
Every comparison comes from the real compatible initializer; wrapper children
are value selections. Exact helper allocations remain in the final store. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatibleEquality
namespace Transport
abbrev carrier := SourceCoreMappingWithDefault.value

def lookupStore {checked : Checked} (prepared : Prepared checked) (layout : Core.OrderedMapping.Layout)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key : Value) : Store :=
  CompatibleMappingComparison.lookupStore prepared layout (carrier header fallback layout entries :: environment) store entries key

def insertStore {checked : Checked} (prepared : Prepared checked) (layout : Core.OrderedMapping.Layout)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key replacement : Value) : Store :=
  CompatibleMappingComparison.insertStore prepared layout (carrier header fallback layout entries :: environment) store entries key replacement

 theorem expression_weaken {checked : Checked} (prepared : Prepared checked) :
    prepared.expression.weakenAt 0 = prepared.expression := by
  rw [← Expr.rename_insertion]
  exact CoreProof.closed_rename prepared.typed _

 theorem lookup_evaluates {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : CompatibleMappingComparison.KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (missingBase header : Word) (fallback : Option Value) (mapping keyExpression : Expr)
    (mappingSelected : Selects environment mapping (carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mapping keyExpression)
      (SourceCoreMappingWithDefault.selectedValue layout.valueType missingBase header fallback (Core.OrderedMapping.lookupEntries equal key entries))
      (lookupStore prepared layout environment store header fallback entries key) := by
  apply SourceCoreMappingWithDefault.lookup_completed (mappingSelected.evaluates store)
  rw [expression_weaken]
  exact CompatibleMappingComparison.lookup_evaluates prepared layout keyType faithful equal correct keyRep related
    (carrier header fallback layout entries :: environment) store _ _
    (.second (.second (.var rfl))) (keySelected.weaken _)

 theorem insert_evaluates {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {registry : Registry} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (equal : Core.OrderedMapping.Predicate)
    (correct : OrderedMapping.KeyEqualityCorrect (CompatibleMappingComparison.KeyRep prepared registry identities) equal)
    {valueRel : OrderedMapping.Relation} {sourceKey : Dynamic.Value} {key replacement : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : CompatibleMappingComparison.KeyRep prepared registry identities sourceKey key)
    (related : OrderedMapping.EntriesRel (CompatibleMappingComparison.KeyRep prepared registry identities) valueRel sources entries)
    (environment : Environment) (store : Store) (header : Word) (fallback : Option Value) (mapping keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mapping (carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    Evaluates environment store (SourceCoreMappingWithDefault.insert layout prepared.expression mapping keyExpression valueExpression)
      (.inRight .word (carrier header fallback layout (Core.OrderedMapping.insertEntries equal key replacement entries)))
      (insertStore prepared layout environment store header fallback entries key replacement) := by
  apply SourceCoreMappingWithDefault.insert_completed (mappingSelected.evaluates store)
  rw [expression_weaken]
  exact CompatibleMappingComparison.insert_evaluates prepared layout keyType faithful equal correct keyRep related
    (carrier header fallback layout entries :: environment) store _ _ _
    (.second (.second (.var rfl))) (keySelected.weaken _) (valueSelected.weaken _)

 theorem lookupStore_extension {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key : Value) :
    ∃ administrative, lookupStore prepared layout environment store header fallback entries key = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  CompatibleMappingComparison.helper_store_extension prepared _ _ _ _ _ _

 theorem insertStore_extension {checked : Checked} (prepared : Prepared checked)
    (layout : Core.OrderedMapping.Layout) (environment : Environment) (store : Store) (header : Word) (fallback : Option Value)
    (entries : Core.OrderedMapping.Entries) (key replacement : Value) :
    ∃ administrative, insertStore prepared layout environment store header fallback entries key replacement = store ++ administrative ∧
      administrative.length = checked.catalog.entries.length + 1 :=
  CompatibleMappingComparison.helper_store_extension prepared _ _ _ _ _ _

end Transport
end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMeaning
/-! Source meaning of actual compatible mapping wrappers. Lookup selects the
first equivalent entry, then the original raw value type's transported default,
then an exact header-specific missing token. Insertion retains full payload
receipts and ordered duplicates. This value-level library has no key-type guard. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality DataEquality

inductive ReadResult (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceValue : TypeSystem.Ty) (key : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value))
    (valueType : Ty) (missingBase header : Word) : Value → Prop where
  | found {source value}
      (lookup : Dynamic.MappingLookup key sources source)
      (represented : Payload registry functions mapping world sourceValue valueType source value) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)
  | default {source value}
      (absent : Dynamic.MappingAbsent key sources) (defaulted : Dynamic.DefaultValue sourceValue source)
      (represented : Payload registry functions mapping world sourceValue valueType source value) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)
  | missing (absent : Dynamic.MappingAbsent key sources) (missing : ¬ Dynamic.Defaultable sourceValue) :
      ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header
        (.inLeft valueType (.word (missingBase.add header)))

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
  {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
  {header : Word} {layout : Core.OrderedMapping.Layout} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}

 theorem ReadResult.success {key : Dynamic.Value} {valueType : Ty} {missingBase header : Word} {value : Value}
    (result : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value)) :
    ∃ source, Dynamic.ProjectionsRead (some (.mapping sourceKey sourceValue sources)) [.index key] (some source) ∧
      Payload registry functions mapping world sourceValue valueType source value := by
  cases result with
  | found found represented => exact ⟨_, .indexFound found .nil, represented⟩
  | default absent defaulted represented => exact ⟨_, .indexDefault absent defaulted .nil, represented⟩

/-- Source runtime compatibility is supplied separately. Native projection alone
cannot establish the metadata-derived key guard for runtime-compatible aliases. -/
 theorem ReadResult.failure {key : Dynamic.Value} {valueType : Ty} {missingBase header token : Word}
    (result : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inLeft valueType (.word token)))
    (keyTyped : Dynamic.ValueRuntimeTypeMatches key sourceKey) :
    token = missingBase.add header ∧ Dynamic.ProjectionsFaults (some (.mapping sourceKey sourceValue sources))
      [.index key] (.missingMappingDefault sourceValue) := by
  cases result with
  | missing absent missing => exact ⟨rfl, .indexDefaultUnavailable keyTyped absent missing⟩

 theorem lookup_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      Evaluates environment store (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) result
        (Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect := predicate_correct prepared functionLeaves keyType (sourceKey := sourceKey) (mapping := mapping) (world := world) correct
  have observedKey : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    have observed := CompatibleEquality.ValueRep.observation functionLeaves keyRep
    simpa only [keyType] using observed
  have evaluated := Transport.lookup_evaluates prepared layout keyType faithful equal correct observedKey
    (entries_observed prepared functionLeaves keyType fields.stored) environment store missingBase header fallback
    mappingExpression keyExpression mappingSelected keySelected
  obtain ⟨found, sourceLookup⟩ := lookup_total sourceLookup sources
  cases sourceLookup with
  | found found =>
    obtain ⟨value, located, represented⟩ := lookup_preserves fullCorrect keyRep fields.stored found
    exact ⟨_, .found found represented, by simpa only [located, SourceCoreMappingWithDefault.selectedValue, Option.or] using evaluated⟩
  | absent absent =>
    have missing := OrderedMapping.absent_related fullCorrect keyRep (entries_related fields.stored) absent
    rw [missing] at evaluated
    cases fields.default with
    | absent noDefault projected wf =>
      exact ⟨_, .missing absent noDefault, evaluated⟩
    | present defaulted represented =>
      exact ⟨_, .default absent defaulted represented, evaluated⟩

 theorem lookup_run (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (missingBase : Word) (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) environment store) =
          .done result (Transport.lookupStore prepared layout environment store header fallback entries key)) ∧
      (∀ fuel actual actualStore, runStateful fuel
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase prepared.expression mappingExpression keyExpression) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = Transport.lookupStore prepared layout environment store header fallback entries key) := by
  obtain ⟨result, meaning, evaluated⟩ := lookup_meaning prepared keyType faithful functionLeaves fields keyRep environment store missingBase
    mappingExpression keyExpression mappingSelected keySelected
  exact ⟨result, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

 theorem insert_meaning (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (mappingExpression keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    ∃ updated nativeEntries,
      Dynamic.MappingInsert sourceLookup sourceReplacement sources updated ∧
      Fields checked registry functions mapping world sourceKey sourceValue updated header layout nativeEntries fallback ∧
      Evaluates environment store (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression)
        (.inRight .word (Transport.carrier header fallback layout nativeEntries))
        (Transport.insertStore prepared layout environment store header fallback entries key replacement) := by
  obtain ⟨equal, correct⟩ := CompatibleMappingComparison.exists_predicate_correct prepared registry faithful
  have fullCorrect := predicate_correct prepared functionLeaves keyType (sourceKey := sourceKey) (mapping := mapping) (world := world) correct
  have observedKey : CompatibleMappingComparison.KeyRep prepared registry identities sourceLookup key := by
    have observed := CompatibleEquality.ValueRep.observation functionLeaves keyRep
    simpa only [keyType] using observed
  obtain ⟨updated, inserted⟩ := insert_total sourceLookup sourceReplacement sources
  have updatedRep := insert_preserves fullCorrect keyRep replacementRep fields.stored inserted
  refine ⟨updated, _, inserted,
    ⟨fields.metadata, fields.identity, fields.keyProjection, fields.valueProjection, fields.registered, updatedRep, fields.default⟩, ?_⟩
  exact Transport.insert_evaluates prepared layout keyType faithful equal correct observedKey
    (entries_observed prepared functionLeaves keyType fields.stored) environment store header fallback
    mappingExpression keyExpression valueExpression mappingSelected keySelected valueSelected

 theorem insert_run (prepared : SourceCoreCompatibleDataEquality.Prepared checked)
    (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (mappingExpression keyExpression valueExpression : Expr)
    (mappingSelected : Selects environment mappingExpression (Transport.carrier header fallback layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression replacement) :
    ∃ updated nativeEntries,
      Dynamic.MappingInsert sourceLookup sourceReplacement sources updated ∧
      Fields checked registry functions mapping world sourceKey sourceValue updated header layout nativeEntries fallback ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression) environment store) =
          .done (.inRight .word (Transport.carrier header fallback layout nativeEntries))
            (Transport.insertStore prepared layout environment store header fallback entries key replacement)) ∧
      (∀ fuel actual actualStore, runStateful fuel
        (.initial (SourceCoreMappingWithDefault.insert layout prepared.expression mappingExpression keyExpression valueExpression) environment store) = .done actual actualStore →
          actual = .inRight .word (Transport.carrier header fallback layout nativeEntries) ∧
          actualStore = Transport.insertStore prepared layout environment store header fallback entries key replacement) := by
  obtain ⟨updated, nativeEntries, inserted, fields, evaluated⟩ := insert_meaning prepared keyType faithful functionLeaves fields keyRep replacementRep
    environment store mappingExpression keyExpression valueExpression mappingSelected keySelected valueSelected
  exact ⟨updated, nativeEntries, inserted, fields, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaces
/-! Single generated compatible index paths. These are the production
select/update/getter/setter expressions. Their static step/comparator receipts
are separate from whole source-expression typing and evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

structure Index (checked : SourceCoreCompatibleCatalog.Checked) (index : PreparedIndex) where
  comparison : SourceCoreCompatibleDataEquality.Prepared checked
  expression : index.comparison = comparison.expression
  keyType : index.layout.keyType = comparison.type

def liftedRead (resultType : Ty) (result : Value) : Value :=
  match result with
  | .inRight .word value => .inRight .word (.inRight .unit value)
  | .inLeft _ reason => .inLeft resultType reason
  | _ => result

 theorem selectedIndex_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      Evaluates environment store (selectedIndex prepared index current keys) result
        (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key) := by
  simpa only [selectedIndex, certificate.expression] using
    lookup_meaning certificate.comparison certificate.keyType faithful functionLeaves fields keyRep
      environment store index.missing current _ mappingSelected keySelected

 theorem selectOne_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (current keys : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key) :
    ∃ result, ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      Evaluates environment store (select prepared [.index index] current keys) (liftedRead prepared.optionalLeaf result)
        (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key) := by
  obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
    environment store current keys mappingSelected keySelected
  refine ⟨result, meaning, ?_⟩
  cases meaning with
  | found | default => exact LanguageResult.bind_success _ evaluated (.inRight (.inRight (.var rfl)))
  | missing => exact LanguageResult.bind_failure _ evaluated

 theorem normalizeRoot_initialized (prepared : Prepared) {environment : Environment} {optional : Expr} {value : Value}
    (selected : Selects environment optional (.inRight .unit value)) (store : Store) :
    Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit value) store := by
  unfold normalizeRoot
  cases prepared.route.rootMapping with
  | none => exact selected.evaluates store
  | some empty => exact .caseRight (selected.evaluates store) (.inRight (.var rfl))

 theorem getter_initialized {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (packValues keys))) :
    ∃ result finalStore administrative,
      ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (liftedRead prepared.optionalLeaf result) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  let stored := Transport.carrier header fallback index.layout entries
  let input := Value.pair (.inRight .unit stored) (packValues keys)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨result, meaning, evaluated⟩ := selectOne_meaning certificate prepared faithful functionLeaves fields keyRep
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) selectedKey
  obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    bodyEnvironment store header fallback entries key
  refine ⟨result, _, administrative, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  exact .caseRight (normalizeRoot_initialized prepared (.first (.var rfl)) store) evaluated

theorem projectPacked_weaken (types : List Ty) (index : Nat) (expression : Expr) :
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

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingUpdates
/-! Actual compatible updater/setter composition. Selection happens before
insertion, so a missing raw default prevents even a constant replacement.
No generated child execution is assumed by the whole-step theorems. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive UpdateResult (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (sourceKey sourceValue : TypeSystem.Ty) (key replacement : Dynamic.Value) (sources : List (Dynamic.Value × Dynamic.Value))
    (header : Word) (layout : Core.OrderedMapping.Layout) (fallback : Option Value) (missingBase : Word) : Value → Nat → Prop where
  | updated {sources' entries}
      (inserted : Dynamic.MappingInsert key replacement sources sources')
      (updated : Dynamic.ProjectionsUpdate (fun _ value => value = replacement)
        (some (.mapping sourceKey sourceValue sources)) [.index key] (.mapping sourceKey sourceValue sources'))
      (represented : Fields checked registry functions mapping world sourceKey sourceValue sources' header layout entries fallback) :
      UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources header layout fallback missingBase
        (.inRight .word (Transport.carrier header fallback layout entries)) (2 * (checked.catalog.entries.length + 1))
  | missing (absent : Dynamic.MappingAbsent key sources) (missing : ¬ Dynamic.Defaultable sourceValue) :
      UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources header layout fallback missingBase
        (.inLeft (SourceCoreMappingWithDefault.type layout) (.word (missingBase.add header))) (checked.catalog.entries.length + 1)

 theorem ReadResult.update {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {key replacement : Dynamic.Value} {sources sources' : List (Dynamic.Value × Dynamic.Value)}
    {valueType : Ty} {missingBase header : Word} {value : Value}
    (read : ReadResult checked registry functions mapping world sourceValue key sources valueType missingBase header (.inRight .word value))
    (inserted : Dynamic.MappingInsert key replacement sources sources') :
    Dynamic.ProjectionsUpdate (fun _ value => value = replacement) (some (.mapping sourceKey sourceValue sources))
      [.index key] (.mapping sourceKey sourceValue sources') := by
  cases read with
  | found found => exact .indexFound found (.leaf rfl) inserted
  | default absent defaulted => exact .indexDefault absent defaulted (.leaf rfl) inserted

private theorem update_after_read {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement selected : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (read : ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header (.inRight .word selected))
    (environment : Environment) (store : Store) (current keys valueExpression : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (valueSelected : Selects environment valueExpression replacement)
    (selection : Evaluates environment store (selectedIndex prepared index current keys) (.inRight .word selected)
      (Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key)) :
    ∃ result finalStore administrative,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result
        (2 * (checked.catalog.entries.length + 1)) ∧
      Evaluates environment store (update prepared [.index index] (SourceCoreMappingWithDefault.type index.layout) current keys valueExpression) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * (checked.catalog.entries.length + 1) := by
  let middle := Transport.lookupStore certificate.comparison index.layout environment store header fallback entries key
  let later := replacement :: selected :: environment
  have shiftedKey : Selects later
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) key := by
    simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken selected).weaken replacement
  obtain ⟨updated, nativeEntries, inserted, represented, evaluated⟩ := insert_meaning certificate.comparison certificate.keyType faithful functionLeaves
    fields keyRep replacementRep later middle (shift 2 current)
    (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) (.var 0)
    (by simpa [shift, List.range_succ] using (mappingSelected.weaken selected).weaken replacement) shiftedKey (.var rfl)
  obtain ⟨firstCells, firstAppended, firstLength⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    environment store header fallback entries key
  obtain ⟨lastCells, lastAppended, lastLength⟩ := Transport.insertStore_extension certificate.comparison index.layout
    later middle header fallback entries key replacement
  refine ⟨_, Transport.insertStore certificate.comparison index.layout later middle header fallback entries key replacement, firstCells ++ lastCells, .updated inserted (read.update inserted) represented, ?_, ?_, ?_⟩
  · apply LanguageResult.bind_success _ selection
    apply LanguageResult.bind_success _ (.inRight (by simpa [shift, List.range_succ] using (valueSelected.weaken selected).evaluates middle))
    simpa only [certificate.expression] using evaluated
  · rw [lastAppended, show middle = store ++ firstCells from firstAppended, List.append_assoc]
  · simp only [List.length_append, firstLength, lastLength]; omega

 theorem updateOne_meaning {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (current keys valueExpression : Expr)
    (mappingSelected : Selects environment current (Transport.carrier header fallback index.layout entries))
    (keySelected : Selects environment (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys) key)
    (valueSelected : Selects environment valueExpression replacement) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      Evaluates environment store (update prepared [.index index] (SourceCoreMappingWithDefault.type index.layout) current keys valueExpression) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
    environment store current keys mappingSelected keySelected
  cases meaning with
  | found found represented =>
    obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ := update_after_read certificate prepared faithful functionLeaves fields
      keyRep replacementRep (.found found represented) environment store current keys valueExpression mappingSelected keySelected valueSelected evaluated
    exact ⟨result, finalStore, administrative, _, meaning, evaluated, appended, length⟩
  | default absent defaulted represented =>
    obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ := update_after_read certificate prepared faithful functionLeaves fields
      keyRep replacementRep (.default absent defaulted represented) environment store current keys valueExpression mappingSelected keySelected valueSelected evaluated
    exact ⟨result, finalStore, administrative, _, meaning, evaluated, appended, length⟩
  | missing absent missing =>
    obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    exact ⟨_, _, administrative, _, .missing absent missing, LanguageResult.bind_failure _ evaluated, appended, length⟩

 theorem setter_initialized {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (.pair (packValues keys) replacement))) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let stored := Transport.carrier header fallback index.layout entries
  let input := Value.pair (.inRight .unit stored) (.pair (packValues keys) replacement)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ := updateOne_meaning certificate prepared faithful functionLeaves
    fields keyRep replacementRep bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) selectedKey (.second (.second (.var rfl)))
  refine ⟨result, finalStore, administrative, count, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps, rootType]
  exact .caseRight (normalizeRoot_initialized prepared (.first (.var rfl)) store) evaluated

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingPlaceRuns
/-! The actual generated getter/setter always finish with enough fuel and all
completed runs agree with their independent source result. The scope is an
initialized root and one index; source-expression and raw key guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

/-- The standalone helper does not check the raw source key type. With that
independent receipt, its missing-default outcome is exactly the source fault. -/
theorem UpdateResult.failure {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {sourceKey sourceValue : TypeSystem.Ty} {key replacement : Dynamic.Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {header missing token : Word}
    {layout : Core.OrderedMapping.Layout} {fallback : Option Value} {count : Nat}
    (result : UpdateResult checked registry functions mapping world sourceKey sourceValue key replacement sources
      header layout fallback missing (.inLeft (SourceCoreMappingWithDefault.type layout) (.word token)) count)
    (keyTyped : Dynamic.ValueRuntimeTypeMatches key sourceKey) :
    token = missing.add header ∧ count = checked.catalog.entries.length + 1 ∧
      Dynamic.ProjectionsFaults (some (.mapping sourceKey sourceValue sources)) [.index key]
        (.missingMappingDefault sourceValue) := by
  cases result with
  | missing absent unavailable => exact ⟨rfl, rfl, .indexDefaultUnavailable keyTyped absent unavailable⟩

 theorem getter_initialized_run {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (packValues keys))) :
    ∃ result finalStore administrative,
      ReadResult checked registry functions mapping world sourceValue sourceLookup sources index.layout.valueType index.missing header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done (liftedRead prepared.optionalLeaf result) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = liftedRead prepared.optionalLeaf result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = checked.catalog.entries.length + 1 := by
  obtain ⟨result, finalStore, administrative, meaning, evaluated, appended, length⟩ :=
    getter_initialized certificate prepared steps faithful functionLeaves fields keyRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨result, finalStore, administrative, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

 theorem setter_initialized_run {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : Index checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {registry : Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities)
    {sourceKey sourceValue : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {header : Word} {entries : Core.OrderedMapping.Entries} {fallback : Option Value}
    (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument
      (.pair (.inRight .unit (Transport.carrier header fallback index.layout entries)) (.pair (packValues keys) replacement))) :
    ∃ result finalStore administrative count,
      UpdateResult checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement sources header index.layout fallback index.missing result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ :=
    setter_initialized certificate prepared steps rootType faithful functionLeaves fields keyRep replacementRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨result, finalStore, administrative, count, meaning, evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedPaths
/-! Structural certificates for the actual compatible mixed selector. Each
node retains complete payload authentication. Mapping tails consume the actual
lookup/default payload relation; no child runtime evaluation is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive Selected (key : Dynamic.Value) (entries : List (Dynamic.Value × Dynamic.Value))
    (type : TypeSystem.Ty) : Dynamic.Value → Prop where
  | found {value} : Dynamic.MappingLookup key entries value → Selected key entries type value
  | default {value} : Dynamic.MappingAbsent key entries → Dynamic.DefaultValue type value → Selected key entries type value

theorem Selected.payload {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {key source : Dynamic.Value} {entries : List (Dynamic.Value × Dynamic.Value)} {type : TypeSystem.Ty}
    (selected : Selected key entries type source) {nativeType : Ty} {missing header : Word} {result : Value}
    (meaning : ReadResult checked registry functions mapping world type key entries nativeType missing header result) :
    ∃ value, result = .inRight .word value ∧ Payload registry functions mapping world type nativeType source value := by
  cases selected with
  | found found => cases meaning with
    | found other represented => exact ⟨_, rfl, found.functional other ▸ represented⟩
    | default absent _ _ => exact (absent.excludes_lookup found).elim
    | missing absent _ => exact (absent.excludes_lookup found).elim
  | default absent defaulted => cases meaning with
    | found found _ => exact (absent.excludes_lookup found).elim
    | default _ other represented => exact ⟨_, rfl, defaulted.functional other ▸ represented⟩
    | missing _ unavailable => exact (unavailable defaulted.defaultable).elim

inductive ReadTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) (leafType : TypeSystem.Ty) (leafCore : Ty) :
    TypeSystem.Ty → Dynamic.Value → Value → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {source value} (related : ValueRep checked registry functions mapping world leafType source value leafCore) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore leafType source value [] [] source 0
  | compatible {expected actual source value steps projections leaf count}
      (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
      (tail : ReadTree checked registry functions mapping world prepared keys leafType leafCore actual source value steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore expected source value steps projections leaf count
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild steps projections leaf count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag) (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : ReadTree checked registry functions mapping world prepared keys leafType leafCore childType sourceChild valueChild steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore expected
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values)))
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child steps projections leaf count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceValue child value steps projections leaf count) :
      ReadTree checked registry functions mapping world prepared keys leafType leafCore (.mapping sourceKey sourceValue)
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries)
        (.index index :: steps) (.index lookup :: projections) leaf (checked.catalog.entries.length + 1 + count)

theorem ReadTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {leafType sourceType : TypeSystem.Ty} {leafCore : Ty}
    {source leaf : Dynamic.Value} {value : Value} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : ReadTree checked registry functions mapping world prepared keys leafType leafCore sourceType source value steps projections leaf count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native finalStore administrative,
      Dynamic.ProjectionsRead (some source) projections (some leaf) ∧
      ValueRep checked registry functions mapping world leafType leaf native leafCore ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression with
  | leaf related => exact ⟨_, store, [], .nil, related, .inRight (.inRight (selected.evaluates store)), by simp, rfl⟩
  | compatible _ _ ih => exact ih environment store current keyExpression selected keysSelected
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild steps projections leaf count fields owner branchAt constructor branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨native, finalStore, administrative, read, related, evaluated, appended, counted⟩ :=
      ih (payload :: environment) store _ (shift 1 keyExpression)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
    exact ⟨native, finalStore, administrative, .member sourceAt read, related,
      .matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]) evaluated,
      appended, counted⟩
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child steps projections leaf count certificate fields keyRep keyAt read tail ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected keySelected
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨leafNative, finalStore, after, tailRead, represented, tailEvaluated, appended, counted⟩ :=
      ih native related (native :: environment) _ (.var 0) (shift 1 keyExpression) (.var rfl)
        (by simpa [shift] using keysSelected.weaken native)
    obtain ⟨before, beforeAppended, firstCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    refine ⟨leafNative, finalStore, before ++ after, ?_, represented, LanguageResult.bind_success _ evaluated tailEvaluated, ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound found tailRead
      | default absent defaulted => exact .indexDefault absent defaulted tailRead
    · rw [appended, beforeAppended, List.append_assoc]
    · simp only [List.length_append, firstCount, counted]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedUpdates
/-! Full-payload reconstruction for compatible mixed paths. The selected raw
constructor ID and mapping header/default are kept; each mapping lookup occurs
before its child update and insertion. Child execution is derived from Trees. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive UpdateTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) (replacementSource : Dynamic.Value) (replacement : Value) :
    TypeSystem.Ty → Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.Value → Nat → Prop where
  | leaf {sourceType source value type}
      (related : ValueRep checked registry functions mapping world sourceType replacementSource replacement type) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceType source value type [] [] replacementSource 0
  | compatible {expected actual source value type steps projections updated count}
      (view : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
      (tail : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement actual source value type steps projections updated count) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement expected source value type steps projections updated count
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild updatedChild steps projections count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (constructor : branch.constructor = tag) (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement childType sourceChild valueChild fieldType steps projections updatedChild count) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement expected
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values))) (.namedData tag.owner)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections)
        (.constructed metadata (sources.set index updatedChild)) count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child updatedChild updatedEntries steps projections count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceValue child value index.layout.valueType steps projections updatedChild count)
      (inserted : Dynamic.MappingInsert lookup updatedChild sources updatedEntries) :
      UpdateTree checked registry functions mapping world prepared keys replacementSource replacement (.mapping sourceKey sourceValue)
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) (.mapping sourceKey sourceValue updatedEntries)
        (2 * (checked.catalog.entries.length + 1) + count)

private theorem replaceAt {values : List Dynamic.Value} {index : Nat} {previous : Dynamic.Value}
    (selected : Dynamic.ValueAt values index previous) (replacement : Dynamic.Value) :
    Dynamic.ValuesReplaceAt values index replacement (values.set index replacement) := by
  induction selected with
  | head => exact .head
  | tail _ ih => exact .tail ih

private theorem pack_eq (expressions : List Expr) : pack expressions = SourceCoreDataPlaces.pack expressions := by
  induction expressions with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest => simp only [pack, SourceCoreDataPlaces.pack, ih]

/-- Both frontends use this same structural bundle replacement expression.
The reused theorem has no strict catalog or source payload assumptions. -/
theorem replacePacked_evaluates {environment : Environment} {store : Store}
    {index : Nat} {types : List Ty} {values : List Value} {payload replacement : Expr} {value : Value}
    (length : types.length = values.length) (selected : Selects environment payload (packValues values))
    (newValue : Selects environment replacement value) :
    Evaluates environment store (replacePacked index types payload replacement) (packValues (values.set index value)) store := by
  simpa only [replacePacked, SourceCoreDataPlaces.replacePacked, pack_eq] using
    (DataPlaceMembers.replacePacked_evaluates (index := index) (store := store) length selected newValue)

theorem UpdateTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {replacementSource source updated : Dynamic.Value} {replacement value : Value}
    {sourceType : TypeSystem.Ty} {nativeType : Ty} {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : UpdateTree checked registry functions mapping world prepared keys replacementSource replacement sourceType source value nativeType steps projections updated count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (type : Ty) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ native finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some source) projections updated ∧
      ValueRep checked registry functions mapping world sourceType updated native nativeType ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression) (.inRight .word native) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store type current keyExpression replacementExpression with
  | leaf related => exact ⟨_, store, [], .leaf rfl, related, .inRight (replacementSelected.evaluates store), by simp, rfl⟩
  | compatible view _ ih =>
    obtain ⟨native, finalStore, administrative, updated, related, evaluated, appended, count⟩ :=
      ih environment store type current keyExpression replacementExpression selected keysSelected replacementSelected
    exact ⟨native, finalStore, administrative, updated, .compatible view related, evaluated, appended, count⟩
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild updatedChild steps projections count fields owner branchAt constructor branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨child, finalStore, administrative, changed, related, evaluated, appended, counted⟩ :=
      ih (payload :: environment) store fieldType _ (shift 1 keyExpression) (shift 1 replacementExpression)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
        (by simpa [shift] using replacementSelected.weaken payload)
    refine ⟨_, finalStore, administrative, .member sourceAt changed (replaceAt sourceAt updatedChild),
      (fields.replace field fieldCore related).represents,
      Evaluates.matchData (selected.evaluates store) owner (by simp only [List.getElem?_map, branchAt, Option.map_some]; rfl) ?_, appended, counted⟩
    apply LanguageResult.bind_success _ evaluated
    rw [constructor]
    exact .inRight (.construct (.pair (.first (.var rfl)) (replacePacked_evaluates arity (.second (.var rfl)) (.var rfl))))
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child updatedChild updatedEntries steps projections count certificate fields keyRep keyAt read tail inserted ih =>
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected keySelected
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨changedNative, childStore, childCells, changed, childRep, childEvaluated, childAppended, childCounted⟩ :=
      ih native related (native :: environment) _ index.layout.valueType (.var 0) (shift 1 keyExpression) (shift 1 replacementExpression)
        (.var rfl) (by simpa [shift] using keysSelected.weaken native) (by simpa [shift] using replacementSelected.weaken native)
    let later := changedNative :: native :: environment
    obtain ⟨actualEntries, nativeEntries, actualInserted, represented, insertedEvaluation⟩ := insert_meaning certificate.comparison certificate.keyType faithful functionLeaves fields keyRep childRep
      later childStore (shift 2 current) (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keyExpression)) (.var 0)
      (by simpa [shift, List.range_succ] using (selected.weaken native).weaken changedNative)
      (by simpa [shift, List.range_succ, projectPacked_weaken] using (keySelected.weaken native).weaken changedNative) (.var rfl)
    have same := actualInserted.functional inserted
    subst actualEntries
    obtain ⟨before, beforeAppended, beforeCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    obtain ⟨after, afterAppended, afterCount⟩ := Transport.insertStore_extension certificate.comparison index.layout later childStore header fallback entries key changedNative
    refine ⟨_, Transport.insertStore certificate.comparison index.layout later childStore header fallback entries key changedNative,
      before ++ childCells ++ after, ?_, represented.represents,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_success _ childEvaluated ?_), ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound found changed inserted
      | default absent defaulted => exact .indexDefault absent defaulted changed inserted
    · simpa only [certificate.expression] using insertedEvaluation
    · rw [afterAppended, childAppended, beforeAppended]
      simp only [List.append_assoc]
    · simp only [List.length_append, beforeCount, childCounted, afterCount]; omega

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedFaults
/-! The first unavailable raw mapping default stops both mixed selectors and
updaters. Exact raw key-type guards belong to independent source fault typing;
the ordinary helpers do not implement an extra key-type check. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive FaultTree (checked : SourceCoreCompatibleCatalog.Checked) (registry : Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (prepared : Prepared) (keys : List Value) :
    Dynamic.Value → Value → Ty → List PreparedStep → List Dynamic.EvaluatedProjection → Dynamic.SemanticFault → Word → Nat → Prop where
  | missing {sourceKey sourceValue index sources header entries fallback lookup key steps projections}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyTyped : Dynamic.ValueRuntimeTypeMatches lookup sourceKey) (keyAt : keys[index.keyPosition]? = some key)
      (absent : Dynamic.MappingAbsent lookup sources) (unavailable : ¬ Dynamic.Defaultable sourceValue) :
      FaultTree checked registry functions mapping world prepared keys
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) (.missingMappingDefault sourceValue) (index.missing.add header)
        (checked.catalog.entries.length + 1)
  | member {expected metadata tag id sources values types dataType index branches branch fieldType childType name}
      {sourceChild valueChild steps projections reason token count}
      (fields : ConstructorFields checked registry functions mapping world expected metadata tag id sources values types)
      (owner : tag.owner = dataType) (branchAt : branches[tag.index]? = some branch)
      (branchTypes : branch.payloadTypes = types)
      (field : metadata.payloadTypes[index]? = some childType) (fieldCore : types[index]? = some fieldType)
      (sourceAt : Dynamic.ValueAt sources index sourceChild) (coreAt : values[index]? = some valueChild)
      (tail : FaultTree checked registry functions mapping world prepared keys sourceChild valueChild fieldType steps projections reason token count) :
      FaultTree checked registry functions mapping world prepared keys
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (packValues values))) (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) reason token count
  | mapping {sourceKey sourceValue index sources header entries fallback lookup key child steps projections reason token count}
      (certificate : Index checked index)
      (fields : Fields checked registry functions mapping world sourceKey sourceValue sources header index.layout entries fallback)
      (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType lookup key)
      (keyTyped : Dynamic.ValueRuntimeTypeMatches lookup sourceKey) (keyAt : keys[index.keyPosition]? = some key)
      (selected : Selected lookup sources sourceValue child)
      (tail : ∀ value, Payload registry functions mapping world sourceValue index.layout.valueType child value →
        FaultTree checked registry functions mapping world prepared keys child value index.layout.valueType steps projections reason token count) :
      FaultTree checked registry functions mapping world prepared keys
        (.mapping sourceKey sourceValue sources) (Transport.carrier header fallback index.layout entries) (SourceCoreMappingWithDefault.type index.layout)
        (.index index :: steps) (.index lookup :: projections) reason token (checked.catalog.entries.length + 1 + count)

 theorem FaultTree.preserves {checked : SourceCoreCompatibleCatalog.Checked} {registry : Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {prepared : Prepared} {keys : List Value} {source : Dynamic.Value} {value : Value} {type : Ty}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys source value type steps projections reason token count)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (store : Store) (current keyExpression replacement : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some source) projections reason ∧
      Evaluates environment store (select prepared steps current keyExpression) (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacement) (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  induction tree generalizing environment store current keyExpression replacement with
  | @missing sourceKey sourceValue index sources header entries fallback lookup key steps projections certificate fields keyRep keyTyped keyAt absent unavailable =>
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    have result : result = .inLeft index.layout.valueType (.word (index.missing.add header)) := by
      cases meaning with
      | found found _ => exact (absent.excludes_lookup found).elim
      | default _ defaulted _ => exact (unavailable defaulted.defaultable).elim
      | missing => rfl
    subst result
    obtain ⟨administrative, appended, counted⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    exact ⟨_, administrative, .indexDefaultUnavailable keyTyped absent unavailable,
      LanguageResult.bind_failure _ evaluated, LanguageResult.bind_failure _ evaluated, appended, counted⟩
  | @member expected metadata tag id sources values types dataType index branches branch fieldType childType name sourceChild valueChild steps projections reason token count fields owner branchAt branchTypes field fieldCore sourceAt coreAt tail ih =>
    have arity : branch.payloadTypes.length = values.length := branchTypes ▸ (fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1)
    let payload := Value.pair (.word id) (packValues values)
    obtain ⟨finalStore, administrative, fault, readEvaluation, updateEvaluation, appended, counted⟩ :=
      ih (payload :: environment) store _ (shift 1 keyExpression) (shift 1 replacement)
        (projectPacked_selects (.second (.var (index := 0) rfl)) arity index coreAt)
        (by simpa [shift] using keysSelected.weaken payload)
    refine ⟨finalStore, administrative, .member sourceAt fault, ?_, ?_, appended, counted⟩
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEvaluation
    · exact .matchData (selected.evaluates store) owner
        (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) (LanguageResult.bind_failure _ updateEvaluation)
  | @mapping sourceKey sourceValue index sources header entries fallback lookup key child steps projections reason token count certificate fields keyRep keyTyped keyAt read tail ih =>
    obtain ⟨result, meaning, evaluated⟩ := selectedIndex_meaning certificate prepared faithful functionLeaves fields keyRep
      environment store current keyExpression selected (projectPacked_selects keysSelected keyLength index.keyPosition keyAt)
    obtain ⟨native, rfl, related⟩ := read.payload meaning
    obtain ⟨finalStore, after, fault, readEvaluation, updateEvaluation, appended, counted⟩ :=
      ih native related (native :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacement) (.var rfl)
        (by simpa [shift] using keysSelected.weaken native)
    obtain ⟨before, beforeAppended, beforeCount⟩ := Transport.lookupStore_extension certificate.comparison index.layout environment store header fallback entries key
    refine ⟨finalStore, before ++ after, ?_, LanguageResult.bind_success _ evaluated readEvaluation,
      LanguageResult.bind_success _ evaluated (LanguageResult.bind_failure _ updateEvaluation), ?_, ?_⟩
    · cases read with
      | found found => exact .indexFound keyTyped found fault
      | default absent defaulted => exact .indexDefault keyTyped absent defaulted fault
    · rw [appended, beforeAppended, List.append_assoc]
    · simp only [List.length_append, beforeCount, counted]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.MixedPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding
/-! Actual public encoder receipts supply the value-level lookup theorem.
Registered layouts authenticate the omitted key type in the outer carrier;
no equality of native mapping carrier types is treated as a full layout cast. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend CompatiblePayload CompatibleEquality DataEquality

 theorem registered_layout_eq {definitions : DataEnvironment} {left right : Core.OrderedMapping.Layout}
    (a : left.Registered definitions) (b : right.Registered definitions)
    (type : SourceCoreMappingWithDefault.type left = SourceCoreMappingWithDefault.type right) : left = right := by
  have parts : left.valueType = right.valueType ∧ left.dataType = right.dataType := by
    simpa [SourceCoreMappingWithDefault.type, Core.OrderedMapping.Layout.lookupResult, Core.OrderedMapping.Layout.type] using type
  have definitions := a.lookup.symm.trans (parts.2 ▸ b.lookup)
  have key : left.keyType = right.keyType := by
    have payloads := congrArg DataDefinition.constructorPayloadTypes (Option.some.inj definitions)
    simp only [Core.OrderedMapping.Layout.definition, List.cons.injEq, Ty.product.injEq, and_true] at payloads
    exact payloads.2.1.1
  cases left; cases right
  simp_all

 theorem encoded_lookup_run {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    (comparison : SourceCoreCompatibleDataEquality.Prepared context.checked) (layout : Core.OrderedMapping.Layout)
    (registered : layout.Registered context.checked.catalog.definitions) (keyType : layout.keyType = comparison.type)
    {sourceKey sourceValue : TypeSystem.Ty}
    (mappingProjection : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type layout))
    (keyProjection : context.checked.catalog.project sourceKey = .ok layout.keyType)
    {carrier : SourceCoreDataValues.Value} {sources : List (Dynamic.Value × Dynamic.Value)}
    {keyCarrier : SourceCoreDataValues.Value} {sourceLookup : Dynamic.Value}
    {encodedMapping : SourceCoreCompatibleValues.Encoded fuel context (.mapping sourceKey sourceValue) carrier}
    {encodedKey : SourceCoreCompatibleValues.Encoded fuel encodedMapping.context sourceKey keyCarrier}
    (mappingAccepted : SourceCoreCompatibleValues.encode fuel context (.mapping sourceKey sourceValue) carrier = .ok encodedMapping)
    (keyAccepted : SourceCoreCompatibleValues.encode fuel encodedMapping.context sourceKey keyCarrier = .ok encodedKey)
    (mappingMeaning : CompatibleEncoding.Means carrier (.mapping sourceKey sourceValue sources))
    (keyMeaning : CompatibleEncoding.Means keyCarrier sourceLookup)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    (mapping : GeneralHeap.LocationMap) (world : StoreTyping) (environment : Environment) (store : Store) (missingBase : Word)
    (mappingExpression keyExpression : Expr)
    (mappingSelected : Selects environment mappingExpression encodedMapping.value)
    (keySelected : Selects environment keyExpression encodedKey.value) :
    ∃ header result finalStore,
      MetadataRep encodedKey.context.registry (.mapping sourceKey sourceValue) header ∧
      ReadResult context.checked encodedKey.context.registry functions mapping world sourceValue sourceLookup sources layout.valueType missingBase header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase comparison.expression mappingExpression keyExpression) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (SourceCoreMappingWithDefault.lookup layout missingBase comparison.expression mappingExpression keyExpression) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      ∃ administrative, finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  have represented := CompatibleAmbientEncoding.encode_represents_at (functions := functions) mappingAccepted mappingMeaning mapping world
  have represented := represented.extend encodedKey.preserves (.refl mapping) (.refl world)
  have keyRep := CompatibleAmbientEncoding.encode_represents_at (context := encodedMapping.context) (functions := functions) keyAccepted keyMeaning mapping world
  have mappingType := Except.ok.inj (encodedMapping.projected.symm.trans mappingProjection)
  have nativeKeyType := Except.ok.inj (encodedKey.projected.symm.trans keyProjection)
  rw [nativeKeyType] at keyRep
  obtain ⟨header, actualLayout, entries, fallback, value, type, _, fields⟩ := mapping_fields represented rfl
  have same := registered_layout_eq fields.registered registered (type.symm.trans mappingType)
  subst actualLayout
  obtain ⟨result, meaning, completes, reflects⟩ := lookup_run comparison keyType faithful functionLeaves fields keyRep
    environment store missingBase mappingExpression keyExpression (by simpa only [value] using mappingSelected) keySelected
  exact ⟨header, result, _, fields.metadata, meaning, completes, reflects,
    Transport.lookupStore_extension comparison layout environment store header fallback entries encodedKey.value⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot
/-! An absent declared mapping root is normalized by the actual literal emitted
by `describe`. Its header and nested default come from the certified compatible
encoder. Literal evaluation and root normalization preserve the entire store;
only the later comparator helpers allocate administrative cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping.VirtualRoot
open Core Frontend SourceInference CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces

inductive Quoted : Value → Expr → Prop where
  | unit : Quoted .unit .unit
  | bool (value : Bool) : Quoted (.bool value) (.bool value)
  | word (value : Word) : Quoted (.word value) (.word value)
  | integer (value : Int) : Quoted (.integer value) (.integer value)
  | pair {a b x y} : Quoted a x → Quoted b y → Quoted (.pair a b) (.pair x y)
  | inLeft {value expression} (type : Ty) : Quoted value expression → Quoted (.inLeft type value) (.inLeft type expression)
  | inRight {value expression} (type : Ty) : Quoted value expression → Quoted (.inRight type value) (.inRight type expression)
  | constructed {value expression} (constructor : ConstructorId) : Quoted value expression → Quoted (.constructed constructor value) (.construct constructor expression)

theorem quoted_of_quote {value : Value} {expression : Expr}
    (generated : SourceCoreCompatibleDataExpressions.quote value = some expression) : Quoted value expression := by
  induction value using Value.rec (motive_2 := fun _ => True) generalizing expression with
  | unit => cases generated; exact .unit
  | bool value => cases generated; exact .bool value
  | word value => cases generated; exact .word value
  | integer value => cases generated; exact .integer value
  | hostFunction | closure | cellRef => cases generated
  | pair a b first second =>
    cases left : SourceCoreCompatibleDataExpressions.quote a <;> cases right : SourceCoreCompatibleDataExpressions.quote b <;>
      simp [SourceCoreCompatibleDataExpressions.quote, left, right] at generated
    cases generated
    exact .pair (first left) (second right)
  | inLeft type value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .inLeft type (ih child)
  | inRight type value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .inRight type (ih child)
  | constructed constructor value ih =>
    cases child : SourceCoreCompatibleDataExpressions.quote value <;> simp [SourceCoreCompatibleDataExpressions.quote, child] at generated
    cases generated
    exact .constructed constructor (ih child)
  | nil | cons => trivial

theorem Quoted.weaken {value : Value} {expression : Expr} (quoted : Quoted value expression) (cutoff : Nat) :
    expression.weakenAt cutoff = expression := by
  induction quoted <;> simp_all [Expr.weakenAt]

theorem Quoted.evaluates {value : Value} {expression : Expr} (quoted : Quoted value expression)
    (environment : Environment) (store : Store) : Evaluates environment store expression value store := by
  induction quoted with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | pair _ _ left right => exact .pair left right
  | inLeft _ _ ih => exact .inLeft ih
  | inRight _ _ ih => exact .inRight ih
  | constructed _ _ ih => exact .construct ih

/-- A static receipt of the actual encoder and quote calls in `describe`. -/
inductive Generated (context : SourceCoreCompatibleDataPlaces.Context) (route : Route)
    (key value : TypeSystem.Ty) : Prop where
  | encoded {expression : Expr}
      {encoded : SourceCoreCompatibleValues.Encoded ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value [])}
      (accepted : SourceCoreCompatibleValues.encode ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value []) = .ok encoded)
      (unchanged : encoded.context.registry.entries = context.registry.entries)
      (quoted : SourceCoreCompatibleDataExpressions.quote encoded.value = some expression)
      (root : route.rootMapping = some expression) : Generated context route key value

theorem generated_of_describe {context : SourceCoreCompatibleDataPlaces.Context} {signatures : ProgramSignatures}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {binder : TypedBinder} {key value : TypeSystem.Ty} {route : Route}
    (found : rootBinder source assignment.target.root = .ok binder)
    (declared : binder.scheme.body = .mapping key value)
    (accepted : describe context signatures source site assignment = .ok route) : Generated context route key value := by
  rcases binder with ⟨id, name, ⟨quantified, declaredType⟩, requirements, staged, span⟩
  dsimp only at declared
  subst declaredType
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> try cases accepted
  obtain ⟨actualBinder, binding, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  have same := Except.ok.inj (binding.symm.trans found)
  subst actualBinder
  obtain ⟨rootType, rootProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := DataEqualityGeneration.bind_ok accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  cases identity : context.checked.catalog.identity? (.mapping key value) with
  | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
  | some identityValue =>
    simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨coreKey, keyProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
    obtain ⟨coreValue, valueProjected, accepted⟩ := DataEqualityGeneration.bind_ok accepted
    split at accepted <;> try cases accepted
    cases encodedBy : SourceCoreCompatibleValues.encode ((TypeSystem.Ty.mapping key value).size + 20) context (.mapping key value) (.mapping key value []) with
    | error error => simp [encodedBy, Except.mapError] at accepted
    | ok encoded =>
      simp only [encodedBy, Except.mapError] at accepted
      split at accepted <;> try cases accepted
      rename_i unchanged
      cases quoted : SourceCoreCompatibleDataExpressions.quote encoded.value with
      | none => simp [quoted, throw] at accepted
      | some expression =>
        simp only [quoted] at accepted
        cases projected : project context.checked site assignment.target.type with
        | error error => simp [projected] at accepted
        | ok type =>
          simp only [projected] at accepted
          cases accepted
          exact .encoded encodedBy unchanged quoted rfl

/-- Only the returned registry entries are inspected by generated literal code.
The actual encoder's extension receipt supplies the other registry laws. -/
theorem return_registry {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    {expected : TypeSystem.Ty} {source : SourceCoreDataValues.Value}
    (encoded : SourceCoreCompatibleValues.Encoded fuel context expected source)
    (unchanged : encoded.context.registry.entries = context.registry.entries) :
    SourceCoreRawMetadata.Extends encoded.context.registry context.registry where
  signatures := encoded.preserves.signatures.symm
  limits := encoded.preserves.limits.symm
  staticLength := encoded.preserves.staticLength.symm
  suffix := ⟨[], by simpa only [List.append_nil] using unchanged.symm⟩

theorem Generated.fields {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping) :
    ∃ expression header layout fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback := by
  cases generated with
  | encoded accepted unchanged quote root =>
    have represented := CompatibleAmbientEncoding.encode_represents_at (functions := functions) accepted (.mapping .empty) mapping world
    have represented := represented.extend (return_registry _ unchanged) (.refl mapping) (.refl world)
    obtain ⟨header, layout, entries, fallback, native, _, _, fields⟩ := mapping_fields represented rfl
    have empty : entries = [] := by
      cases entries with
      | nil => rfl
      | cons head tail => have length := fields.stored.length; simp at length
    subst entries
    exact ⟨_, header, layout, fallback, root, by simpa only [native] using quoted_of_quote quote, fields⟩

theorem Generated.at_layout {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (layout : Core.OrderedMapping.Layout) (registered : layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout)) :
    ∃ expression header fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback := by
  obtain ⟨expression, header, actualLayout, fallback, root, quoted, fields⟩ := generated.fields functions mapping world
  have same := registered_layout_eq fields.registered registered (Except.ok.inj (fields.represents.projection.symm.trans projected))
  subst actualLayout
  exact ⟨expression, header, fallback, root, quoted, fields⟩

theorem Generated.at_layout_extended {context : SourceCoreCompatibleDataPlaces.Context} {route : Route}
    {key value : TypeSystem.Ty} (generated : Generated context route key value)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (layout : Core.OrderedMapping.Layout) (registered : layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry) :
    ∃ expression header fallback,
      route.rootMapping = some expression ∧
      Quoted (Transport.carrier header fallback layout []) expression ∧
      Fields context.checked registry functions mapping world key value [] header layout [] fallback := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout functions mapping world layout registered projected
  exact ⟨expression, header, fallback, root, quoted, ⟨fields.metadata.extend extended,
    fields.identity, fields.keyProjection, fields.valueProjection, fields.registered,
    fields.stored.extend extended (.refl mapping) (.refl world), fields.default.extend extended (.refl mapping) (.refl world)⟩⟩

theorem normalize_absent (prepared : Prepared) {expression : Expr} {value : Value}
    (root : prepared.route.rootMapping = some expression) (quoted : Quoted value expression)
    (environment : Environment) (store : Store) (optional : Expr)
    (selected : Selects environment optional (.inLeft prepared.route.rootType .unit)) :
    Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit value) store := by
  simp only [normalizeRoot, root]
  apply Evaluates.caseLeft (selected.evaluates store)
  apply Evaluates.inRight
  rw [quoted.weaken]
  exact quoted.evaluates _ store

theorem generated_normalizes {context : SourceCoreCompatibleDataPlaces.Context} {prepared : Prepared}
    {key value : TypeSystem.Ty} (generated : Generated context prepared.route key value)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
    (environment : Environment) (store : Store) (optional : Expr)
    (selected : Selects environment optional (.inLeft prepared.route.rootType .unit)) :
    ∃ header layout fallback,
      Dynamic.RootInitialValue ⟨.mapping key value, none, none⟩ (some (.mapping key value [])) ∧
      Fields context.checked context.registry functions mapping world key value [] header layout [] fallback ∧
      Evaluates environment store (normalizeRoot prepared optional) (.inRight .unit (Transport.carrier header fallback layout [])) store := by
  obtain ⟨expression, header, layout, fallback, root, quoted, fields⟩ := generated.fields functions mapping world
  exact ⟨header, layout, fallback, .emptyMapping _ _, fields, normalize_absent prepared root quoted environment store optional selected⟩

theorem getter_absent {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (packValues keys))) :
    ∃ header result finalStore administrative,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      ReadResult context.checked registry functions mapping world sourceValue sourceLookup [] index.layout.valueType index.missing header result ∧
      Evaluates environment store (.apply (getter prepared keyType) argument) (liftedRead prepared.optionalLeaf result) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout_extended functions mapping world index.layout registered projected extended
  let stored := Transport.carrier header fallback index.layout []
  let input := Value.pair (.inLeft prepared.route.rootType .unit) (packValues keys)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.second (.var 1))) key :=
    projectPacked_selects (.second (.var rfl)) keysLength _ keyAt
  obtain ⟨result, meaning, evaluated⟩ := selectOne_meaning certificate prepared faithful functionLeaves fields keyRep
    bodyEnvironment store (.var 0) (.second (.var 1)) (.var rfl) selectedKey
  obtain ⟨administrative, appended, length⟩ := Transport.lookupStore_extension certificate.comparison index.layout
    bodyEnvironment store header fallback [] key
  refine ⟨header, result, _, administrative, fields.metadata, .emptyMapping _ _, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  exact .caseRight (normalize_absent prepared root quoted _ store (.first (.var 0)) (.first (.var rfl))) evaluated

theorem setter_absent {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement))) :
    ∃ header fallback result finalStore administrative count,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      UpdateResult context.checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement [] header index.layout fallback index.missing result count ∧
      Evaluates environment store (.apply (setter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨expression, header, fallback, root, quoted, fields⟩ := generated.at_layout_extended functions mapping world index.layout registered projected extended
  let stored := Transport.carrier header fallback index.layout []
  let input := Value.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement)
  let bodyEnvironment := stored :: input :: environment
  have selectedKey : Selects bodyEnvironment
      (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (.first (.second (.var 1)))) key :=
    projectPacked_selects (.first (.second (.var rfl))) keysLength _ keyAt
  obtain ⟨result, finalStore, administrative, count, meaning, evaluated, appended, length⟩ := updateOne_meaning certificate prepared faithful functionLeaves
    fields keyRep replacementRep bodyEnvironment store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) selectedKey (.second (.second (.var rfl)))
  refine ⟨header, fallback, result, finalStore, administrative, count, fields.metadata, .emptyMapping _ _, meaning, ?_, appended, length⟩
  apply Evaluates.apply .lambda (argumentSelected.evaluates store)
  simp only [steps]
  apply Evaluates.caseRight (normalize_absent prepared root quoted _ store (.first (.var 0)) (.first (.var rfl)))
  simpa only [bodyEnvironment, input, stored, rootType] using evaluated

theorem getter_absent_run {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup : Dynamic.Value} {key : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (packValues keys))) :
    ∃ header result finalStore administrative,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      ReadResult context.checked registry functions mapping world sourceValue sourceLookup [] index.layout.valueType index.missing header result ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done (liftedRead prepared.optionalLeaf result) finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (getter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = liftedRead prepared.optionalLeaf result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = context.checked.catalog.entries.length + 1 := by
  obtain ⟨header, result, finalStore, administrative, metadata, initial, meaning, evaluated, appended, count⟩ :=
    getter_absent certificate prepared steps generated registered projected extended faithful functionLeaves keyRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨header, result, finalStore, administrative, metadata, initial, meaning,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, count⟩

theorem setter_absent_run {context : SourceCoreCompatibleDataPlaces.Context} {index : PreparedIndex}
    (certificate : Index context.checked index) (prepared : Prepared) (steps : prepared.steps = [.index index])
    (rootType : prepared.route.rootType = SourceCoreMappingWithDefault.type index.layout)
    {sourceKey sourceValue : TypeSystem.Ty} (generated : Generated context prepared.route sourceKey sourceValue)
    (registered : index.layout.Registered context.checked.catalog.definitions)
    (projected : context.checked.catalog.project (.mapping sourceKey sourceValue) = .ok (SourceCoreMappingWithDefault.type index.layout))
    {registry : Registry} (extended : SourceCoreRawMetadata.Extends context.registry registry)
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    {functions : FunctionModel context.checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    {sourceLookup sourceReplacement : Dynamic.Value} {key replacement : Value}
    (keyRep : Payload registry functions mapping world sourceKey index.layout.keyType sourceLookup key)
    (replacementRep : Payload registry functions mapping world sourceValue index.layout.valueType sourceReplacement replacement)
    (environment : Environment) (store : Store) (keyType : Ty) (keys : List Value) (argument : Expr)
    (keysLength : prepared.keyTypes.length = keys.length) (keyAt : keys[index.keyPosition]? = some key)
    (argumentSelected : Selects environment argument (.pair (.inLeft prepared.route.rootType .unit) (.pair (packValues keys) replacement))) :
    ∃ header fallback result finalStore administrative count,
      MetadataRep registry (.mapping sourceKey sourceValue) header ∧
      Dynamic.RootInitialValue ⟨.mapping sourceKey sourceValue, none, none⟩ (some (.mapping sourceKey sourceValue [])) ∧
      UpdateResult context.checked registry functions mapping world sourceKey sourceValue sourceLookup sourceReplacement [] header index.layout fallback index.missing result count ∧
      (∃ required, ∀ budget, required ≤ budget → runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done result finalStore) ∧
      (∀ budget actual actualStore, runStateful budget
        (.initial (.apply (setter prepared keyType) argument) environment store) = .done actual actualStore →
          actual = result ∧ actualStore = finalStore) ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨header, fallback, result, finalStore, administrative, count, metadata, initial, meaning, evaluated, appended, length⟩ :=
    setter_absent certificate prepared steps rootType generated registered projected extended faithful functionLeaves keyRep replacementRep
      environment store keyType keys argument keysLength keyAt argumentSelected
  exact ⟨header, fallback, result, finalStore, administrative, count, metadata, initial, meaning,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated, appended, length⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping.VirtualRoot
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedHelpers
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
    {ambient : AmbientDefinitions context.checked.catalog.definitions}
    (functions : FunctionModel context.checked.catalog ambient) (mapping : GeneralHeap.LocationMap) (world : StoreTyping)
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingPreparation
/-! Exact equations for a real single-index compatible place preparation.
These static receipts do not assume any getter or setter execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMapping
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces

 theorem comparison_sourceType {checked : Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreCompatibleDataEquality.Prepared checked}
    (accepted : SourceCoreCompatibleDataEquality.prepare fuel checked source = .ok prepared) : prepared.sourceType = source := by
  unfold SourceCoreCompatibleDataEquality.prepare at accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  split at accepted <;> try cases accepted
  dsimp only at accepted
  split at accepted <;> cases accepted
  rfl

 def Index.of_generated {checked : Checked} {fuel : Nat} {source : TypeSystem.Ty}
    {prepared : SourceCoreCompatibleDataEquality.Prepared checked} {layout : Core.OrderedMapping.Layout}
    {key : ExpressionId} {position : Nat} {missing : Word}
    (accepted : SourceCoreCompatibleDataEquality.prepare fuel checked source = .ok prepared)
    (projected : checked.catalog.project source = .ok layout.keyType) :
    Index checked ⟨layout, key, position, prepared.expression, missing⟩ where
  comparison := prepared
  expression := rfl
  keyType := by
    have projection := prepared.projection
    rw [comparison_sourceType accepted] at projection
    exact Except.ok.inj (projected.symm.trans projection)

 theorem prepare_single {context : SourceCoreCompatibleDataPlaces.Context} {fuel : Nat} {route : Route} {invalid : Word} {missing : TypeSystem.Ty → Word}
    {layout : Core.OrderedMapping.Layout} {key : ExpressionId} {sourceKey sourceValue recordedValue : TypeSystem.Ty}
    {entry : SourceCoreDataCatalog.Entry} {comparison : SourceCoreCompatibleDataEquality.Prepared context.checked}
    (steps : route.steps = [.index layout key sourceValue])
    (selected : context.checked.catalog.entries[layout.dataType.index]? = some entry)
    (mappingType : entry.sourceType = .mapping sourceKey recordedValue)
    (generated : SourceCoreCompatibleDataEquality.prepare fuel context.checked sourceKey = .ok comparison) :
    prepare context fuel route invalid missing = .ok
      ⟨route, [.index ⟨layout, key, 0, comparison.expression, missing sourceValue⟩], [(key, layout.keyType)], invalid⟩ := by
  simp [prepare, steps, selected, mappingType, generated, bind, Except.bind, pure, Except.pure, Except.mapError]

end Solcore.SourceSemantics.CoreLowering.CompatibleMapping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedRuns
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes
/-! Runtime key guards follow the original source metadata up to staging
normalization. Core type projection is not an authentication rule. Function
leaves supply their own shallow source-type law, independent of capture heaps.
The remaining arbitrary nested data cases follow from the full payload relation.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend SourceInference GeneralHeap

/-- The independent source normalization agrees with the compiler's metadata
view, by structural recursion over every source type form. -/
theorem runtimeType_agrees_metadata (type : TypeSystem.Ty) :
    Dynamic.runtimeType type = SourceCoreRawMetadata.runtimeType type := by
  induction type <;> simp_all [Dynamic.runtimeType, SourceCoreRawMetadata.runtimeType]

def FunctionRuntimeViews {catalog : SourceCoreCompatibleCatalog.Catalog} {ambient : AmbientDefinitions catalog.definitions} (functions : FunctionModel catalog ambient) : Prop :=
  ∀ {registry mapping world parameter result source value type},
    functions.Represents registry mapping world (.function parameter result) source value type →
      Dynamic.ValueRuntimeTypeMatches source (.function parameter result)

/-- Exact metadata receipts and structural children determine runtime
compatibility, including staged mapping keys and proxies nested in products. -/
theorem ValueRep.source_runtimeView {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (functionTypes : FunctionRuntimeViews functions)
    (represented : ValueRep checked registry functions mapping world sourceType source value type) :
    Dynamic.ValueRuntimeTypeMatches source sourceType := by
  induction represented using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => exact Dynamic.ValueRuntimeType.unit.matches
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second =>
    cases first with
    | intro first firstView =>
      cases second with
      | intro second secondView =>
        exact .intro (.product first second) (by simp only [Dynamic.runtimeType, firstView, secondView])
  | function related => exact functionTypes related
  | proxy => exact (Dynamic.ValueRuntimeType.proxy _).matches
  | constructed => exact (Dynamic.ValueRuntimeType.constructed _ _).matches
  | mappingValue => exact (Dynamic.ValueRuntimeType.mapping _ _ _).matches
  | compatible same _ ih =>
    cases ih with
    | intro typed view =>
      exact .intro typed (view.trans (by simpa only [runtimeType_agrees_metadata] using same.symm))
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRawScalarFields
/-! Original scalar metadata determines both represented values without
any assumptions about the representation of callable values. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRawScalarFields
open Core Frontend SourceInference GeneralHeap CompatiblePayload

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
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

theorem integer_fields {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer ∧ type = .integer := by
  revert view
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | integer integer => intro _; exact ⟨integer, rfl, rfl, rfl⟩
  | compatible same _ ih => intro view; exact ih (same.symm.trans view)
  | @constructed metadata id tag sources values types _ _ _ projected _ _ _ =>
      intro view
      have scalar : checked.catalog.project metadata.resultType = .ok .integer := by
        rw [← checked.catalog.project_runtimeType, view]
        rfl
      cases Except.ok.inj (projected.symm.trans scalar)
  | unit | bool | word | product | function | proxy | mappingValue =>
      intro view
      cases view
  | nil | cons | empty | entry | absent | present => trivial

end Solcore.SourceSemantics.CoreLowering.CompatibleRawScalarFields
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
/-! Nominal entries produced by the actual compatible catalog factory retain
the complete source constructor list. Finished native definitions have exactly
that many payloads; pending recursive reservations remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
open Core Frontend SourceInference SourceCoreCompatibleCatalog
open CompatibleCatalogRegistrationPrefix

def EntryShape (signatures : ProgramSignatures) (entry : Entry) : Prop :=
  ∀ declaration arguments, SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments) →
    ∃ signature, signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature] ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      ∀ definition, entry.definition = some definition →
        definition.constructorPayloadTypes.length = signature.constructors.length

def Shapes (signatures : ProgramSignatures) (catalog : Catalog) : Prop :=
  ∀ entry ∈ catalog.entries, EntryShape signatures entry

def Complete (catalog : Catalog) : Prop :=
  ∀ entry ∈ catalog.entries, entry.definition.isSome = true

theorem Shapes.empty (signatures : ProgramSignatures) (callableContracts : Bool) :
    Shapes signatures {callableContracts} := by
  intro entry member
  cases member

private theorem Shapes.append {signatures : ProgramSignatures} {catalog : Catalog} {entry : Entry}
    (previous : Shapes signatures catalog) (added : EntryShape signatures entry) :
    Shapes signatures {catalog with entries := catalog.entries ++ [entry]} := by
  intro item member
  rcases List.mem_append.mp member with member | member
  · exact previous item member
  · exact List.mem_singleton.mp member ▸ added

private theorem modify_preserves {α : Type} (property : α → Prop) (entries : List α)
    (index : Nat) (update : α → α) (previous : ∀ entry ∈ entries, property entry)
    (updated : ∀ entry, entries[index]? = some entry → property (update entry)) :
    ∀ entry ∈ entries.modify index update, property entry := by
  induction entries generalizing index with
  | nil => intro entry member; simp at member
  | cons head tail ih =>
    cases index with
    | zero =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact updated head rfl
      · exact previous entry (by simp [member])
    | succ index =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact previous entry (by simp)
      · exact ih index (fun item member => previous item (by simp [member]))
          (fun item found => updated item found) entry member

private theorem install_preserves {signatures : ProgramSignatures} {before after : Catalog}
    {entry : Entry} (payloads : List Ty)
    (extension : EntriesExtend {before with entries := before.entries ++ [entry]} after)
    (previous : Shapes signatures after)
    (updated : EntryShape signatures {entry with definition := some ⟨payloads⟩}) :
    Shapes signatures {after with entries := after.entries.modify before.entries.length (fun item => {item with definition := some ⟨payloads⟩})} := by
  apply modify_preserves _ _ _ _ previous
  intro item found
  have original : ({before with entries := before.entries ++ [entry]} : Catalog).entries[before.entries.length]? = some entry := by
    simp
  have same := extension.lookup original
  have equal := Option.some.inj (found.symm.trans same)
  subst item
  exact updated

private theorem nonnominal {signatures : ProgramSignatures} {entry : Entry}
    (absent : SourceCoreDataCatalog.nominalParts entry.sourceType = none) : EntryShape signatures entry := by
  intro declaration arguments found
  rw [absent] at found
  cases found

private theorem reservation {signatures : ProgramSignatures} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {signature : ProgramDataSignature}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature]) :
    EntryShape signatures ⟨type, none, signature.constructors.map (·.id)⟩ := by
  intro actual parameters found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nominal.symm.trans found))
  exact ⟨signature, selected, rfl, fun _ impossible => by cases impossible⟩

private theorem installed {signatures : ProgramSignatures} {type : TypeSystem.Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {signature : ProgramDataSignature}
    {payloads : List Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (count : payloads.length = signature.constructors.length) :
    EntryShape signatures ⟨type, some ⟨payloads.map (Ty.product .word)⟩, signature.constructors.map (·.id)⟩ := by
  intro actual parameters found
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (nominal.symm.trans found))
  refine ⟨signature, selected, rfl, ?_⟩
  intro definition same
  cases same
  simpa using count

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem exact_signature {signatures : ProgramSignatures} {declaration : Resolved.DeclarationId}
    {signature : ProgramDataSignature}
    (accepted : (match signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
      | [] => throw (Error.catalog (.missingData declaration))
      | [signature] => pure signature
      | _ => throw (Error.catalog (.ambiguousData declaration))) = (Except.ok signature : Except SourceCoreCompatibleCatalog.Error ProgramDataSignature)) :
    signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature] := by
  split at accepted
  · cases accepted
  · cases accepted; assumption
  · cases accepted

theorem registered_shapes (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, Shapes signatures before →
      registerType signatures fuel before original = .ok (after, type) → Shapes signatures after) ∧
    (∀ before originals after types, Shapes signatures before →
      registerTypes signatures fuel before originals = .ok (after, types) →
        Shapes signatures after ∧ types.length = originals.length) := by
  induction fuel with
  | zero =>
    constructor
    · intro before original after type previous accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact previous
        · cases accepted
      · cases accepted
    · intro before originals after types previous accepted
      cases originals with
      | nil => cases accepted; exact ⟨previous, rfl⟩
      | cons => cases accepted
  | succ fuel ih =>
    constructor
    · intro before original after type previous accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact previous
        · split at accepted
          · obtain ⟨native, _, accepted⟩ := bind_ok accepted
            cases accepted
            exact previous
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact ih.1 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact ih.1 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
          · obtain ⟨registered, child, accepted⟩ := bind_ok accepted
            cases accepted
            rename_i inner view
            have absent : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = none := by rw [view]; rfl
            have reserved := previous.append (nonnominal (entry := ⟨SourceCoreRawMetadata.runtimeType original, none, []⟩) absent)
            exact install_preserves _ (registerType_entries child) (ih.1 _ _ _ _ reserved child)
              (nonnominal absent)
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            rename_i key value view
            have absent : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = none := by rw [view]; rfl
            have reserved := previous.append (nonnominal (entry := ⟨SourceCoreRawMetadata.runtimeType original, none, []⟩) absent)
            have shaped := ih.1 _ _ _ _ (ih.1 _ _ _ _ reserved initial) final
            exact install_preserves _ ((registerType_entries initial).trans (registerType_entries final)) shaped
              (nonnominal absent)
          · split at accepted
            · obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
              have selected := exact_signature selected
              split at accepted
              · split at accepted
                · obtain ⟨_, _, accepted⟩ := bind_ok accepted
                  obtain ⟨registered, child, accepted⟩ := bind_ok accepted
                  cases accepted
                  have reserved := previous.append (reservation (by assumption) selected)
                  obtain ⟨shaped, count⟩ := ih.2 _ _ _ _ reserved child
                  apply install_preserves _ (registerTypes_entries child) shaped
                  apply installed (by assumption) selected
                  simpa using count
                · cases accepted
              · cases accepted
            · cases accepted
      · cases accepted
    · intro before originals after types previous accepted
      cases originals with
      | nil => cases accepted; exact ⟨previous, rfl⟩
      | cons original rest =>
        obtain ⟨first, initial, remaining⟩ := bind_ok accepted
        obtain ⟨tail, final, accepted⟩ := bind_ok remaining
        cases accepted
        obtain ⟨shaped, count⟩ := ih.2 _ _ _ _ (ih.1 _ _ _ _ previous initial) final
        exact ⟨shaped, by simpa using count⟩

theorem registerType_shapes {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (previous : Shapes signatures before)
    (accepted : registerType signatures fuel before original = .ok (after, type)) : Shapes signatures after :=
  (registered_shapes signatures fuel).1 _ _ _ _ previous accepted

theorem registerTypes_shapes {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (previous : Shapes signatures before)
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    Shapes signatures after ∧ types.length = originals.length :=
  (registered_shapes signatures fuel).2 _ _ _ _ previous accepted

theorem prepare_shapes {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked) :
    Shapes signatures checked.catalog := by
  unfold prepare at accepted
  obtain ⟨registered, produced, accepted⟩ := bind_ok accepted
  rcases registered with ⟨catalog, nativeTypes⟩
  have shaped := (registerTypes_shapes (Shapes.empty signatures callableContracts) produced).1
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  rcases discovered with ⟨seen, original⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact shaped
    · cases accepted

theorem identity_entry {catalog : Catalog} {original : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? original = some identity) :
    ∃ entry, catalog.entries[identity.index]? = some entry ∧
      entry.sourceType = SourceCoreRawMetadata.runtimeType original := by
  unfold Catalog.identity? at found
  cases selected : catalog.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType original)) with
  | none => simp [selected] at found
  | some item =>
    rcases item with ⟨entry, index⟩
    simp only [selected, Option.map_some, Option.some.injEq] at found
    subst identity
    have member := List.mem_of_find?_eq_some selected
    have sourceEq : entry.sourceType = SourceCoreRawMetadata.runtimeType original := by
      simpa using List.find?_some selected
    exact ⟨entry, List.mk_mem_zipIdx_iff_getElem?.mp member, sourceEq⟩

private theorem finished_of_forIn {entries : List (Entry × Nat)} {output : Unit}
    (accepted : forIn entries () (fun item _ => do
      if item.1.definition.isNone then throw (Error.catalog (.unfinishedDefinition item.2))
      pure (.yield ())) = (Except.ok output : Except SourceCoreCompatibleCatalog.Error Unit)) :
    ∀ item ∈ entries, item.1.definition.isSome = true := by
  induction entries with
  | nil => intro item member; cases member
  | cons item rest ih =>
    cases stored : item.1.definition with
    | none => simp [List.forIn_cons, stored, throw, bind, Except.bind] at accepted
    | some definition =>
      have remaining : forIn rest () (fun item _ => do
          if item.1.definition.isNone then throw (Error.catalog (.unfinishedDefinition item.2))
          pure (.yield ())) = (Except.ok output : Except SourceCoreCompatibleCatalog.Error Unit) := by
        simpa [List.forIn_cons, stored, pure, Except.pure, bind, Except.bind] using accepted
      intro actual member
      rcases List.mem_cons.mp member with rfl | member
      · simp [stored]
      · exact ih remaining actual member

theorem prepare_complete {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked) :
    Complete checked.catalog := by
  unfold prepare at accepted
  obtain ⟨registered, _, accepted⟩ := bind_ok accepted
  rcases registered with ⟨catalog, nativeTypes⟩
  obtain ⟨output, finished, accepted⟩ := bind_ok accepted
  have complete : Complete catalog := by
    intro entry member
    obtain ⟨index, found⟩ := List.getElem?_of_mem member
    have zipped : (entry, index) ∈ catalog.entries.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr found
    exact finished_of_forIn finished (entry, index) zipped
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  rcases discovered with ⟨seen, original⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact complete
    · cases accepted

theorem Shapes.nominal_coverage {signatures : ProgramSignatures} {catalog : Catalog}
    (shaped : Shapes signatures catalog)
    (complete : Complete catalog)
    {original : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {signature : ProgramDataSignature} {identity : DataTypeId} {definition : DataDefinition}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (declaration, arguments))
    (selected : signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (found : catalog.identity? original = some identity)
    (registered : catalog.definitions.lookupDataType? identity = some definition) :
    ∃ entry, catalog.entries[identity.index]? = some entry ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      definition.constructorPayloadTypes.length = signature.constructors.length := by
  obtain ⟨entry, entryAt, sourceEq⟩ := identity_entry found
  obtain ⟨actual, exact, ids, count⟩ := shaped entry (List.mem_of_getElem? entryAt)
    declaration arguments (by rw [sourceEq]; exact nominal)
  have same := List.singleton_inj.mp (exact.symm.trans selected)
  subst actual
  have definitionAt : entry.definition = some definition := by
    simp only [DataEnvironment.lookupDataType?, Catalog.definitions, List.getElem?_map, entryAt,
      Option.map_some, Option.some.injEq] at registered
    cases stored : entry.definition with
    | none =>
      have present := complete entry (List.mem_of_getElem? entryAt)
      simp [stored] at present
    | some stored => simpa [stored] using congrArg some registered
  exact ⟨entry, entryAt, ids, count definition definitionAt⟩

theorem prepare_nominal_coverage {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked)
    {original : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    {signature : ProgramDataSignature} {identity : DataTypeId} {definition : DataDefinition}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType original) = some (declaration, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) = [signature])
    (found : checked.catalog.identity? original = some identity)
    (registered : checked.catalog.definitions.lookupDataType? identity = some definition) :
    ∃ entry, checked.catalog.entries[identity.index]? = some entry ∧
      entry.constructors = signature.constructors.map (·.id) ∧
      definition.constructorPayloadTypes.length = signature.constructors.length := by
  have owner := prepare_signatures accepted
  rw [owner] at selected
  exact (prepare_shapes accepted).nominal_coverage (prepare_complete accepted) nominal selected found registered

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogNominalCoverage
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds
/-! The actual callable diagnostic producer starts at its requested minimum.
This finite receipt exposes the original checked unknown token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Allocation uses the actual checked word conversion of the computed start;
no property of the later decision traversal is assumed. -/
theorem prepare_unknown {plan : SourceCoreStageCodebook.Plan}
    {contracts : SourceCoreStageCodebook.Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program) :
    0 < program.unknown.val ∧ minimum ≤ program.unknown.val := by
  unfold SourceCoreCallableFaultSites.prepare at accepted
  obtain ⟨unknown, issued, accepted⟩ := bind_ok accepted
  obtain ⟨sites, _traversed, finished⟩ := bind_ok accepted
  have same : unknown = program.unknown := congrArg (·.unknown) (Except.ok.inj finished)
  rw [← same]
  change (match Word.ofNat? _ with
    | some value => Except.ok value
    | none => Except.error SourceCoreCallableFaultSites.Error.reasonSpaceExhausted) = .ok unknown at issued
  split at issued
  · rename_i value converted
    cases issued
    unfold Word.ofNat? at converted
    split at converted
    · have number := congrArg Fin.val (Option.some.inj converted).symm
      rw [number]
      exact ⟨Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩
    · cases converted
  · cases issued

/-- A retained token below the actual requested minimum is below the genuine
unknown-token boundary used by the public callable append. -/
theorem below_unknown {plan : SourceCoreStageCodebook.Plan}
    {contracts : SourceCoreStageCodebook.Table} {base : SourceCoreFaultSites.Table}
    {minimum : Nat} {program : SourceCoreCallableFaultSites.Program} {token : Word}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts base minimum = .ok program)
    (below : token.val < minimum) : token.val < program.unknown.val := by
  exact Nat.lt_of_lt_of_le below (prepare_unknown accepted).2

/-- The public receiver uses this same callable producer. Its filtered append
therefore preserves the base table's result for the retained earlier token. -/
theorem append_diagnostic {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {plan : SourceCoreStageCodebook.Plan} {contracts : SourceCoreStageCodebook.Table}
    {issuedBase table : SourceCoreFaultSites.Table} {minimum : Nat}
    {callable : SourceCoreCallableFaultSites.Program} {token : Word}
    (accepted : SourceCoreCallableFaultSites.prepare plan contracts issuedBase minimum = .ok callable)
    (present : prepared.base.callableDiagnostics = some callable)
    (below : token.val < minimum) :
    (CallableIndexedOwnedPublicFaultReceiverTables.appendCallable prepared table).diagnostic? token =
      table.diagnostic? token := by
  exact CallableIndexedOwnedPublicFaultReceiverTables.appendCallable_diagnostic present
    (below_unknown accepted below)

end Solcore.SourceSemantics.CoreLowering.CompatibleCallableDiagnosticBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
/-! Independent payload meaning supplies the public codec's structural output
certificate at the same actual metadata registry. Raw defaults and ordered
mapping rows remain exact; no successful codec call is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload

private theorem pack_eq (values : List Value) : SourceCorePublicOutputShapes.pack values = packValues values := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons second rest => exact congrArg (Value.pair head) ih

private theorem layout_at {checked : SourceCoreCompatibleCatalog.Checked}
    {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    (identity : checked.catalog.identity? (.mapping key value) = some layout.dataType)
    (keyProjection : checked.catalog.project key = .ok layout.keyType)
    (valueProjection : checked.catalog.project value = .ok layout.valueType)
    (registered : layout.Registered checked.catalog.definitions) :
    checked.catalog.mappingLayout key value = .ok layout := by
  simp only [SourceCoreCompatibleCatalog.Catalog.mappingLayout, identity, keyProjection, valueProjection,
    pure, Except.pure, bind, Except.bind]
  have same : (⟨layout.keyType, layout.valueType, layout.dataType⟩ : OrderedMapping.Layout) = layout := by cases layout; rfl
  rw [same]
  simp only [registered.lookup, ↓reduceIte]

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

private def Meaning (sourceType : TypeSystem.Ty) (source : Dynamic.Value) (native : Value) : Prop :=
  SourceCorePublicOutputShapes.Output checked registry world ambient.definitions sourceType native ∧
  ∀ raw, DefaultData raw source → ∃ data,
    SourceCoreCompatibleValues.defaultFromSource? raw = some data ∧
    SourceCorePublicOutputShapes.DefaultData checked registry sourceType data native

private theorem represents_shape {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {native : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source native type) :
    Meaning (checked := checked) (registry := registry) (ambient := ambient) (world := world) sourceType source native := by
  induction related using ValueRep.rec
    (motive_2 := fun types _ natives _ _ => SourceCorePublicOutputShapes.Payloads checked registry world ambient.definitions types natives)
    (motive_3 := fun key value _ entries _ _ _ => SourceCorePublicOutputShapes.Entries checked registry world ambient.definitions key value entries)
    (motive_4 := fun raw fallback nativeType _ =>
      SourceCorePublicOutputShapes.Default checked registry raw nativeType (OrderedMapping.optionValue nativeType fallback)) with
  | unit => exact ⟨.unit, fun _ data => by cases data; exact ⟨_, rfl, .unit⟩⟩
  | bool value => exact ⟨.bool value, fun _ data => by cases data; exact ⟨_, rfl, .bool _⟩⟩
  | word value => exact ⟨.word value, fun _ data => by cases data; exact ⟨_, rfl, .word _⟩⟩
  | integer value => exact ⟨.integer value, fun _ data => by cases data; exact ⟨_, rfl, .integer _⟩⟩
  | product _ _ first second =>
    refine ⟨.product first.1 second.1, ?_⟩
    intro raw data
    cases data with
    | product left right =>
      obtain ⟨a, firstAt, firstShape⟩ := first.2 _ left
      obtain ⟨b, secondAt, secondShape⟩ := second.2 _ right
      exact ⟨.product a b, by simp only [SourceCoreCompatibleValues.defaultFromSource?, firstAt, secondAt, bind, Option.bind, pure],
        .product firstShape secondShape⟩
  | function represented =>
    refine ⟨.function (functions.projection represented) (functions.runtime_hasType represented), ?_⟩
    intro raw data
    have callable := functions.source_function represented
    cases callable <;> cases data
  | proxy metadata identity _ =>
    exact ⟨.proxy metadata.lookup identity, fun _ data => by cases data; exact ⟨_, rfl, .proxy metadata.lookup identity⟩⟩
  | @constructed metadata id tag sources natives types metadataAt owner selected _ registered payloads ih =>
    have authentic := metadataAt.authenticated
    change SourceCoreRawMetadata.constructorAuthentic registry.signatures metadata = true at authentic
    rw [owner] at authentic
    have resolved : checked.resolveConstructor metadata = .ok tag := by
      simp only [SourceCoreCompatibleCatalog.Checked.resolveConstructor, authentic, selected,
        payloads.projection, registered, ↓reduceIte, pure, Except.pure, bind, Except.bind]
    have nominal : ∃ declaration arguments, metadata.resultType = TypeSystem.Ty.nominal declaration arguments := by
      cases CompatibleConstructorMetadata.facts authentic with
      | mk _ _ _ _ _ _ _ _ result => exact ⟨_, _, result⟩
    refine ⟨?_, fun _ data => by cases data⟩
    simpa only [pack_eq] using SourceCorePublicOutputShapes.Output.constructed metadataAt.lookup resolved nominal ih
  | @mappingValue key value id layout sources entries fallback metadata identity keyProjection valueProjection registered stored _ entriesIH defaultIH =>
    have layoutAt := layout_at identity keyProjection valueProjection registered
    refine ⟨.mapping metadata.lookup layoutAt entriesIH defaultIH, ?_⟩
    intro raw data
    cases data
    cases stored
    exact ⟨_, rfl, .mapping metadata.lookup layoutAt defaultIH⟩
  | compatible same _ ih =>
    refine ⟨.compatible same ih.1, ?_⟩
    intro raw data
    obtain ⟨carrier, projected, shaped⟩ := ih.2 raw data
    exact ⟨carrier, projected, .compatible same shaped⟩
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head.1 tail
  | empty key value _ _ => exact .empty key value
  | entry _ _ _ key value tail => exact .entry key.1 value.1 tail
  | @absent raw nativeType missing _ _ =>
    have absent := (CompatiblePayload.defaultValue?_absent_iff (type := raw) (fuel := raw.size + 1) (by omega)).mpr missing
    exact .absent (by simp only [SourceCoreCompatibleValues.defaultValue?, absent, Option.bind_none])
  | @present raw source native nativeType meaning _ ih =>
    obtain ⟨rawValue, computed, data⟩ := CompatiblePayload.defaultValue?_canonical meaning
    obtain ⟨carrier, projected, shaped⟩ := ih.2 rawValue data
    exact .present (by simp only [SourceCoreCompatibleValues.defaultValue?, computed, Option.bind_some, projected]) shaped

/-- The existing independent relation at the actual boundary registry closes
all structural requirements of the public output codec. -/
theorem ValueRep.output {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {native : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source native type) :
    SourceCorePublicOutputShapes.Output checked registry world ambient.definitions sourceType native :=
  (represents_shape related).1

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleEqualityEncoding
/-! Public compatible encoding receipts feed real generated comparators.
The second encoding may extend the registry; the first value is transported
through that authenticated extension before the comparison proof is used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceCoreCompatibleDataEquality DataEquality CompatiblePayload

 theorem encoded_compare_run {fuel : Nat} {context : SourceCoreCompatibleValues.Context}
    (prepared : Prepared context.checked)
    {left right : SourceCoreDataValues.Value} {sourceLeft sourceRight : Dynamic.Value}
    {encodedLeft : SourceCoreCompatibleValues.Encoded fuel context prepared.sourceType left}
    {encodedRight : SourceCoreCompatibleValues.Encoded fuel encodedLeft.context prepared.sourceType right}
    (leftAccepted : SourceCoreCompatibleValues.encode fuel context prepared.sourceType left = .ok encodedLeft)
    (rightAccepted : SourceCoreCompatibleValues.encode fuel encodedLeft.context prepared.sourceType right = .ok encodedRight)
    (leftMeaning : CompatibleEncoding.Means left sourceLeft) (rightMeaning : CompatibleEncoding.Means right sourceRight)
    {functions : FunctionModel context.checked.catalog} {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) (functionLeaves : FunctionObservations context.checked.catalog functions identities)
    (mapping : GeneralHeap.LocationMap) (world : StoreTyping) (environment : Environment) (store : Store)
    (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression encodedLeft.value)
    (rightSelected : Selects environment rightExpression encodedRight.value) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      (∃ required, ∀ budget, required ≤ budget →
        runStateful budget (.initial (comparison prepared leftExpression rightExpression) environment store) =
          .done (.bool result) (preparedStore prepared environment store)) ∧
      (∀ budget actual actualStore,
        runStateful budget (.initial (comparison prepared leftExpression rightExpression) environment store) = .done actual actualStore →
          actual = .bool result ∧ actualStore = preparedStore prepared environment store) := by
  have first := CompatibleEncoding.encode_represents_at (functions := functions) leftAccepted leftMeaning mapping world
  have second := CompatibleEncoding.encode_represents_at (context := encodedLeft.context) (functions := functions) rightAccepted rightMeaning mapping world
  have first := first.extend encodedRight.preserves (.refl mapping) (.refl world)
  have firstType := Except.ok.inj (encodedLeft.projected.symm.trans prepared.projection)
  have secondType := Except.ok.inj (encodedRight.projected.symm.trans prepared.projection)
  rw [firstType] at first
  rw [secondType] at second
  exact represented_compare_run prepared faithful functionLeaves first second environment store _ _ leftSelected rightSelected

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
end
