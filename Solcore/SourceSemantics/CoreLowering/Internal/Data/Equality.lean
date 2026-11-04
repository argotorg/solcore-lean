import Solcore.Frontend.SourceCoreDataEquality
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.Core.Correspondence
import Solcore.Core.Renaming

/-!
# Data: equality

Generated data equality, its installation and initialization.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEquality
/-! Finite comparison certificates for the generated Core templates. The
certificate follows the compared finite values, including recursive nominal
payloads. Installed helper references and exact source metadata are explicit;
no source evaluator or equality-result evaluation is assumed. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.DataEquality

open Core Frontend
open SourceCoreDataEquality

/-- Projection paths used by generated comparison code. Their values are
independent of the heap, including when shifted under payload binders. -/
inductive Selects (environment : Environment) : Expr → Value → Prop where
  | var {index : Nat} {value : Value} (found : environment[index]? = some value) :
      Selects environment (.var index) value
  | first {expression : Expr} {left right : Value}
      (pair : Selects environment expression (.pair left right)) : Selects environment (.first expression) left
  | second {expression : Expr} {left right : Value}
      (pair : Selects environment expression (.pair left right)) : Selects environment (.second expression) right

 theorem Selects.evaluates {environment : Environment} {expression : Expr} {value : Value}
    (selected : Selects environment expression value) (store : Store) :
    Evaluates environment store expression value store := by
  induction selected with
  | var found => exact .var found
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih

 theorem Selects.weaken {environment : Environment} {expression : Expr} {value : Value}
    (selected : Selects environment expression value) (inserted : Value) :
    Selects (inserted :: environment) (expression.weakenAt 0) value := by
  induction selected with
  | @var index value found =>
    simpa [Expr.weakenAt] using (Selects.var (environment := inserted :: environment)
      (index := index + 1) (value := value) (by simpa using found))
  | first _ ih => simpa [Expr.weakenAt] using Selects.first ih
  | second _ ih => simpa [Expr.weakenAt] using Selects.second ih

/-- An identity assignment must retain the entire source global/evidence or
builtin identity. A bare code pointer is insufficient. -/
structure IdentityFaithful (identities : Dynamic.Value → Word → Prop) : Prop where
  comparable : ∀ {source identity}, identities source identity → Dynamic.ValueComparable source
  equal : ∀ {left right leftId rightId}, identities left leftId → identities right rightId →
    (leftId = rightId ↔ left = right)

theorem product_equivalent {a b c d : Dynamic.Value} :
    Dynamic.ValueEquivalent (.product a b) (.product c d) ↔
      Dynamic.ValueEquivalent a c ∧ Dynamic.ValueEquivalent b d := by
  constructor
  · rintro ⟨same, comparable⟩
    cases same
    cases comparable with
    | product left right => exact ⟨⟨rfl, left⟩, ⟨rfl, right⟩⟩
  · rintro ⟨⟨rfl, left⟩, ⟨rfl, right⟩⟩
    exact ⟨rfl, .product left right⟩

theorem pack_comparable {values : List Dynamic.Value} {packed : Dynamic.Value}
    (packing : Dynamic.ValuesPack values packed) :
    Dynamic.ValueComparable packed ↔ ∀ value, value ∈ values → Dynamic.ValueComparable value := by
  induction packing with
  | nil => simp; exact .unit
  | singleton value => simp
  | @cons first second rest packed tail ih =>
    constructor
    · intro comparable
      cases comparable with
      | product left right =>
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact left
        · exact ih.mp right value member
    · intro all
      exact .product (all _ (by simp)) (ih.mpr (by
        intro value member
        exact all value (List.mem_cons_of_mem first member)))

theorem pack_equivalent {left right : List Dynamic.Value} {leftPacked rightPacked : Dynamic.Value}
    (leftPack : Dynamic.ValuesPack left leftPacked) (rightPack : Dynamic.ValuesPack right rightPacked)
    (arity : left.length = right.length) :
    Dynamic.ValueEquivalent leftPacked rightPacked ↔ Dynamic.ValuesEquivalent left right := by
  constructor
  · rintro ⟨same, comparable⟩
    subst rightPacked
    exact ⟨leftPack.injective_of_length_eq rightPack arity, (pack_comparable leftPack).mp comparable⟩
  · rintro ⟨rfl, comparable⟩
    exact ⟨leftPack.functional rightPack, (pack_comparable leftPack).mpr comparable⟩

/-- Rules carry actual generated branch lookups and helper-store lookups.
Metadata equality and the identity assignment are source representation facts,
not consequences of Core type checking alone. -/
inductive Tree (identities : Dynamic.Value → Word → Prop) (store : Store) :
    Environment → Expr → Dynamic.Value → Dynamic.Value → Bool → Prop where
  | unit {environment : Environment} : Tree identities store environment (.bool true) .unit .unit true
  | bool {environment : Environment} {left right : Expr} {a b : Bool}
      (leftSelected : Selects environment left (.bool a))
      (rightSelected : Selects environment right (.bool b)) :
      Tree identities store environment (.ifE left right (.unary .boolNot right)) (.bool a) (.bool b) (a == b)
  | word {environment : Environment} {left right : Expr} {a b : Word}
      (leftSelected : Selects environment left (.word a))
      (rightSelected : Selects environment right (.word b)) :
      Tree identities store environment (.binary .wordEq left right) (.word a) (.word b) (a == b)
  | integer {environment : Environment} {left right : Expr} {a b : Int}
      (leftSelected : Selects environment left (.integer a))
      (rightSelected : Selects environment right (.integer b)) :
      Tree identities store environment (.binary .integerEq left right) (.integer a) (.integer b) (a == b)
  | product {environment : Environment} {left right : Expr} {a b c d : Dynamic.Value} {first second : Bool}
      (firstTree : Tree identities store environment left a c first)
      (secondTree : Tree identities store environment right b d second) :
      Tree identities store environment (.ifE left right (.bool false)) (.product a b) (.product c d) (first && second)
  | proxy {environment : Environment} (inner : TypeSystem.Ty) :
      Tree identities store environment (.bool true) (.proxy inner) (.proxy inner) true
  | mapping {environment : Environment} (leftKey leftValue rightKey rightValue : TypeSystem.Ty)
      (left right : List (Dynamic.Value × Dynamic.Value)) :
      Tree identities store environment (.bool false)
        (.mapping leftKey leftValue left) (.mapping rightKey rightValue right) false
  | identified {environment : Environment} {left right : Expr} {leftCode rightCode : Value}
      {leftSource rightSource : Dynamic.Value} {leftId rightId : Word}
      (leftMeaning : identities leftSource leftId) (rightMeaning : identities rightSource rightId)
      (leftSelected : Selects environment left (.pair (.inRight .unit (.word leftId)) leftCode))
      (rightSelected : Selects environment right (.pair (.inRight .unit (.word rightId)) rightCode)) :
      Tree identities store environment (functionEqual left right) leftSource rightSource (leftId == rightId)
  | anonymousLeft {environment : Environment} {left right : Expr} {leftCode rightCode rightIdentity : Value}
      (leftSource : Dynamic.Closure) (rightSource : Dynamic.Value)
      (leftSelected : Selects environment left (.pair (.inLeft .word .unit) leftCode))
      (rightSelected : Selects environment right (.pair rightIdentity rightCode)) :
      Tree identities store environment (functionEqual left right) (.closure leftSource) rightSource false
  | anonymousRight {environment : Environment} {left right : Expr} {leftCode rightCode : Value} {leftId : Word}
      (leftSource : Dynamic.Value) (rightSource : Dynamic.Closure)
      (leftSelected : Selects environment left (.pair (.inRight .unit (.word leftId)) leftCode))
      (rightSelected : Selects environment right (.pair (.inLeft .word .unit) rightCode)) :
      Tree identities store environment (functionEqual left right) leftSource (.closure rightSource) false
  | invoke {environment captured : Environment} {reference left right body : Expr}
      {leftValue rightValue : Value} {location : Nat} {type : Core.Ty} {a b : Dynamic.Value} {result : Bool}
      (referenceSelected : Selects environment reference
        (.cellRef (OptionalCell.cellType (comparatorType type)) location))
      (leftSelected : Selects environment left leftValue)
      (rightSelected : Selects environment right rightValue)
      (installed : store[location]? = some (.inRight .unit (.closure (.product type type) .bool body captured)))
      (comparison : Tree identities store (.pair leftValue rightValue :: captured) body a b result) :
      Tree identities store environment (SourceCoreDataEquality.invoke reference left right) a b result
  | nominalSame {environment : Environment} {left right : Expr} {branches rightBranches : List Expr} {body : Expr}
      {id : DataTypeId} {index : Nat} {leftPayload rightPayload : Value}
      (instantiation : SourceInference.DataConstructorInstantiation)
      {leftArguments rightArguments : List Dynamic.Value} {leftPacked rightPacked : Dynamic.Value} {result : Bool}
      (leftSelected : Selects environment left (.constructed ⟨id, index⟩ leftPayload))
      (rightSelected : Selects environment right (.constructed ⟨id, index⟩ rightPayload))
      (leftBranch : branches[index]? = some (.matchData id .bool (right.weakenAt 0) rightBranches))
      (rightBranch : rightBranches[index]? = some body)
      (leftPack : Dynamic.ValuesPack leftArguments leftPacked)
      (rightPack : Dynamic.ValuesPack rightArguments rightPacked)
      (arity : leftArguments.length = rightArguments.length)
      (payload : Tree identities store (rightPayload :: leftPayload :: environment) body leftPacked rightPacked result) :
      Tree identities store environment (.matchData id .bool left branches)
        (.constructed instantiation leftArguments) (.constructed instantiation rightArguments) result
  | nominalDifferent {environment : Environment} {left right : Expr} {branches rightBranches : List Expr}
      {id : DataTypeId} {leftIndex rightIndex : Nat} {leftPayload rightPayload : Value}
      (leftInstantiation rightInstantiation : SourceInference.DataConstructorInstantiation)
      (leftArguments rightArguments : List Dynamic.Value)
      (distinct : leftInstantiation ≠ rightInstantiation)
      (leftSelected : Selects environment left (.constructed ⟨id, leftIndex⟩ leftPayload))
      (rightSelected : Selects environment right (.constructed ⟨id, rightIndex⟩ rightPayload))
      (leftBranch : branches[leftIndex]? = some (.matchData id .bool (right.weakenAt 0) rightBranches))
      (rightBranch : rightBranches[rightIndex]? = some (.bool false)) :
      Tree identities store environment (.matchData id .bool left branches)
        (.constructed leftInstantiation leftArguments) (.constructed rightInstantiation rightArguments) false

theorem Tree.meaning {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {store : Store} {environment : Environment} {expression : Expr} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    result = true ↔ Dynamic.ValueEquivalent left right := by
  induction tree with
  | unit => exact ⟨fun _ => ⟨rfl, .unit⟩, fun _ => rfl⟩
  | bool | word | integer =>
    constructor
    · intro same
      have same := beq_iff_eq.mp same
      subst_vars
      exact ⟨rfl, by constructor⟩
    · rintro ⟨same, _⟩
      cases same
      simp
  | product _ _ left right => simpa [Bool.and_eq_true, product_equivalent] using and_congr left right
  | proxy inner => exact ⟨fun _ => ⟨rfl, .proxy inner⟩, fun _ => rfl⟩
  | mapping => constructor <;> intro impossible
               · cases impossible
               · cases impossible.2
  | identified leftMeaning rightMeaning _ _ =>
    constructor
    · intro same
      exact ⟨(faithful.equal leftMeaning rightMeaning).mp (beq_iff_eq.mp same), faithful.comparable leftMeaning⟩
    · intro equivalent
      exact beq_iff_eq.mpr ((faithful.equal leftMeaning rightMeaning).mpr equivalent.1)
  | anonymousLeft => constructor <;> intro impossible
                     · cases impossible
                     · cases impossible.2
  | anonymousRight => constructor <;> intro impossible
                      · cases impossible
                      · cases impossible.comparable_right
  | invoke _ _ _ _ _ ih => exact ih
  | nominalSame instantiation _ _ _ _ leftPack rightPack arity _ ih =>
    rw [ih, pack_equivalent leftPack rightPack arity]
    constructor
    · rintro ⟨rfl, comparable⟩
      exact ⟨rfl, .constructed instantiation _ comparable⟩
    · rintro ⟨same, comparable⟩
      cases same
      cases comparable with
      | constructed _ _ comparable => exact ⟨rfl, comparable⟩
  | nominalDifferent _ _ _ _ distinct _ _ _ _ =>
    constructor
    · intro impossible; cases impossible
    · intro equivalent
      exact False.elim (distinct (Dynamic.Value.constructed.inj equivalent.1).1)

theorem Tree.evaluates {identities : Dynamic.Value → Word → Prop}
    {store : Store} {environment : Environment} {expression : Expr} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    Evaluates environment store expression (.bool result) store := by
  induction tree with
  | unit | proxy | mapping => exact .bool
  | @bool environment left right a b leftSelected rightSelected =>
    cases a <;> cases b
    · exact .ifFalse (leftSelected.evaluates store) (.unary (rightSelected.evaluates store) rfl)
    · exact .ifFalse (leftSelected.evaluates store) (.unary (rightSelected.evaluates store) rfl)
    · exact .ifTrue (leftSelected.evaluates store) (rightSelected.evaluates store)
    · exact .ifTrue (leftSelected.evaluates store) (rightSelected.evaluates store)
  | word left right | integer left right => exact .binary (left.evaluates store) (right.evaluates store) rfl
  | @product environment left right a b c d first second _ _ leftIH rightIH =>
    cases first
    · exact .ifFalse leftIH .bool
    · exact .ifTrue leftIH rightIH
  | identified _ _ left right =>
    exact .letE (left.evaluates store) (.letE ((right.weaken _).evaluates store) TaggedFunction.equalBody_identified)
  | anonymousLeft _ _ left right =>
    exact .letE (left.evaluates store) (.letE ((right.weaken _).evaluates store) TaggedFunction.equalBody_anonymous_left)
  | anonymousRight _ _ left right =>
    exact .letE (left.evaluates store) (.letE ((right.weaken _).evaluates store) TaggedFunction.equalBody_anonymous_right)
  | invoke reference left right installed _ ih =>
    exact .caseRight (.loadCell (reference.evaluates store) installed)
      (.apply (.var rfl) (.pair ((left.weaken _).evaluates store) ((right.weaken _).evaluates store)) ih)
  | nominalSame _ left right leftBranch rightBranch _ _ _ _ ih =>
    exact .matchData (left.evaluates store) rfl leftBranch
      (.matchData ((right.weaken _).evaluates store) rfl rightBranch ih)
  | nominalDifferent _ _ _ _ _ left right leftBranch rightBranch =>
    exact .matchData (left.evaluates store) rfl leftBranch
      (.matchData ((right.weaken _).evaluates store) rfl rightBranch .bool)

/-- The equation authenticates the actual generator output; the certificate
and installed store establish finite, pure execution over represented values. -/
theorem compareType_run_preserves {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities) {fuel depth : Nat} {catalog : Catalog} {type : Core.Ty}
    {leftExpression rightExpression expression : Expr}
    (compiled : compareType fuel catalog depth type leftExpression rightExpression = .ok expression)
    {store : Store} {environment : Environment} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store environment expression left right result) :
    (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      ∃ required, ∀ budget, required ≤ budget →
        runStateful budget (State.initial expression environment store) = .done (.bool result) store := by
  have _ := compiled
  exact ⟨tree.meaning faithful, evaluation_runStateful_complete_with_sufficient_fuel tree.evaluates⟩

/-- Directly supplies OrderedMapping's pure-comparator premise in the actual
installed store, which may already contain that mapping helper's admin cell. -/
theorem Tree.compares {identities : Dynamic.Value → Word → Prop} {store : Store}
    (layout : OrderedMapping.Layout) {captured : Environment} {body : Expr}
    {leftValue rightValue : Value} {left right : Dynamic.Value} {result : Bool}
    (tree : Tree identities store (.pair leftValue rightValue :: captured) body left right result) :
    OrderedMapping.Compares layout
      (.closure (.product layout.keyType layout.keyType) .bool body captured)
      leftValue rightValue result store :=
  ⟨body, captured, rfl, tree.evaluates⟩

end Solcore.SourceSemantics.CoreLowering.DataEquality
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
/-! Equality preparation only allocates cells and installs suspended closures.
This finite fragment theorem establishes termination of that actual generated
initializer, even when the closures are mutually recursive. It does not yet
identify each installed helper with its source comparison certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
open Core Frontend SourceCoreDataEquality

/-- Suspended lambda bodies need not terminate. No function application is
executed while preparing the comparison closures. -/
inductive Initializer : Expr → Prop where
  | unit : Initializer .unit
  | var (index : Nat) : Initializer (.var index)
  | lambda (parameter result : Ty) (body : Expr) : Initializer (.lambda parameter result body)
  | inLeft {right : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.inLeft right payload)
  | inRight {left : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.inRight left payload)
  | newCell {type : Ty} {payload : Expr} (child : Initializer payload) : Initializer (.newCell type payload)
  | storeCell {reference value : Expr} (first : Initializer reference) (second : Initializer value) :
      Initializer (.storeCell reference value)
  | letE {value body : Expr} (first : Initializer value) (second : Initializer body) : Initializer (.letE value body)

theorem Initializer.rename {expression : Expr} (initializing : Initializer expression) (mapping : Renaming) :
    Initializer (expression.rename mapping) := by
  induction initializing generalizing mapping with
  | unit => exact .unit
  | var => exact .var _
  | lambda => exact .lambda _ _ _
  | inLeft _ ih => exact .inLeft (ih mapping)
  | inRight _ ih => exact .inRight (ih mapping)
  | newCell _ ih => exact .newCell (ih mapping)
  | storeCell _ _ left right => exact .storeCell (left mapping) (right mapping)
  | letE _ _ first second => exact .letE (first mapping) (second mapping.lift)

theorem Initializer.weakenAt {expression : Expr} (initializing : Initializer expression) (cutoff : Nat) :
    Initializer (expression.weakenAt cutoff) := by
  rw [← Expr.rename_insertion]
  exact initializing.rename _

/-- Structural termination uses runtime store typing between effects, so it
also admits cells containing closures, cells and recursive references. -/
theorem Initializer.evaluates {expression : Expr} (initializing : Initializer expression)
    {definitions : DataEnvironment} {context : Core.Context} {type : Ty} {environment : Environment}
    {world : StoreTyping} {store : Store} (typed : HasType context expression type definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyped : RuntimeStoreHasTypes world store definitions) :
    ∃ value finalStore, Evaluates environment store expression value finalStore := by
  induction initializing generalizing context type environment world store with
  | unit => exact ⟨_, _, .unit⟩
  | var index =>
    cases typed with
    | var found => obtain ⟨value, lookup, _⟩ := environmentTyped.lookup found; exact ⟨value, store, .var lookup⟩
  | lambda => exact ⟨_, _, .lambda⟩
  | inLeft child ih =>
    cases typed with
    | inLeft _ childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .inLeft evaluated⟩
  | inRight child ih =>
    cases typed with
    | inRight _ childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .inRight evaluated⟩
  | newCell child ih =>
    cases typed with
    | newCell childTyped => obtain ⟨value, finalStore, evaluated⟩ := ih childTyped environmentTyped storeTyped; exact ⟨_, _, .newCell evaluated⟩
  | storeCell first second firstIH secondIH =>
    cases typed with
    | storeCell referenceTyped valueTyped =>
      obtain ⟨reference, referenceStore, referenceEvaluated⟩ := firstIH referenceTyped environmentTyped storeTyped
      obtain ⟨referenceWorld, extension, referenceStoreTyped, referenceValueTyped⟩ :=
        evaluation_preserves_type referenceEvaluated referenceTyped environmentTyped storeTyped
      cases referenceValueTyped with
      | cellRef worldLookup =>
        obtain ⟨old, oldRead, _⟩ := referenceStoreTyped.read worldLookup
        obtain ⟨value, valueStore, valueEvaluated⟩ := secondIH valueTyped (environmentTyped.weaken extension) referenceStoreTyped
        obtain ⟨valueWorld, valueExtends, valueStoreTyped, _⟩ :=
          evaluation_preserves_type valueEvaluated valueTyped (environmentTyped.weaken extension) referenceStoreTyped
        obtain ⟨finalStore, written⟩ := (Store.write?_success_iff _ _ value).mpr
          (valueStoreTyped.location_lt (valueExtends.lookup worldLookup))
        exact ⟨_, _, .storeCell referenceEvaluated oldRead valueEvaluated written⟩
  | letE first second firstIH secondIH =>
    cases typed with
    | letE firstTyped secondTyped =>
      obtain ⟨value, middleStore, firstEvaluated⟩ := firstIH firstTyped environmentTyped storeTyped
      obtain ⟨middleWorld, extension, middleStoreTyped, valueTyped⟩ :=
        evaluation_preserves_type firstEvaluated firstTyped environmentTyped storeTyped
      obtain ⟨result, finalStore, bodyEvaluated⟩ := secondIH secondTyped
        (.cons valueTyped (environmentTyped.weaken extension)) middleStoreTyped
      exact ⟨result, finalStore, .letE firstEvaluated bodyEvaluated⟩

private theorem install_initializes (catalog : Catalog) (bodies : List Expr) {next : Expr}
    (initialized : Initializer next) : Initializer (install catalog bodies next) := by
  unfold install
  generalize bodies.zipIdx = rows
  induction rows with
  | nil => exact initialized
  | cons row rows ih =>
    exact .letE (.storeCell (.var _) (.inRight (.lambda _ _ _))) (ih.weakenAt 0)

private theorem allocate_initializes (catalog : Catalog) {next : Expr} (initialized : Initializer next) :
    Initializer (allocate catalog next) := by
  unfold allocate
  generalize catalog.entries.zipIdx = rows
  induction rows with
  | nil => exact initialized
  | cons row rows ih => exact .letE (.newCell (.inLeft .unit)) ih

theorem prepared_initializes {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked) :
    Initializer prepared.expression := by
  rw [prepared.expression_eq]
  exact allocate_initializes _ (install_initializes _ _ (.lambda _ _ _))

/-- Actual prepared code executes finitely in any aligned ambient environment
and store. Returned closure syntax and captured values are the machine's real
result, including administrative binders introduced during installation. -/
theorem prepared_evaluates {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured finalStore finalWorld,
      Evaluates environment store prepared.expression
        (.closure (.product prepared.type prepared.type) .bool body captured) finalStore ∧
      WorldExtends world finalWorld ∧ RuntimeStoreHasTypes finalWorld finalStore checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions := by
  have typed : HasType context prepared.expression (comparatorType prepared.type) checked.catalog.definitions := by
    have respect : Renaming.Respects Renaming.id [] context := by intro index type found; simp at found
    simpa using prepared.typed.rename respect
  obtain ⟨value, finalStore, evaluated⟩ := (prepared_initializes prepared).evaluates typed environmentTyped storeTyped
  obtain ⟨finalWorld, extension, finalStoreTyped, resultTyped⟩ :=
    evaluation_preserves_type evaluated typed environmentTyped storeTyped
  cases resultTyped with
  | closure capturedTyped bodyTyped =>
    exact ⟨_, _, finalStore, finalWorld, evaluated, extension, finalStoreTyped, .closure capturedTyped bodyTyped⟩

theorem prepared_run {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured finalStore finalWorld,
      WorldExtends world finalWorld ∧ RuntimeStoreHasTypes finalWorld finalStore checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression environment store) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) finalStore) ∧
      (∀ fuel actual actualStore,
        runStateful fuel (.initial prepared.expression environment store) = .done actual actualStore →
        actual = .closure (.product prepared.type prepared.type) .bool body captured ∧ actualStore = finalStore) := by
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, resultTyped⟩ :=
    prepared_evaluates prepared environmentTyped storeTyped
  exact ⟨body, captured, finalStore, finalWorld, extension, storeTyped, resultTyped,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

/-- Count allocation effects in the initialization fragment. Suspended lambda
bodies do not contribute effects. -/
def allocations : Expr → Nat
  | .newCell _ initializer => allocations initializer + 1
  | .letE value body | .storeCell value body => allocations value + allocations body
  | .inLeft _ value | .inRight _ value => allocations value
  | _ => 0

private theorem Initializer.allocations_rename {expression : Expr} (initializing : Initializer expression)
    (mapping : Renaming) : allocations (expression.rename mapping) = allocations expression := by
  induction initializing generalizing mapping with
  | unit | var | lambda => rfl
  | inLeft _ ih | inRight _ ih | newCell _ ih => simpa [Expr.rename, allocations] using ih mapping
  | storeCell _ _ left right => simp [Expr.rename, allocations, left mapping, right mapping]
  | letE _ _ first second => simp [Expr.rename, allocations, first mapping, second mapping.lift]

private theorem Initializer.allocations_weaken {expression : Expr} (initializing : Initializer expression)
    (cutoff : Nat) : allocations (expression.weakenAt cutoff) = allocations expression := by
  rw [← Expr.rename_insertion]
  exact initializing.allocations_rename _

/-- Every successful initializer execution has precisely its syntactic
allocation count; stores are allowed to grow and contain recursive closures. -/
theorem Initializer.evaluation_length {expression : Expr} (initializing : Initializer expression)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore expression value finalStore) :
    finalStore.length = initialStore.length + allocations expression := by
  induction initializing generalizing environment initialStore finalStore value with
  | unit | var | lambda => cases evaluated; simp [allocations]
  | inLeft child ih => cases evaluated with
    | inLeft payload => exact ih payload
  | inRight child ih => cases evaluated with
    | inRight payload => exact ih payload
  | newCell child ih => cases evaluated with
    | newCell payload => simp [allocations, List.length_append, ih payload, Nat.add_assoc]
  | storeCell first second firstIH secondIH => cases evaluated with
    | storeCell reference _ value written =>
      have left := firstIH reference
      have right := secondIH value
      have same := Store.write?_preserves_length written
      simp only [allocations]
      omega
  | letE first second firstIH secondIH => cases evaluated with
    | letE initial body =>
      have left := firstIH initial
      have right := secondIH body
      simp only [allocations]
      omega

private theorem install_count (catalog : Catalog) (bodies : List Expr) {next : Expr}
    (initialized : Initializer next) : allocations (install catalog bodies next) = allocations next := by
  unfold install
  generalize bodies.zipIdx = rows
  suffices ∀ rows : List (Expr × Nat),
      Initializer (rows.foldr (fun (body, index) next =>
        .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
          (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
          (next.weakenAt 0)) next) ∧
      allocations (rows.foldr (fun (body, index) next =>
        .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
          (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
          (next.weakenAt 0)) next) = allocations next by exact (this rows).2
  intro rows
  induction rows with
  | nil => exact ⟨initialized, rfl⟩
  | cons row rows ih =>
    refine ⟨.letE (.storeCell (.var _) (.inRight (.lambda _ _ _))) (ih.1.weakenAt 0), ?_⟩
    simp only [List.foldr_cons, allocations, Nat.zero_add, ih.1.allocations_weaken, ih.2]

private theorem allocate_count (catalog : Catalog) (next : Expr) :
    allocations (allocate catalog next) = catalog.entries.length + allocations next := by
  unfold allocate
  have count : catalog.entries.zipIdx.length = catalog.entries.length := by simp
  generalize catalog.entries.zipIdx = rows at *
  rw [← count]
  clear count
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.foldr_cons, List.length_cons, OptionalCell.allocate, allocations] at ih ⊢
    omega

/-- Preparation allocates exactly one administrative cell for each catalog
entry. Installation changes those cells without allocating more cells. -/
theorem prepared_allocation_count {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked) :
    allocations prepared.expression = checked.catalog.entries.length := by
  rw [prepared.expression_eq, allocate_count, install_count _ _ (.lambda _ _ _)]
  simp [allocations]

theorem prepared_evaluation_length {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    finalStore.length = initialStore.length + checked.catalog.entries.length := by
  simpa only [prepared_allocation_count] using (prepared_initializes prepared).evaluation_length evaluated

end Solcore.SourceSemantics.CoreLowering.DataEqualityInitialization
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore
/-! Store confinement for actual comparison initialization. Closure bodies and
captured values remain suspended, so only directly accessible reference values
can authorize a write. This requires no acyclic traversal of closure heaps. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore
open Core Frontend SourceCoreDataEquality DataEqualityInitialization

/-- Direct references visible to the initializer point at administrative
cells. Closures need no condition on their suspended captured environments. -/
def ReferenceAbove (boundary : Nat) (value : Value) : Prop :=
  ∀ type location, value = .cellRef type location → boundary ≤ location

/-- Typing restricts accessible variable indices; inaccessible ambient values
need no condition, in particular when the initializer has closed Core type. -/
def AccessibleReferencesAbove (boundary : Nat) (context : Core.Context) (environment : Environment) : Prop :=
  ∀ (index : Nat) (type : Ty) (value : Value), context[index]? = some type → environment[index]? = some value → ReferenceAbove boundary value

/-- Administrative writes and allocations preserve every preexisting slot. -/
def PrefixPreserved (boundary : Nat) (initial final : Store) : Prop :=
  ∀ location, location < boundary → final.read? location = initial.read? location

private theorem PrefixPreserved.refl (boundary : Nat) (store : Store) : PrefixPreserved boundary store store :=
  fun _ _ => rfl
private theorem PrefixPreserved.trans {boundary : Nat} {first middle last : Store}
    (left : PrefixPreserved boundary first middle) (right : PrefixPreserved boundary middle last) :
    PrefixPreserved boundary first last := fun location bound => (right location bound).trans (left location bound)

private theorem references_cons {boundary : Nat} {context : Core.Context} {environment : Environment}
    {value : Value} {type : Ty} (head : ReferenceAbove boundary value)
    (tail : AccessibleReferencesAbove boundary context environment) :
    AccessibleReferencesAbove boundary (type :: context) (value :: environment) := by
  intro index selected actual typed found
  cases index with
  | zero => cases typed; cases found; exact head
  | succ index => exact tail index selected actual typed found

/-- This finite fragment cannot reach a preexisting cell through a suspended
closure. Every actual write target comes from a checked accessible variable or
a fresh allocation, and the proof follows its real evaluation. -/
theorem Initializer.preserves_prefix {expression : Expr} (initializing : Initializer expression)
    {definitions : DataEnvironment} {context : Core.Context} {type : Ty} {environment : Environment}
    {boundary : Nat} {initialStore finalStore : Store} {value : Value}
    (typed : HasType context expression type definitions)
    (accessible : AccessibleReferencesAbove boundary context environment)
    (inBounds : boundary ≤ initialStore.length)
    (evaluated : Evaluates environment initialStore expression value finalStore) :
    ReferenceAbove boundary value ∧ PrefixPreserved boundary initialStore finalStore := by
  induction initializing generalizing context type environment initialStore finalStore value with
  | unit => cases evaluated; exact ⟨(by intro _ _ impossible; cases impossible), PrefixPreserved.refl _ _⟩
  | var index =>
    cases typed with
    | var found => cases evaluated with
      | var read => exact ⟨accessible index _ _ found read, PrefixPreserved.refl _ _⟩
  | lambda => cases evaluated; exact ⟨(by intro _ _ impossible; cases impossible), PrefixPreserved.refl _ _⟩
  | inLeft child ih =>
    cases typed with
    | inLeft _ childTyped => cases evaluated with
      | inLeft childEvaluated =>
        exact ⟨(by intro _ _ impossible; cases impossible), (ih childTyped accessible inBounds childEvaluated).2⟩
  | inRight child ih =>
    cases typed with
    | inRight _ childTyped => cases evaluated with
      | inRight childEvaluated =>
        exact ⟨(by intro _ _ impossible; cases impossible), (ih childTyped accessible inBounds childEvaluated).2⟩
  | newCell child ih =>
    cases typed with
    | newCell childTyped => cases evaluated with
      | newCell childEvaluated =>
        have childBounds := Nat.le_trans inBounds (evaluation_store_length_monotone childEvaluated)
        refine ⟨?_, ?_⟩
        · intro type location same
          cases same
          exact childBounds
        · intro location bound
          have current := (ih childTyped accessible inBounds childEvaluated).2 location bound
          apply Eq.trans ?_ current
          apply Store.allocate_old_lookup
          exact Nat.lt_of_lt_of_le bound childBounds
  | storeCell first second firstIH secondIH =>
    cases typed with
    | storeCell firstTyped secondTyped => cases evaluated with
      | storeCell referenceRead oldRead valueRead written =>
        obtain ⟨referenceAbove, referencePrefix⟩ := firstIH firstTyped accessible inBounds referenceRead
        have targetAbove := referenceAbove _ _ rfl
        obtain ⟨_, valuePrefix⟩ := secondIH secondTyped accessible
          (Nat.le_trans inBounds (evaluation_store_length_monotone referenceRead)) valueRead
        refine ⟨(by intro _ _ impossible; cases impossible), ?_⟩
        intro location bound
        apply Eq.trans ?_ ((valuePrefix location bound).trans (referencePrefix location bound))
        exact Store.write?_preserves_other written (Nat.ne_of_lt (Nat.lt_of_lt_of_le bound targetAbove))
  | letE first second firstIH secondIH =>
    cases typed with
    | letE firstTyped secondTyped => cases evaluated with
      | letE firstEvaluated bodyEvaluated =>
        obtain ⟨valueAbove, firstPrefix⟩ := firstIH firstTyped accessible inBounds firstEvaluated
        obtain ⟨resultAbove, bodyPrefix⟩ := secondIH secondTyped (references_cons valueAbove accessible)
          (Nat.le_trans inBounds (evaluation_store_length_monotone firstEvaluated)) bodyEvaluated
        exact ⟨resultAbove, firstPrefix.trans bodyPrefix⟩

/-- Closed prepared code cannot write through an ambient reference, even when
the caller's environment contains references into the preexisting store. -/
theorem prepared_preserves_prefix {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    PrefixPreserved initialStore.length initialStore finalStore := by
  have accessible : AccessibleReferencesAbove initialStore.length [] environment := by
    intro index type value found
    simp at found
  exact (Initializer.preserves_prefix (prepared_initializes prepared) prepared.typed accessible (Nat.le_refl _) evaluated).2

/-- The actual initializer extends the store with exactly the catalog's helper
cells and leaves the complete source-visible prefix unchanged. -/
theorem prepared_store_extension {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {initialStore finalStore : Store} {value : Value}
    (evaluated : Evaluates environment initialStore prepared.expression value finalStore) :
    ∃ administrative, finalStore = initialStore ++ administrative ∧ administrative.length = checked.catalog.entries.length := by
  have preserved :=  prepared_preserves_prefix prepared evaluated
  have length := prepared_evaluation_length prepared evaluated
  refine ⟨finalStore.drop initialStore.length, ?_, ?_⟩
  · have take : finalStore.take initialStore.length = initialStore := by
      apply List.ext_getElem?
      intro index
      by_cases bound : index < initialStore.length
      · simp only [List.getElem?_take, bound, ↓reduceIte]
        exact preserved index bound
      · simp [List.getElem?_take, bound]
    exact (List.take_append_drop initialStore.length finalStore).symm.trans
      (congrArg (fun head => head ++ finalStore.drop initialStore.length) take)
  · simp only [List.length_drop]
    omega

/-- Preparation returns its real closure and appends a precisely sized
administrative suffix. Resumption/completion can retain the original source
heap representation because every existing slot remains byte-for-byte equal. -/
theorem prepared_run_extends {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {context : Core.Context} {store : Store} {world : StoreTyping}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions) :
    ∃ body captured administrative finalWorld,
      administrative.length = checked.catalog.entries.length ∧ WorldExtends world finalWorld ∧
      RuntimeStoreHasTypes finalWorld (store ++ administrative) checked.catalog.definitions ∧
      RuntimeValueHasType finalWorld (.closure (.product prepared.type prepared.type) .bool body captured)
        (comparatorType prepared.type) checked.catalog.definitions ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (.initial prepared.expression environment store) =
          .done (.closure (.product prepared.type prepared.type) .bool body captured) (store ++ administrative)) ∧
      (∀ fuel actual actualStore,
        runStateful fuel (.initial prepared.expression environment store) = .done actual actualStore →
        actual = .closure (.product prepared.type prepared.type) .bool body captured ∧ actualStore = store ++ administrative) := by
  obtain ⟨body, captured, finalStore, finalWorld, evaluated, extension, storeTyped, valueTyped⟩ :=
    prepared_evaluates prepared environmentTyped storeTyped
  obtain ⟨administrative, rfl, length⟩ := prepared_store_extension prepared evaluated
  exact ⟨body, captured, administrative, finalWorld, length, extension, storeTyped, valueTyped,
    evaluation_runStateful_complete_with_sufficient_fuel evaluated,
    fun _ _ _ ran => evaluation_deterministic (runStateful_evaluation_sound ran) evaluated⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityInitializationStore
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
/-! Exact closure layout during comparison helper installation. Each preceding
write introduces a real Unit binder. The installed closure stores the shifted
body together with that actual captured environment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
open Core Frontend SourceCoreDataEquality

def offset (count : Nat) : Renaming := fun index => count + index

def captured (count : Nat) (environment : Environment) : Environment :=
  List.replicate count .unit ++ environment

def helper (environment : Environment) (body : Expr) (index : Nat) : Value :=
  .closure (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool
    (body.rename (offset index).lift) (captured index environment)

def cells (environment : Environment) (bodies : List Expr) (start : Nat := 0) : List Value :=
  (bodies.zipIdx start).map fun (body, index) => .inRight .unit (helper environment body index)

/-- All catalog references are allocated before any closure is installed. -/
def References (catalog : Catalog) (base : Nat) (environment : Environment) : Prop :=
  ∀ index, index < catalog.entries.length →
    environment[referenceIndex catalog 0 ⟨index⟩]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index))

private theorem captured_succ (count : Nat) (environment : Environment) :
    captured (count + 1) environment = .unit :: captured count environment := by
  simp [captured, List.replicate_succ]

private theorem offset_weaken (expression : Expr) (count : Nat) :
    (expression.weakenAt 0).rename (offset count).lift = expression.rename (offset (count + 1)) := by
  rw [← Expr.rename_insertion, Expr.rename_comp]
  congr 1
  funext index
  simp only [Renaming.comp, Renaming.insertion, Nat.zero_le, ↓reduceIte, Renaming.lift, offset]
  omega

private theorem captured_lookup {environment : Environment} {index count : Nat} {value : Value}
    (found : environment[index]? = some value) : (captured count environment)[count + index]? = some value := by
  simpa [captured, List.getElem?_append_right] using found

private theorem write_next (before previous remaining : Store) (old value : Value) :
    (before ++ previous ++ old :: remaining).write? (before.length + previous.length) value =
      some (before ++ previous ++ value :: remaining) := by
  have bound : before.length + previous.length < (before ++ previous ++ old :: remaining).length := by simp
  rw [Store.write?, if_pos bound]
  congr 1
  rw [List.set_append_right _ _ (by simp), List.length_append, Nat.sub_self]
  rfl

private def installRow (catalog : Catalog) (row : Expr × Nat) (next : Expr) : Expr :=
  .letE (.storeCell (.var (referenceIndex catalog 0 ⟨row.2⟩))
    (.inRight .unit (.lambda (.product (.namedData ⟨row.2⟩) (.namedData ⟨row.2⟩)) .bool row.1)))
    (next.weakenAt 0)

/-- Install an actual suffix of the generated rows. The relation specifies
both every stored closure and the final comparator's captured environment. -/
theorem install_evaluates_suffix (catalog : Catalog) (environment : Environment) (before : Store)
    (references : References catalog before.length environment)
    (remaining : List Expr) (count : Nat) (previous pending : Store)
    (previousLength : previous.length = count) (pendingLength : pending.length = remaining.length)
    (bounds : count + remaining.length ≤ catalog.entries.length)
    (parameter result : Ty) (body : Expr) :
    Evaluates (captured count environment) (before ++ previous ++ pending)
      (((remaining.zipIdx count).foldr (installRow catalog) (.lambda parameter result body)).rename (offset count))
      (.closure parameter result (body.rename (offset (count + remaining.length)).lift)
        (captured (count + remaining.length) environment))
      (before ++ previous ++ cells environment remaining count) := by
  induction remaining generalizing count previous pending with
  | nil =>
    cases pending with
    | nil => simpa [cells, offset, Expr.rename] using
        (Evaluates.lambda (environment := captured count environment) (store := before ++ previous)
          (parameterType := parameter) (resultType := result) (body := body.rename (offset count).lift))
    | cons => simp at pendingLength
  | cons head tail ih =>
    cases pending with
    | nil => simp at pendingLength
    | cons old pending =>
      have pendingTail : pending.length = tail.length := by simpa using pendingLength
      have previousNext : (previous ++ [Value.inRight .unit (helper environment head count)]).length = count + 1 := by simp [previousLength]
      have countEq : count + 1 + tail.length = count + (head :: tail).length := by
        simp only [List.length_cons, Nat.add_assoc]
        rw [Nat.add_comm 1 tail.length]
      have boundsNext : count + 1 + tail.length ≤ catalog.entries.length := countEq ▸ bounds
      have headBound : count < catalog.entries.length :=
        Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.zero_lt_succ tail.length)) bounds
      have evaluated := ih (count + 1) (previous ++ [Value.inRight .unit (helper environment head count)]) pending
        previousNext pendingTail boundsNext
      rw [countEq] at evaluated
      rw [List.zipIdx_cons, List.foldr_cons]
      simp only [installRow, Expr.rename]
      rw [offset_weaken]
      apply Evaluates.letE (bodyStore := before ++ previous ++ .inRight .unit (helper environment head count) :: pending)
      · apply Evaluates.storeCell
          (elementType := OptionalCell.cellType (comparatorType (.namedData ⟨count⟩)))
          (location := before.length + count) (oldValue := old)
        · exact .var (captured_lookup (references count headBound))
        · simp [Store.read?, ← previousLength]
        · exact .inRight .lambda
        · simpa only [previousLength, helper] using write_next before previous pending old (.inRight .unit (helper environment head count))
      · simpa [captured_succ, cells, List.zipIdx_cons, List.append_assoc, Nat.add_assoc, helper] using evaluated

/-- Actual `install` has this layout, including the Unit binders accumulated
by its preceding writes. No installed lambda body is executed here. -/
theorem install_evaluates (catalog : Catalog) (environment : Environment) (before pending : Store)
    (bodies : List Expr) (references : References catalog before.length environment)
    (pendingLength : pending.length = bodies.length) (bounds : bodies.length ≤ catalog.entries.length)
    (parameter result : Ty) (body : Expr) :
    Evaluates environment (before ++ pending) (install catalog bodies (.lambda parameter result body))
      (.closure parameter result (body.rename (offset bodies.length).lift) (captured bodies.length environment))
      (before ++ cells environment bodies) := by
  have evaluated := install_evaluates_suffix catalog environment before references bodies 0 [] pending rfl pendingLength
    (by simpa using bounds) parameter result body
  have zero : offset 0 = Renaming.id := by funext index; simp [offset, Renaming.id]
  rw [zero, Expr.rename_id] at evaluated
  simp only [captured, List.replicate_zero, List.nil_append, List.append_nil, Nat.zero_add] at evaluated
  exact evaluated

def catalogTypes (catalog : Catalog) : List Ty :=
  catalog.entries.zipIdx.map fun (_, index) => comparatorType (.namedData ⟨index⟩)

def emptyCells (types : List Ty) : Store := types.map fun type => .inLeft type .unit

def allocatedReferences (types : List Ty) (base : Nat) : Environment :=
  (types.zipIdx base).map fun (type, location) => .cellRef (OptionalCell.cellType type) location

def allocatedEnvironment (catalog : Catalog) (base : Nat) (environment : Environment) : Environment :=
  (allocatedReferences (catalogTypes catalog) base).reverse ++ environment

theorem allocate_types_evaluates (types : List Ty) (next : Expr)
    (environment : Environment) (store : Store) {value : Value} {finalStore : Store}
    (nextEvaluated : Evaluates ((allocatedReferences types store.length).reverse ++ environment)
      (store ++ emptyCells types) next value finalStore) :
    Evaluates environment store
      (types.foldr (fun type body => .letE (OptionalCell.allocate type) body) next) value finalStore := by
  induction types generalizing environment store with
  | nil => simpa [allocatedReferences, emptyCells] using nextEvaluated
  | cons type types ih =>
    apply Evaluates.letE (OptionalCell.allocate_evaluates type environment store)
    apply ih
    simpa [allocatedReferences, emptyCells, List.zipIdx_cons, List.reverse_cons, List.append_assoc] using nextEvaluated

theorem allocate_eq_types (catalog : Catalog) (next : Expr) :
    allocate catalog next =
      (catalogTypes catalog).foldr (fun type body => .letE (OptionalCell.allocate type) body) next := by
  simp [allocate, catalogTypes, List.foldr_map]

theorem catalogTypes_length (catalog : Catalog) : (catalogTypes catalog).length = catalog.entries.length := by
  simp [catalogTypes]

theorem allocated_references (catalog : Catalog) (base : Nat) (environment : Environment) :
    References catalog base (allocatedEnvironment catalog base environment) := by
  intro index bound
  have typesLength := catalogTypes_length catalog
  have referencesLength : (allocatedReferences (catalogTypes catalog) base).length = catalog.entries.length := by
    simp [allocatedReferences, typesLength]
  have typeFound : (catalogTypes catalog)[index]? = some (comparatorType (.namedData ⟨index⟩)) := by
    simp [catalogTypes, List.getElem?_zipIdx, List.getElem?_eq_getElem bound]
  have referenceFound : (allocatedReferences (catalogTypes catalog) base)[index]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) := by
    simp [allocatedReferences, List.getElem?_zipIdx, typeFound]
  have reverseFound : (allocatedReferences (catalogTypes catalog) base).reverse[catalog.entries.length - 1 - index]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) := by
    rw [List.getElem?_reverse' (j := index) (by omega)]
    exact referenceFound
  have reversedBound : catalog.entries.length - 1 - index < (allocatedReferences (catalogTypes catalog) base).reverse.length := by
    simp only [List.length_reverse, referencesLength]
    omega
  simpa [allocatedEnvironment, referenceIndex, List.getElem?_append_left reversedBound] using reverseFound

private theorem bodies_length {catalog : Catalog} {fuel : Nat} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) : bodies.length = catalog.entries.length := by
  unfold helperBodies at generated
  have mapLength : ∀ (entries : List (SourceCoreDataCatalog.Entry × Nat)) (output : List Expr),
      entries.mapM (fun (_, index) => helperBody fuel catalog ⟨index⟩) = .ok output → output.length = entries.length := by
    intro entries
    induction entries with
    | nil => intro output accepted; simpa [List.mapM_nil, pure, Except.pure] using congrArg List.length (Except.ok.inj accepted).symm
    | cons head tail ih =>
      intro output accepted
      rw [List.mapM_cons] at accepted
      cases first : helperBody fuel catalog ⟨head.2⟩ with
      | error error => simp [first, bind, Except.bind] at accepted
      | ok value =>
        cases rest : tail.mapM (fun (_, index) => helperBody fuel catalog ⟨index⟩) with
        | error error => simp [first, rest, bind, Except.bind] at accepted
        | ok values =>
          simp only [first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
          subst output
          simpa using ih values rest
  simpa using mapLength _ _ generated

/-- The full generated initializer has an exact closure/store description.
Every helper captures all references plus the Unit binders created before its
own installation; the returned comparator captures all installation binders. -/
theorem prepared_evaluates_exact {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Evaluates environment store prepared.expression
      (.closure (.product prepared.type prepared.type) .bool
        (prepared.body.rename (offset prepared.bodies.length).lift)
        (captured prepared.bodies.length (allocatedEnvironment checked.catalog store.length environment)))
      (store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  rw [prepared.expression_eq, allocate_eq_types]
  apply allocate_types_evaluates
  apply install_evaluates checked.catalog _ store _ prepared.bodies
  · exact allocated_references _ _ _
  · simp [emptyCells, catalogTypes_length, bodies_length prepared.bodiesGenerated]
  · exact Nat.le_of_eq (bodies_length prepared.bodiesGenerated)

/-- Exact contents of each installed helper slot. The representation includes
real shifted code and actual captured environments, not merely a function type. -/
def Installed (catalog : Catalog) (bodies : List Expr) (base : Nat)
    (environment : Environment) (store : Store) : Prop :=
  ∀ index body, bodies[index]? = some body →
    store.read? (base + index) =
      some (.inRight .unit (helper (allocatedEnvironment catalog base environment) body index))

theorem cells_lookup {environment : Environment} {bodies : List Expr} {index : Nat} {body : Expr}
    (found : bodies[index]? = some body) :
    (cells environment bodies)[index]? = some (.inRight .unit (helper environment body index)) := by
  simp [cells, List.getElem?_zipIdx, found]

theorem prepared_installed {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (environment : Environment) (store : Store) :
    Installed checked.catalog prepared.bodies store.length environment
      (store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  intro index body found
  simpa [Store.read?, List.getElem?_append_right] using
    (cells_lookup (environment := allocatedEnvironment checked.catalog store.length environment) found)

/-- Helpers' captured references include their own cell and every other
catalog helper. Lookup remains exact despite earlier installation Unit binders. -/
theorem captured_reference (catalog : Catalog) (base : Nat) (environment : Environment)
    (count index : Nat) (bound : index < catalog.entries.length) :
    (captured count (allocatedEnvironment catalog base environment))[count + referenceIndex catalog 0 ⟨index⟩]? =
      some (.cellRef (OptionalCell.cellType (comparatorType (.namedData ⟨index⟩))) (base + index)) :=
  captured_lookup (allocated_references catalog base environment index bound)

/-- Every completed run of actual preparation installs the exact helper table;
finite completion itself follows from `prepared_evaluates_exact`. -/
theorem prepared_completed_installed {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    {environment : Environment} {store finalStore : Store} {value : Value} {fuel : Nat}
    (ran : runStateful fuel (.initial prepared.expression environment store) = .done value finalStore) :
    value = .closure (.product prepared.type prepared.type) .bool
      (prepared.body.rename (offset prepared.bodies.length).lift)
      (captured prepared.bodies.length (allocatedEnvironment checked.catalog store.length environment)) ∧
    finalStore = store ++ cells (allocatedEnvironment checked.catalog store.length environment) prepared.bodies ∧
    Installed checked.catalog prepared.bodies store.length environment finalStore := by
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic (runStateful_evaluation_sound ran)
    (prepared_evaluates_exact prepared environment store)
  exact ⟨rfl, rfl, prepared_installed prepared environment store⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
/-! Lookup facts extracted from the actual comparator generator. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
open Core Frontend SourceCoreDataEquality

theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]

theorem mapM_lookup {α β ε : Type} (function : α → Except ε β) {inputs : List α} {outputs : List β}
    (accepted : inputs.mapM function = .ok outputs) {index : Nat} {input : α}
    (selected : inputs[index]? = some input) :
    ∃ output, outputs[index]? = some output ∧ function input = .ok output := by
  induction inputs generalizing outputs index with
  | nil => simp at selected
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨value, generated, accepted⟩ := bind_ok accepted
    obtain ⟨values, rest, accepted⟩ := bind_ok accepted
    simp only [pure, Except.pure, Except.ok.injEq] at accepted
    subst outputs
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at selected; subst input; exact ⟨value, rfl, generated⟩
    | succ index => exact ih rest selected

theorem helperBodies_lookup {fuel : Nat} {catalog : Catalog} {bodies : List Expr}
    (generated : helperBodies fuel catalog = .ok bodies) {index : Nat}
    (bound : index < catalog.entries.length) :
    ∃ body, bodies[index]? = some body ∧ helperBody fuel catalog ⟨index⟩ = .ok body := by
  exact mapM_lookup (fun (row : SourceCoreDataCatalog.Entry × Nat) => helperBody fuel catalog ⟨row.2⟩)
    generated (input := (catalog.entries[index], index))
    (by simp [List.getElem?_zipIdx, List.getElem?_eq_getElem bound])

theorem nominalBody_branches {fuel : Nat} {catalog : Catalog} {id : DataTypeId}
    {payloads : List Ty} {body : Expr} (generated : nominalBody fuel catalog id payloads = .ok body)
    {leftIndex rightIndex : Nat} {leftType rightType : Ty}
    (leftSelected : payloads[leftIndex]? = some leftType)
    (rightSelected : payloads[rightIndex]? = some rightType) :
    ∃ branches rightBranches branch,
      body = .matchData id .bool (.first (.var 0)) branches ∧
      branches[leftIndex]? = some (.matchData id .bool (.second (.var 1)) rightBranches) ∧
      rightBranches[rightIndex]? = some branch ∧
      (if leftIndex = rightIndex then compareType fuel catalog 3 leftType (.var 1) (.var 0)
       else .ok (.bool false)) = .ok branch := by
  unfold nominalBody at generated
  obtain ⟨branches, generatedBranches, generated⟩ := bind_ok generated
  simp only [pure, Except.pure, Except.ok.injEq] at generated
  subst body
  obtain ⟨leftBranch, selectedBranch, generatedLeft⟩ := mapM_lookup _ generatedBranches
    (index := leftIndex) (input := (leftType, leftIndex)) (by simp [List.getElem?_zipIdx, leftSelected])
  obtain ⟨rightBranches, generatedRight, generatedLeft⟩ := bind_ok generatedLeft
  simp only [pure, Except.pure, Except.ok.injEq] at generatedLeft
  subst leftBranch
  obtain ⟨branch, selectedRight, generatedBranch⟩ := mapM_lookup _ generatedRight
    (index := rightIndex) (input := (rightType, rightIndex)) (by simp [List.getElem?_zipIdx, rightSelected])
  exact ⟨branches, rightBranches, branch, rfl, selectedBranch, selectedRight, generatedBranch⟩

theorem rename_weaken (expression : Expr) (mapping : Renaming) :
    (expression.weakenAt 0).rename mapping.lift = (expression.rename mapping).weakenAt 0 := by
  rw [← Expr.rename_insertion, ← Expr.rename_insertion, Expr.rename_comp, Expr.rename_comp]
  congr 1

theorem functionEqual_rename (left right : Expr) (mapping : Renaming) :
    (functionEqual left right).rename mapping = functionEqual (left.rename mapping) (right.rename mapping) := by
  simp [functionEqual, Expr.rename, rename_weaken, TaggedFunction.equalBody, Renaming.lift]

theorem invoke_rename (reference left right : Expr) (mapping : Renaming) :
    (invoke reference left right).rename mapping = invoke (reference.rename mapping) (left.rename mapping) (right.rename mapping) := by
  simp [invoke, Expr.rename, rename_weaken, Renaming.lift]

theorem renameList_lookup {branches : List Expr} {index : Nat} {branch : Expr}
    (selected : branches[index]? = some branch) (mapping : Renaming) :
    (Expr.renameList branches mapping)[index]? = some (branch.rename mapping) := by
  induction branches generalizing index with
  | nil => simp at selected
  | cons head tail ih => cases index with
    | zero => simpa [Expr.renameList] using congrArg (Option.map (·.rename mapping)) selected
    | succ index => exact ih selected

theorem nominal_compareType {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments))
    {fuel depth : Nat} {left right compiled : Expr}
    (accepted : compareType fuel catalog depth (.namedData id) left right = .ok compiled) :
    compiled = invoke (.var (referenceIndex catalog depth id)) left right := by
  cases fuel with
  | zero => simp [compareType] at accepted
  | succ fuel =>
    cases kind : entry.sourceType <;>
      simp only [compareType, selected, kind, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    all_goals try exact accepted.symm
    all_goals simp [kind, SourceCoreDataCatalog.nominalParts] at nominal

theorem nominal_helperBody {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts entry.sourceType = some (declaration, arguments))
    {fuel : Nat} {body : Expr} (accepted : helperBody fuel catalog id = .ok body) :
    ∃ definition, entry.definition = some definition ∧
      nominalBody fuel catalog id definition.constructorPayloadTypes = .ok body := by
  have next : (match entry.definition with
      | some definition => nominalBody fuel catalog id definition.constructorPayloadTypes
      | none => .error (.missingDefinition id)) = .ok body := by
    cases kind : entry.sourceType <;>
      simp only [helperBody, selected, kind, bind, Except.bind, pure, Except.pure] at accepted
    all_goals try exact accepted
    all_goals simp [kind, SourceCoreDataCatalog.nominalParts] at nominal
  cases found : entry.definition with
  | none => simp [found] at next
  | some definition => exact ⟨definition, rfl, by simpa [found] using next⟩

theorem registered_payload {catalog : Catalog} {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry}
    (selected : catalog.entries[id.index]? = some entry) {definition : DataDefinition}
    (definitionSelected : entry.definition = some definition) {index : Nat} {payloadType : Ty}
    (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType) :
    definition.constructorPayloadTypes[index]? = some payloadType := by
  simpa [SourceCoreDataCatalog.Catalog.definitions, DataEnvironment.lookupConstructorPayloadType?,
    DataEnvironment.lookupDataType?, selected, definitionSelected] using registered

end Solcore.SourceSemantics.CoreLowering.DataEqualityGeneration
end
