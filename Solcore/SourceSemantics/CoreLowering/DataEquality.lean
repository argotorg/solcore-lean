import Solcore.Frontend.SourceCoreDataEquality
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.Core.Correspondence

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

private theorem product_equivalent {a b c d : Dynamic.Value} :
    Dynamic.ValueEquivalent (.product a b) (.product c d) ↔
      Dynamic.ValueEquivalent a c ∧ Dynamic.ValueEquivalent b d := by
  constructor
  · rintro ⟨same, comparable⟩
    cases same
    cases comparable with
    | product left right => exact ⟨⟨rfl, left⟩, ⟨rfl, right⟩⟩
  · rintro ⟨⟨rfl, left⟩, ⟨rfl, right⟩⟩
    exact ⟨rfl, .product left right⟩

private theorem pack_comparable {values : List Dynamic.Value} {packed : Dynamic.Value}
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

private theorem pack_equivalent {left right : List Dynamic.Value} {leftPacked rightPacked : Dynamic.Value}
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
