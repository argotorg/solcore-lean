import Solcore.SourceSemantics.CoreLowering.DataPatternCertificates
import Solcore.SourceSemantics.CoreLowering.DataEquality

/-! Proof-side data representation for matching. A nominal node retains the
entire source instantiation and the catalog constructor lookup; Core type
membership alone does not establish source constructor authenticity. The
initial relation covers finite scalar/product/nominal values. Function,
mapping, and proxy binder inputs need the corresponding general value bridge. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternValues
open Core Frontend Frontend.SourceInference
open SourceCoreDataMatches DataEquality

inductive ListRel {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRel relation [] []
  | cons {head : α} {tail : List α} {value : β} {values : List β}
      (related : relation head value) (rest : ListRel relation tail values) :
      ListRel relation (head :: tail) (value :: values)

def packValues : List Value → Value
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packValues rest)

mutual
  inductive ValueRep (catalog : SourceCoreDataCatalog.Catalog) : Dynamic.Value → Value → Prop where
    | unit : ValueRep catalog .unit .unit
    | bool (value : Bool) : ValueRep catalog (.bool value) (.bool value)
    | word (value : Word) : ValueRep catalog (.word value) (.word value)
    | integer (value : Int) : ValueRep catalog (.integer value) (.integer value)
    | product {left right : Dynamic.Value} {a b : Value}
        (leftRep : ValueRep catalog left a) (rightRep : ValueRep catalog right b) :
        ValueRep catalog (.product left right) (.pair a b)
    | constructed {instantiation : DataConstructorInstantiation} {tag : ConstructorId}
        {arguments : List Dynamic.Value} {values : List Value}
        (selected : catalog.constructor? instantiation = some tag)
        (payloads : ValuesRep catalog arguments values) :
        ValueRep catalog (.constructed instantiation arguments) (.constructed tag (packValues values))

  inductive ValuesRep (catalog : SourceCoreDataCatalog.Catalog) : List Dynamic.Value → List Value → Prop where
    | nil : ValuesRep catalog [] []
    | cons {source : Dynamic.Value} {value : Value} {sources : List Dynamic.Value} {values : List Value}
        (head : ValueRep catalog source value) (tail : ValuesRep catalog sources values) :
        ValuesRep catalog (source :: sources) (value :: values)
end

theorem ValuesRep.length {catalog : SourceCoreDataCatalog.Catalog} {sources : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep catalog sources values) : sources.length = values.length := by
  induction sources generalizing values with
  | nil => cases represented; rfl
  | cons head tail ih => cases represented with
    | cons headRep tailRep => simp [ih tailRep]

theorem ValuesRep.pack {catalog : SourceCoreDataCatalog.Catalog} {sources : List Dynamic.Value} {values : List Value}
    (represented : ValuesRep catalog sources values) {source : Dynamic.Value}
    (packed : Dynamic.ValuesPack sources source) : ValueRep catalog source (packValues values) := by
  induction packed generalizing values with
  | nil => cases represented; exact .unit
  | singleton source => cases represented with
    | cons head tail => cases tail; exact head
  | cons packed ih => cases represented with
    | cons head tail =>
      cases tail with
      | cons second rest => exact .product head (ih (.cons second rest))

theorem bundle_evaluates {environment : Environment} {store : Store}
    {expressions : List Expr} {values : List Value}
    (evaluations : ListRel (fun expression value => Evaluates environment store expression value store) expressions values) :
    Evaluates environment store (bundle expressions) (packValues values) store := by
  induction evaluations with
  | nil => exact .unit
  | @cons expression expressions value values head tail ih =>
    cases expressions with
    | nil => cases tail; exact head
    | cons second rest => cases tail with
      | cons secondEval restEval => exact .pair head ih

theorem projectPacked_selects {environment : Environment} {expression : Expr} {types : List Ty} {values : List Value}
    (selected : Selects environment expression (packValues values)) (sameLength : types.length = values.length)
    (index : Nat) {value : Value} (found : values[index]? = some value) :
    Selects environment (SourceCoreDataExpressions.projectPacked index types expression) value := by
  induction types generalizing expression values index with
  | nil =>
    have empty : values = [] := by simpa using sameLength.symm
    subst values; simp at found
  | cons type types ih =>
    cases values with
    | nil => simp at sameLength
    | cons first values =>
      cases types with
      | nil =>
        have empty : values = [] := by simpa using (Nat.succ.inj sameLength).symm
        subst values
        cases index with
        | zero => simp at found; subst value; exact selected
        | succ => simp at found
      | cons second rest =>
        cases values with
        | nil => simp at sameLength
        | cons next values =>
          cases index with
          | zero =>
            simp at found; subst value
            simpa [SourceCoreDataExpressions.projectPacked] using Selects.first selected
          | succ index =>
            have tail := ih (Selects.second selected) (Nat.succ.inj sameLength) index (by simpa using found)
            simpa [SourceCoreDataExpressions.projectPacked] using tail

/-- Pure paths remain valid after introducing the successful child-bundle
binder used by the generated matcher. -/
theorem selects_weaken_list {environment : Environment} {expressions : List Expr} {values : List Value}
    (selected : ListRel (Selects environment) expressions values) (inserted : Value) :
    ListRel (Selects (inserted :: environment)) (expressions.map (·.weakenAt 0)) values := by
  induction selected with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.weaken inserted) ih

end Solcore.SourceSemantics.CoreLowering.DataPatternValues
