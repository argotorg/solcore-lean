import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityInstalled

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
