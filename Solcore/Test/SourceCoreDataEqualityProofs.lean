import Solcore.SourceSemantics.CoreLowering.DataEquality
import Solcore.SourceSemantics.CoreLowering.DataDefaults

/-! A recursive nominal comparison proof for every finite pair of unary
constructor trees, using the actual generated helper body and a shared cell.
The source constructors are explicit canonical metadata parameters. -/

set_option autoImplicit false

namespace Tests.SourceCoreDataEqualityProofs

open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics
open Solcore.SourceSemantics.CoreLowering.DataEquality

private def sourceType (declaration : Resolved.DeclarationId) : TypeSystem.Ty :=
  .constructor (.declaration declaration)
private def catalog (declaration : Resolved.DeclarationId) : SourceCoreDataCatalog.Catalog :=
  ⟨[{ sourceType := sourceType declaration,
      definition := some ⟨[.unit, .namedData ⟨0⟩]⟩ }]⟩
private def type : Core.Ty := .namedData ⟨0⟩
private def parameter : Core.Ty := .product type type
private def helper : Expr := .matchData ⟨0⟩ .bool (.first (.var 0)) [
  .matchData ⟨0⟩ .bool (.second (.var 1)) [.bool true, .bool false],
  .matchData ⟨0⟩ .bool (.second (.var 1)) [.bool false,
    SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]]

example (declaration : Resolved.DeclarationId) :
    SourceCoreDataEquality.helperBody 8 (catalog declaration) ⟨0⟩ = .ok helper := by
  simp [SourceCoreDataEquality.helperBody, SourceCoreDataEquality.nominalBody,
    SourceCoreDataEquality.compareType, SourceCoreDataEquality.referenceIndex,
    catalog, sourceType, helper, List.mapM, List.mapM.loop, bind, Except.bind, pure, Except.pure]

private def encode : Nat → Value
  | 0 => .constructed ⟨⟨0⟩, 0⟩ .unit
  | n + 1 => .constructed ⟨⟨0⟩, 1⟩ (encode n)
private def source (nil cons : DataConstructorInstantiation) : Nat → Dynamic.Value
  | 0 => .constructed nil []
  | n + 1 => .constructed cons [source nil cons n]
private def reference (location : Nat) : Value :=
  .cellRef (OptionalCell.cellType (SourceCoreDataEquality.comparatorType type)) location
private def closure (location : Nat) (captured : Environment) : Value :=
  .closure parameter .bool helper (reference location :: captured)
private def identities : Dynamic.Value → Word → Prop := fun _ _ => False
private theorem faithful : IdentityFaithful identities := {
  comparable := by intro _ _ impossible; cases impossible
  equal := by intro _ _ _ _ impossible; cases impossible
}

/-- Structural induction over the compared values traverses the shared
recursive helper. It neither unfolds an evaluator nor assumes its result. -/
private theorem comparison (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    Tree identities store (.pair (encode left) (encode right) :: reference location :: captured)
      helper (source nil cons left) (source nil cons right) (decide (left = right)) := by
  induction left generalizing right with
  | zero =>
    cases right with
    | zero =>
      simp only [source, encode, helper]
      exact Tree.nominalSame (right := .second (.var 0)) (rightBranches := [.bool true, .bool false]) nil
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
        .nil .nil rfl .unit
    | succ right =>
      simp only [source, encode, helper]
      exact Tree.nominalDifferent (right := .second (.var 0)) (rightBranches := [.bool true, .bool false]) nil cons [] [source nil cons right] distinct
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
  | succ left ih =>
    cases right with
    | zero =>
      simp only [source, encode, helper]
      exact Tree.nominalDifferent (right := .second (.var 0))
        (rightBranches := [.bool false, SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]) cons nil [source nil cons left] [] (Ne.symm distinct)
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
    | succ right =>
      simp only [source, encode, helper, Nat.succ.injEq]
      refine Tree.nominalSame (right := .second (.var 0))
        (rightBranches := [.bool false, SourceCoreDataEquality.invoke (.var 3) (.var 1) (.var 0)]) cons
        (.first (.var rfl)) (.second (.var rfl)) (by simp [Expr.weakenAt]) rfl
        (.singleton (source nil cons left)) (.singleton (source nil cons right)) rfl ?_
      exact Tree.invoke (.var rfl) (.var rfl) (.var rfl) installed (ih right)

/-- Arbitrary existing store contents and captured values are retained. The
helper remains pure after any append that preserves its installed location. -/
example (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    OrderedMapping.Compares ⟨type, .word, ⟨1⟩⟩ (closure location captured)
      (encode left) (encode right) (decide (left = right)) store ∧
    (decide (left = right) = true ↔
      Dynamic.ValueEquivalent (source nil cons left) (source nil cons right)) := by
  have tree := comparison nil cons distinct store location captured installed left right
  exact ⟨tree.compares _, tree.meaning faithful⟩

/-- Authentic generator output and the recursive value certificate yield a
finite run for every finite pair, with the exact unchanged store. -/
example (declaration : Resolved.DeclarationId)
    (nil cons : DataConstructorInstantiation) (distinct : nil ≠ cons)
    (store : Store) (location : Nat) (captured : Environment)
    (installed : store[location]? = some (.inRight .unit (closure location captured)))
    (left right : Nat) :
    ∃ required, ∀ fuel, required ≤ fuel →
      runStateful fuel (State.initial
        (SourceCoreDataEquality.invoke (.var 1) (.first (.var 0)) (.second (.var 0)))
        (.pair (encode left) (encode right) :: reference location :: captured) store) =
      .done (.bool (decide (left = right))) store := by
  have compiled : SourceCoreDataEquality.compareType 8 (catalog declaration) 1 type
      (.first (.var 0)) (.second (.var 0)) =
      .ok (SourceCoreDataEquality.invoke (.var 1) (.first (.var 0)) (.second (.var 0))) := by
    simp [SourceCoreDataEquality.compareType, SourceCoreDataEquality.referenceIndex, catalog, sourceType, type]
  exact (compareType_run_preserves faithful compiled
    (Tree.invoke (.var rfl) (.first (.var rfl)) (.second (.var rfl)) installed
      (comparison nil cons distinct store location captured installed left right))).2

example (environment : Environment) (store : Store) :
    ∃ source value required,
      CoreLowering.DataDefaults.Tree {} (.product .integer .bool) source value
        (.pair (.integer 0) (.bool false)) ∧
      Dynamic.DefaultValue (.product .integer .bool) source ∧
      ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.pair (.integer 0) (.bool false)) environment store) =
          .done value store :=
  CoreLowering.DataDefaults.defaultExpression_run_preserves 3 {} (.product .integer .bool)
    _ rfl environment store

end Tests.SourceCoreDataEqualityProofs
