import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityGeneration
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityPayload
import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding

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
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
    {functions : FunctionModel checked.catalog} {mapping : GeneralHeap.LocationMap} {world : StoreTyping}
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
