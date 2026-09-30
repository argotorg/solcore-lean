import Solcore.SourceSemantics.CoreLowering.DataEqualityInstalled
import Solcore.SourceSemantics.CoreLowering.DataPatternValues

/-! Actual comparison compilation yields a finite comparison certificate for
scalar/product carriers. Nominal recursive payloads, function identities,
mapping keys and proxy metadata require their own authenticated extensions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
open Core Frontend SourceCoreDataEquality DataEquality DataPatternValues

inductive ScalarType : Ty → Prop where
  | unit : ScalarType .unit
  | bool : ScalarType .bool
  | word : ScalarType .word
  | integer : ScalarType .integer
  | product {left right : Ty} (first : ScalarType left) (second : ScalarType right) : ScalarType (.product left right)

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The certificate is extracted from successful actual compilation and
represented input shapes. It supplies its own finite child comparisons. -/
theorem tree_of_compareType {type : Ty} (scalar : ScalarType type)
    {catalog : Catalog} {fuel depth : Nat} {leftExpression rightExpression compiled : Expr}
    (accepted : compareType fuel catalog depth type leftExpression rightExpression = .ok compiled)
    {definitions : DataEnvironment} {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue type definitions) (rightTyped : ValueHasType rightValue type definitions)
    (environment : Environment) (store : Store) (mapping : Renaming)
    (leftSelected : Selects environment (leftExpression.rename mapping) leftValue)
    (rightSelected : Selects environment (rightExpression.rename mapping) rightValue) :
    ∃ result, Tree identities store environment (compiled.rename mapping) sourceLeft sourceRight result := by
  induction scalar generalizing fuel depth leftExpression rightExpression compiled sourceLeft sourceRight leftValue rightValue with
  | unit =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨true, .unit⟩
  | bool =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .bool leftSelected rightSelected⟩
  | word =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .word leftSelected rightSelected⟩
  | integer =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      simp only [compareType, pure, Except.pure, Except.ok.injEq] at accepted
      subst compiled
      cases leftTyped; cases rightTyped; cases leftRepresentation; cases rightRepresentation
      exact ⟨_, .integer leftSelected rightSelected⟩
  | @product leftType rightType first second firstIH secondIH =>
    cases fuel with
    | zero => simp [compareType] at accepted
    | succ fuel =>
      have generated : (show Except SourceCoreDataEquality.Error Expr from do
          let left ← compareType fuel catalog depth leftType (.first leftExpression) (.first rightExpression)
          let right ← compareType fuel catalog depth rightType (.second leftExpression) (.second rightExpression)
          pure (.ifE left right (.bool false))) = .ok compiled := by
        cases leftType <;> try cases first
        all_goals exact accepted
      obtain ⟨leftCode, leftCompiled, generated⟩ := bind_ok generated
      obtain ⟨rightCode, rightCompiled, generated⟩ := bind_ok generated
      simp only [pure, Except.pure, Except.ok.injEq] at generated
      subst compiled
      cases leftTyped with
      | pair firstTyped secondTyped => cases rightTyped with
        | pair otherFirstTyped otherSecondTyped => cases leftRepresentation with
          | product firstRepresentation secondRepresentation => cases rightRepresentation with
            | product otherFirstRepresentation otherSecondRepresentation =>
              obtain ⟨firstResult, firstTree⟩ := firstIH leftCompiled firstRepresentation otherFirstRepresentation
                firstTyped otherFirstTyped (.first leftSelected) (.first rightSelected)
              obtain ⟨secondResult, secondTree⟩ := secondIH rightCompiled secondRepresentation otherSecondRepresentation
                secondTyped otherSecondTyped (.second leftSelected) (.second rightSelected)
              exact ⟨_, .product firstTree secondTree⟩

/-- Scalar comparisons from a prepared initializer work in its real captured
environment and in any later store, including an OrderedMapping helper suffix. -/
theorem prepared_tree {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) {identities : Dynamic.Value → Word → Prop}
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (initialStore store : Store) :
    ∃ result, Tree identities store
      (.pair leftValue rightValue :: DataEqualityInstalled.captured prepared.bodies.length
        (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment))
      (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
      sourceLeft sourceRight result := by
  apply tree_of_compareType scalar prepared.bodyGenerated leftRepresentation rightRepresentation leftTyped rightTyped
  · exact .first (.var rfl)
  · exact .second (.var rfl)

/-- The prepared comparator supplies OrderedMapping's pure comparison law
in the actual later store; scalar/product comparisons perform no heap effects. -/
theorem prepared_compares {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) (layout : OrderedMapping.Layout) (keyType : layout.keyType = prepared.type)
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (initialStore store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      OrderedMapping.Compares layout
        (.closure (.product prepared.type prepared.type) .bool
          (prepared.body.rename (DataEqualityInstalled.offset prepared.bodies.length).lift)
          (DataEqualityInstalled.captured prepared.bodies.length
            (DataEqualityInstalled.allocatedEnvironment checked.catalog initialStore.length environment)))
        leftValue rightValue result store := by
  obtain ⟨result, tree⟩ := prepared_tree prepared scalar leftRepresentation rightRepresentation
    leftTyped rightTyped environment initialStore store
  exact ⟨result, tree.meaning faithful, by simpa only [keyType] using tree.compares layout⟩

/-- Actual initialization followed by invocation preserves independent source
key equality. Child comparisons and closure installation are both proved,
without an execution-correctness premise supplied by a caller. -/
theorem prepared_compare_preserves {checked : SourceCoreDataCatalog.Checked} (prepared : Prepared checked)
    (scalar : ScalarType prepared.type) {identities : Dynamic.Value → Word → Prop}
    (faithful : IdentityFaithful identities)
    {sourceLeft sourceRight : Dynamic.Value} {leftValue rightValue : Value}
    (leftRepresentation : ValueRep checked.catalog sourceLeft leftValue)
    (rightRepresentation : ValueRep checked.catalog sourceRight rightValue)
    (leftTyped : ValueHasType leftValue prepared.type checked.catalog.definitions)
    (rightTyped : ValueHasType rightValue prepared.type checked.catalog.definitions)
    (environment : Environment) (store : Store) (leftExpression rightExpression : Expr)
    (leftSelected : Selects environment leftExpression leftValue)
    (rightSelected : Selects environment rightExpression rightValue) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent sourceLeft sourceRight) ∧
      Evaluates environment store
        (.letE prepared.expression (.apply (.var 0)
          (.pair (leftExpression.weakenAt 0) (rightExpression.weakenAt 0))))
        (.bool result)
        (store ++ DataEqualityInstalled.cells
          (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies) := by
  obtain ⟨result, tree⟩ := prepared_tree prepared scalar leftRepresentation rightRepresentation leftTyped rightTyped
    environment store (store ++ DataEqualityInstalled.cells
      (DataEqualityInstalled.allocatedEnvironment checked.catalog store.length environment) prepared.bodies)
  refine ⟨result, tree.meaning faithful, .letE (DataEqualityInstalled.prepared_evaluates_exact prepared environment store) ?_⟩
  exact .apply (.var rfl) (.pair ((leftSelected.weaken _).evaluates _) ((rightSelected.weaken _).evaluates _)) tree.evaluates

end Solcore.SourceSemantics.CoreLowering.DataEqualityScalarCertificates
