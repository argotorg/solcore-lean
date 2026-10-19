import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalReadReceipts

/-! Runtime selection of a generalized local instance follows the exact
candidate position emitted by the compiler. The row can contain different
native types; selecting a field leaves the shared store unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism

theorem project_evaluates {types : List Core.Ty} {values : List Core.Value}
    {index : Nat} {native : Core.Value} {bundle projection : Core.Expr}
    {environment : Core.Environment} {before after : Core.Store}
    (lengths : values.length = types.length)
    (found : values[index]? = some native)
    (selected : ProductBundle.project? types index bundle = some projection)
    (evaluated : Core.Evaluates environment before bundle (ProductBundle.value values) after) :
    Core.Evaluates environment before projection native after := by
  induction types generalizing values index bundle projection with
  | nil =>
      have empty : values = [] := by simpa using lengths
      simp [empty] at found
  | cons head rest ih =>
      cases values with
      | nil => simp at lengths
      | cons value tail =>
        cases rest with
        | nil =>
            have empty : tail = [] := by simpa using lengths
            subst tail
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                simp only [ProductBundle.project?, Option.some.injEq] at selected
                subst native
                subst projection
                exact evaluated
            | succ index => simp at found
        | cons next remaining =>
            cases tail with
            | nil => simp at lengths
            | cons nextValue remainingValues =>
                cases index with
                | zero =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                    simp only [ProductBundle.project?, Option.some.injEq] at selected
                    subst native
                    subst projection
                    exact .first evaluated
                | succ index =>
                    exact ih (by simpa using lengths) (by simpa using found)
                      selected (.second evaluated)

variable {catalog : Catalog} {caller : Key} {active : Substitution}
  {source : TypedSource} {scope : Scope} {id : ExpressionId} {reason : Core.Word}
  {lowered : SourceCoreBasic.LoweredExpr}

/-- A row relation authenticates each stored candidate independently. Its
selection proof needs no equation between the different candidate types. -/
theorem related_selected {relation : Instance → Core.Value → Prop}
    {instances : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise relation instances values)
    {index : Nat} {candidate : Instance}
    (found : instances[index]? = some candidate) :
    ∃ native, values[index]? = some native ∧ relation candidate native := by
  induction rows generalizing index with
  | nil => simp at found
  | @cons head native rest tail related rows ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst candidate
          exact ⟨native, rfl, related⟩
      | succ index => exact ih (by simpa using found)

theorem row_length {relation : Instance → Core.Value → Prop}
    {instances : List Instance} {values : List Core.Value}
    (rows : ProductBundle.Pointwise relation instances values) :
    values.length = instances.length := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simpa using ih

/-- The actual lowering reads the mapped optional cell, then projects its
selected candidate without changing the heap or consulting another instance. -/
theorem preserves
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {relation : Instance → Core.Value → Prop} {values : List Core.Value}
    {environment : Core.Environment} {store : Core.Store} {location : Core.Location}
    (rows : ProductBundle.Pointwise relation (receipt.binding.atContext active) values)
    (reference : environment[receipt.index]? =
      some (.cellRef (OptionalCell.cellType receipt.payloadType) location))
    (read : store.read? location = some (.inRight .unit (ProductBundle.value values))) :
    ∃ native, relation receipt.candidate native ∧
      Core.Evaluates environment store lowered.expression (.inRight .word native) store := by
  obtain ⟨native, found, related⟩ := related_selected rows receipt.candidate_at
  refine ⟨native, related, ?_⟩
  rw [receipt.emitted]
  exact SourceCoreLocalPolymorphism.read_success
    (OptionalCell.read_success reason (.var reference) read)
    (project_evaluates (by simpa using row_length rows) found receipt.projected (.var rfl))

/-- Any finite native execution of the same emitted read returns that same
selected payload and retains the store. -/
theorem reflects
    (receipt : GeneralizedLocalReadReceipts.Certificate catalog caller active source scope id reason lowered)
    {relation : Instance → Core.Value → Prop} {values : List Core.Value}
    {environment : Core.Environment} {before after : Core.Store} {location : Core.Location}
    {output : Core.Value}
    (rows : ProductBundle.Pointwise relation (receipt.binding.atContext active) values)
    (reference : environment[receipt.index]? =
      some (.cellRef (OptionalCell.cellType receipt.payloadType) location))
    (read : before.read? location = some (.inRight .unit (ProductBundle.value values)))
    (evaluated : Core.Evaluates environment before lowered.expression output after) :
    after = before ∧ ∃ native, output = .inRight .word native ∧ relation receipt.candidate native := by
  obtain ⟨native, related, expected⟩ := preserves receipt rows reference read
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated expected
  exact ⟨rfl, native, rfl, related⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBundleReadMeaning
