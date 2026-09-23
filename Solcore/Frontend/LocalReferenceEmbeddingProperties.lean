import Solcore.Frontend.LocalExpression
import Solcore.Frontend.LocalExpressionTyping
import Solcore.Frontend.LocalExpressionEvaluation
import Solcore.Frontend.LocalReference

/-! The identifier/group adapter embeds exactly in the conditional adapter.
Variable-shaped resolution characterizes the old fragment; evaluating a
conditional to a local value does not turn it into an old reference expression. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- A variable-shaped structural result can only arise from an old reference. -/
theorem ResolvesLocalExpression.toLocalReference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (resolution : ResolvesLocalExpression table source (.var id)) :
    ResolvesLocalReference table source id := by
  cases resolution with
  | identifier found => exact .identifier found
  | group child => exact .group child.toLocalReference
termination_by sizeOf source

theorem resolvesLocalExpression_var_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    ResolvesLocalExpression table source (.var id) ↔ ResolvesLocalReference table source id :=
  ⟨ResolvesLocalExpression.toLocalReference, ResolvesLocalReference.toLocalExpression⟩

theorem resolveLocalExpression?_var_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId} :
    resolveLocalExpression? table source = some (.var id) ↔
      resolveLocalReference? table source = some (.var id) :=
  resolveLocalExpression?_iff.trans
    (resolvesLocalExpression_var_iff_reference.trans resolveLocalReference?_iff.symm)

/-- Once the name resolves, both checked endpoints agree for every supplied
context, including contexts where the selected identity is absent. -/
theorem elaborateLocalExpression?_eq_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id) (context : Resolved.Context) :
    elaborateLocalExpression? table context source = elaborateLocalReference? table context source := by
  simp only [elaborateLocalExpression?, elaborateLocalReference?,
    reference.complete, reference.toLocalExpression.complete]

/-- On an already resolved reference, the new store-threaded evaluation is
exactly the old value judgment together with equality of the store endpoints. -/
theorem localExpressionEvaluates_iff_reference {table : LocalNameTable}
    {source : Syntax.Expr} {id : Resolved.LocalId}
    (reference : ResolvesLocalReference table source id)
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store} {value : Core.Value} :
    LocalExpressionEvaluates table environment initialStore source value finalStore ↔
      LocalReferenceEvaluates table environment source value ∧ finalStore = initialStore := by
  rw [reference.toLocalExpression.evaluates_iff]
  constructor
  · intro evaluation
    cases evaluation with
    | var found => exact ⟨.reference reference found, rfl⟩
  · rintro ⟨evaluation, rfl⟩
    cases evaluation with
    | reference actual found =>
        cases reference.id_unique actual
        exact .var found

end Solcore.Frontend
