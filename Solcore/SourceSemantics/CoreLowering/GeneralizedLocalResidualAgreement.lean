import Solcore.SourceSemantics.SourceResidualNodeSubstitutionAgreement
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationResidualScopes
import Solcore.SourceSemantics.CoreLowering.CallableBodyViewSubstitution

/-! Actual residual validation reduces a node's substitution agreement to its
own lexical scope. Embedded binder quantifiers are masked by the real binder
operation; their body and requirement metadata are both preserved. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
open Core Frontend SourceInference TypeSystem SourceSpecialization
open GeneralizedLocalInstanceCompilation (Inputs)
open GeneralizedLocalLambdaCompilation (Packet)
open GeneralizedLocalLambdaGeneration (Indexed)
open CallableAncestryProfiles.SourceComposition
open CallableBodyMetadataViews CallableLambdaBodyReachability

private theorem type_congr {left right : Substitution} (type : TypeSystem.Ty)
    (same : ∀ metavariable ∈ type.freeVariables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    left.apply type = right.apply type := by
  induction type with
  | «variable» metavariable => exact same metavariable (by simp [Ty.freeVariables])
  | parameter | constructor | error => rfl
  | application _ _ first second | function _ _ first second
  | product _ _ first second | mapping _ _ first second =>
    simp only [Substitution.apply]
    rw [first (by intro v h; exact same v (by simp [h])),
      second (by intro v h; exact same v (by simp [h]))]
  | proxy _ ih | comptime _ ih =>
    simp only [Substitution.apply]
    rw [ih (by intro v h; exact same v (by simpa only [Ty.freeVariables] using h))]

/-- The same action is needed only for the actual path's variables. Quantifiers
of embedded binders are handled by their existing capture-avoiding masks. -/
theorem node_of_scope {left right : Substitution} {node : Node}
    {variables : List TypeVarId}
    (types : ∀ type ∈ residualNodeTypes node,
      ∀ metavariable ∈ type.freeVariables, metavariable ∈ variables)
    (binders : ∀ binder ∈ residualNodeBinders node, ∀ type ∈ residualBinderTypes binder,
      ∀ metavariable ∈ type.freeVariables,
        metavariable ∈ variables ∨ metavariable ∈ binder.scheme.quantified)
    (same : ∀ metavariable ∈ variables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    node.applySubstitution left = node.applySubstitution right := by
  apply SourceResidualNodeSubstitutionAgreement.node_congr
  · intro type member
    exact type_congr type (fun v occurs => same v (types type member v occurs))
  · intro binder member type inspected
    apply type_congr
    intro metavariable occurs
    by_cases quantified : metavariable ∈ binder.scheme.quantified
    · simp only [Substitution.apply, lookup_without, if_pos quantified]
    · have inScope : metavariable ∈ variables :=
        (binders binder member type inspected metavariable occurs).resolve_right quantified
      simpa only [Substitution.apply, lookup_without, if_neg quantified] using same metavariable inScope

/-- The catalog entry and accepted Packet supply the real source validation.
This endpoint does not ask for a separate residual-formation law. -/
theorem binding_node_at_scope {compiled : SourceCoreUnifiedCompilation.Compiled}
    {binding : SourceCoreLocalPolymorphism.Binding} {active left right : Substitution}
    {candidate : SourceCoreLocalPolymorphism.Instance} {inputs : Inputs} {raw : Core.Expr}
    {packet : Packet inputs candidate raw} (indexed : Indexed compiled.indexed packet)
    (located : compiled.indexed.base.locals.binding binding.caller binding.binder.id = .ok binding)
    (member : candidate ∈ binding.atContext active)
    {node : Node} (present : node ∈ binding.source.nodes) {variables : List TypeVarId}
    (path : ResidualScopePath binding.source node.id variables)
    (same : ∀ metavariable ∈ variables,
      left.apply (.variable metavariable) = right.apply (.variable metavariable)) :
    node.applySubstitution left = node.applySubstitution right := by
  obtain ⟨types, binders⟩ :=
    SelectedCompilationResidualScopes.binding_path_support indexed located member present path
  exact node_of_scope types binders same

/-- Node agreement on the actual reached body supplies the existing body view.
Unrelated source-table rows are never compared. -/
theorem body_view_of_nodes {source : TypedSource} {roots : List NodeId}
    {left right : Substitution}
    (same : ∀ node ∈ source.nodes, Reaches source roots node.id →
      node.applySubstitution left = node.applySubstitution right) :
    BodyView (source.applySubstitution left) (source.applySubstitution right) roots where
  owner := rfl
  inputs := by simp only [TypedSource.applySubstitution_inputIds]
  expression reached _ found := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, selected, rfl⟩ := Option.map_eq_some_iff.mp found
    have contained := lookupExpression?_sound selected
    have agreement := same (.expression node) contained.1
      (by simpa only [Node.id, contained.2] using path)
    have nodeEq := Node.expression.inj agreement
    exact ⟨node.applySubstitution left, by rw [lookupExpression_apply, selected]; rfl,
      rfl, congrArg ExpressionNode.form nodeEq⟩
  expression_back reached _ found := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupExpression_apply] at found
    obtain ⟨node, selected, rfl⟩ := Option.map_eq_some_iff.mp found
    have contained := lookupExpression?_sound selected
    have agreement := same (.expression node) contained.1
      (by simpa only [Node.id, contained.2] using path)
    have nodeEq := Node.expression.inj agreement
    exact ⟨node.applySubstitution right, by rw [lookupExpression_apply, selected]; rfl,
      rfl, congrArg ExpressionNode.form nodeEq.symm⟩
  statement reached := by
    have path := reached.elim (reaches_substitution left).mp (reaches_substitution right).mp
    rw [lookupStatement_apply, lookupStatement_apply]
    cases selected : source.lookupStatement? _ with
    | none => rfl
    | some node =>
      have contained := lookupStatement?_sound selected
      have agreement := same (.statement node) contained.1
        (by simpa only [Node.id, contained.2] using path)
      exact congrArg some (Node.statement.inj agreement)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalResidualAgreement
