import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadMeaning
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure

/-! Genuine captured declarations survive the same flexible substitution as
the materialized Source closure. Binder identities and declaration order stay
fixed; source schemes and the lexical context are substituted together. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
open Core Frontend SourceInference TypeSystem
open SourceCoreDataPlaces

private theorem instructions (substitution : Substitution) (items : List MatchPatternInstruction) :
    instructionBinders (items.map (MatchPatternInstruction.applySubstitution substitution)) =
      (instructionBinders items).map (TypedBinder.applySubstitution substitution) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simpa [instructionBinders, MatchPatternInstruction.applySubstitution] using ih

private theorem pattern (substitution : Substitution) (item : TypedMatchPattern) :
    patternBinders (item.applySubstitution substitution) =
      (patternBinders item).map (TypedBinder.applySubstitution substitution) := by
  cases form : item.resolution <;>
    simp [patternBinders, TypedMatchPattern.applySubstitution, MatchPatternResolution.applySubstitution, form, instructions]

private theorem for_items (substitution : Substitution) (items : List ForItemForm) :
    (items.map (ForItemForm.applySubstitution substitution)).filterMap (fun | .letDecl binder _ => some binder | _ => none) =
      (items.filterMap (fun | .letDecl binder _ => some binder | _ => none)).map (TypedBinder.applySubstitution substitution) := by
  induction items with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [ForItemForm.applySubstitution, ih]

theorem declared (substitution : Substitution) (source : TypedSource) :
    declaredBinders (source.applySubstitution substitution) =
      (declaredBinders source).map (TypedBinder.applySubstitution substitution) := by
  simp only [declaredBinders, TypedSource.applySubstitution, List.map_append, List.flatMap_map, List.map_flatMap]
  congr 1
  apply congrArg (fun f : Node → List TypedBinder => source.nodes.flatMap f)
  funext node
  cases node with
  | expression node =>
    cases form : node.form <;> simp [Node.applySubstitution, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]
  | statement node =>
    cases form : node.form <;>
      simp [Node.applySubstitution, StatementNode.applySubstitution, StatementForm.applySubstitution, form,
        List.filterMap_append, MatchResolution.applySubstitution, List.flatMap_map,
        List.map_flatMap, TypedMatchCase.applySubstitution, pattern]
    rename_i initial condition post body
    have first := for_items substitution initial
    have second := for_items substitution post
    simp only [List.filterMap_map] at first second
    exact congr (congrArg List.append first) second

theorem root (substitution : Substitution) (source : TypedSource) (id : Resolved.LocalId) :
    rootBinder (source.applySubstitution substitution) id =
      (rootBinder source id).map (TypedBinder.applySubstitution substitution) := by
  unfold rootBinder
  rw [declared]
  simp only [TypedSource.applySubstitution]
  by_cases owner : id.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte]
    have selected : ((declaredBinders source).map (TypedBinder.applySubstitution substitution)).filter
        (fun binder => decide (binder.id = id)) =
        ((declaredBinders source).filter (fun binder => decide (binder.id = id))).map
          (TypedBinder.applySubstitution substitution) := by
      simp only [List.filter_map, Function.comp_def, TypedBinder.applySubstitution_id]
    rw [selected]
    cases entries : (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
    | nil => rfl
    | cons binder rest =>
      cases rest with
      | nil =>
        simp only [List.map_cons, List.map_nil, FlexibleSubstitution.applyTypedBinder_scheme_quantified,
          FlexibleSubstitution.applyTypedBinder_schemeRequirements, List.isEmpty_map]
        split <;> split <;> rfl
      | cons next remaining => rfl
  · simp [owner, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, Except.map]

private theorem lookup (substitution : Substitution)
    {locals : Resolved.LocalScope Scheme} {id : Resolved.LocalId} {scheme : Scheme}
    (found : Resolved.LocalScope.Lookup locals id scheme) :
    Resolved.LocalScope.Lookup (FlexibleSubstitution.applyLocals substitution locals) id (scheme.apply substitution) := by
  induction found with
  | head => exact .head
  | tail different tail ih => exact .tail different ih

theorem scope {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {context : SourceSemantics.Context}
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context) (substitution : Substitution) :
    CompatibleExpressionReads.ScopeDeclarations (source.applySubstitution substitution) scope
      (FlexibleSubstitution.closeContext substitution context) := by
  intro id declared index type selected authentic
  rw [root] at authentic
  cases original : rootBinder source id with
  | error error => simp only [original, Except.map] at authentic; cases authentic
  | ok binder =>
    simp only [original, Except.map] at authentic
    cases authentic
    simpa only [FlexibleSubstitution.applyTypedBinder_scheme, FlexibleSubstitution.closeContext, FlexibleSubstitution.applyContext] using lookup substitution (declarations _ _ _ _ selected original)

theorem materialized {function : Dynamic.GeneralizedClosure} {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source scope function.definitionContext)
    (substitution : Substitution) (evidence : Dynamic.EvidenceEnvironment) :
    CompatibleExpressionReads.ScopeDeclarations (function.instantiate substitution evidence).source scope
      (function.instantiate substitution evidence).context := by
  exact GeneralizedLocalScopeDeclarations.scope (context := localSchemeInitializerContext function.definitionContext function.binder) declarations substitution

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalScopeDeclarations
