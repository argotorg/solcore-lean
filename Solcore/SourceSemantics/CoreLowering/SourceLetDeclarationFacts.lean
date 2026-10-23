import Solcore.SourceSemantics.Ownership
import Solcore.Frontend.SourceCoreDataPlaces

/-! A concrete let and the same source's local identity ownership supply its
complete declaration and distinguish it from input parameters. These finite
inventory proofs are shared with the accepted-body binder analysis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
open Core Frontend SourceInference

private theorem instruction_ids (instructions : List MatchPatternInstruction) :
    (SourceCoreDataPlaces.instructionBinders instructions).map (·.id) =
      patternInstructionBinderIds instructions := by
  induction instructions with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [SourceCoreDataPlaces.instructionBinders,
      patternInstructionBinderIds] at ih ⊢ <;> exact ih

private theorem pattern_ids (pattern : TypedMatchPattern) :
    (SourceCoreDataPlaces.patternBinders pattern).map (·.id) = patternBinderIds pattern := by
  cases pattern with
  | mk source type resolution requirements =>
    cases resolution <;> simp [SourceCoreDataPlaces.patternBinders, patternBinderIds, instruction_ids]

private theorem for_ids (items : List ForItemForm) :
    (items.filterMap fun | .letDecl binder _ => some binder | _ => none).map (·.id) =
      items.flatMap forItemDefinedLocalIds := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [forItemDefinedLocalIds, ih]

private def nodeBinders (node : Node) : List TypedBinder :=
  match node with
  | .expression node => match node.form with
      | .lambda parameters _ _ => parameters
      | _ => []
  | .statement node => match node.form with
      | .letDecl binder _ => [binder]
      | .forLoop initial _ post _ => (initial ++ post).filterMap fun
          | .letDecl binder _ => some binder | _ => none
      | .matchWith resolution => resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)
      | _ => []

private theorem node_ids (node : Node) :
    ((nodeBinders node).map (·.id)).Sublist node.definedLocalIds := by
  cases node with
  | expression node => cases form : node.form <;>
      simp [nodeBinders, form, Node.definedLocalIds, ExpressionForm.definedLocalIds]
  | statement node =>
      cases form : node.form <;>
        simp [nodeBinders, form, Node.definedLocalIds, StatementForm.definedLocalIds,
          for_ids]
      case matchWith resolution =>
        have same : (resolution.cases.flatMap (fun arm => SourceCoreDataPlaces.patternBinders arm.pattern)).map (·.id) =
            resolution.cases.flatMap (fun arm => arm.pattern.binderIds) := by
          simp [List.map_flatMap, pattern_ids]
        rw [same]
        exact List.sublist_cons_self _ _

private theorem nodes_ids (nodes : List Node) :
    ((nodes.flatMap nodeBinders).map (·.id)).Sublist (nodes.flatMap Node.definedLocalIds) := by
  induction nodes with
  | nil => exact .refl _
  | cons node rest ih =>
    simpa only [List.flatMap_cons, List.map_append] using (node_ids node).append ih

private theorem declared_ids (source : TypedSource) :
    ((SourceCoreDataPlaces.declaredBinders source).map (·.id)).Sublist (definedLocalIds source) := by
  have same : SourceCoreDataPlaces.declaredBinders source = source.inputs ++ source.nodes.flatMap nodeBinders := rfl
  rw [same, List.map_append, ← typedSourceDefinedLocalIds_eq_carrier]
  exact (List.Sublist.refl _).append (nodes_ids source.nodes)

private theorem filter_self {binders : List TypedBinder} {binder : TypedBinder}
    (unique : (binders.map (·.id)).Nodup) (member : binder ∈ binders) :
    binders.filter (fun other => decide (other.id = binder.id)) = [binder] := by
  induction binders with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with rfl | member
    · have none : rest.filter (fun other => decide (other.id = binder.id)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro other found
        simp only [decide_eq_true_eq]
        intro equal
        exact absent (List.mem_map.mpr ⟨other, found, equal⟩)
      simp [none]
    · have different : first.id ≠ binder.id := by
        intro same
        exact absent (List.mem_map.mpr ⟨binder, member, same.symm⟩)
      simp [different, ih restUnique member]

theorem of_lookup {source : TypedSource} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source ∧
      (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder] ∧
      source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  have member := (lookupStatement?_sound found).1
  have defined : binder ∈ nodeBinders (.statement node) := by simp [nodeBinders, form]
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.statement node, member, defined⟩)
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨.statement node, member,
      (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
      (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
      by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨declared, filtered, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro occurs
  obtain ⟨input, present, same⟩ := List.any_eq_true.mp occurs
  exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
    binder.id inNodes (of_decide_eq_true same)

end Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts

namespace Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
open Core Frontend SourceInference

theorem of_header_lookup {source : TypedSource} {id : StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (ownership : LocalIdentityOwnership source)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body)
    (present : ForItemForm.letDecl binder initializer ∈ initial ++ post) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source ∧
      (SourceCoreDataPlaces.declaredBinders source).filter
        (fun actual => decide (actual.id = binder.id)) = [binder] ∧
      source.inputs.any (fun input => decide (input.id = binder.id)) = false := by
  have member := (lookupStatement?_sound found).1
  have defined : binder ∈ nodeBinders (.statement node) := by
    simp only [nodeBinders, form]
    exact List.mem_filterMap.mpr ⟨.letDecl binder initializer, present, rfl⟩
  have declared : binder ∈ SourceCoreDataPlaces.declaredBinders source :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨.statement node, member, defined⟩)
  have filtered := filter_self ((declared_ids source).nodup ownership.unique) declared
  have inNodes : binder.id ∈ source.nodes.flatMap Node.definedLocalIds :=
    List.mem_flatMap.mpr ⟨.statement node, member,
      (node_ids (.statement node)).subset (List.mem_map.mpr ⟨binder, defined, rfl⟩)⟩
  have disjoint := (List.nodup_append.mp (show
      (source.inputs.map (·.id) ++ source.nodes.flatMap Node.definedLocalIds).Nodup from
      by simpa only [definedLocalIds, ← flatMapNodeDefinedLocalIds_eq_carrier] using ownership.unique)).2.2
  refine ⟨declared, filtered, ?_⟩
  apply Bool.eq_false_iff.mpr
  intro occurs
  obtain ⟨input, present, same⟩ := List.any_eq_true.mp occurs
  exact disjoint input.id (List.mem_map.mpr ⟨input, present, rfl⟩)
    binder.id inNodes (of_decide_eq_true same)

end Solcore.SourceSemantics.CoreLowering.SourceLetDeclarationFacts
