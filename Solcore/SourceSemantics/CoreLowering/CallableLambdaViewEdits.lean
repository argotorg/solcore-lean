import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaViewPrefix

/-! Local compiler edits retain complete expression metadata outside their
recorded occurrence IDs. This is stronger than the allocation metadata view.
Freshness is explicit: graph ownership does not establish that a changed parent
cannot occur among a body's references. These are static lookup receipts, not
an execution equivalence for arbitrary edited expressions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewEdits
open Frontend SourceInference

private theorem lookup_other (source : TypedSource) (replacement : ExpressionNode)
    (id : ExpressionId) (different : id ≠ replacement.id) :
    (SourceCoreEvidence.withNode source replacement).lookupExpression? id = source.lookupExpression? id := by
  rcases source with ⟨owner, inputs, roots, nodes⟩
  unfold SourceCoreEvidence.withNode TypedSource.lookupExpression? TypedSource.lookupNode?
  dsimp only
  induction nodes with
  | nil => rfl
  | cons node rest ih =>
    cases node with
    | statement statement =>
      cases hit : decide ((Node.statement statement).occurrenceId = id.occurrence)
      · simpa only [List.map_cons, List.find?_cons, hit] using ih
      · simp only [List.map_cons, List.find?_cons, hit]
    | expression expression =>
      by_cases same : expression.id = replacement.id
      · have notId : expression.id.occurrence ≠ id.occurrence := by
          intro equal
          exact different ((congrArg ExpressionId.mk equal.symm).trans same)
        have replacedNotId : replacement.id.occurrence ≠ id.occurrence := by simpa only [same] using notId
        simpa only [List.map_cons, same, ↓reduceIte, List.find?_cons, Node.occurrenceId,
          Node.id, NodeId.occurrenceId, notId, replacedNotId, decide_false] using ih
      · cases hit : decide ((Node.expression expression).occurrenceId = id.occurrence)
        · simpa only [List.map_cons, same, ↓reduceIte, List.find?_cons, hit] using ih
        · simp only [List.map_cons, same, ↓reduceIte, List.find?_cons, hit]

structure LocalView (original view : TypedSource) (changed : List ExpressionId) : Prop where
  metadata : LambdaMetadataViews.MetadataView original view
  unchanged : ∀ id, id ∉ changed → original.lookupExpression? id = view.lookupExpression? id

theorem LocalView.refl (source : TypedSource) : LocalView source source [] :=
  ⟨.refl source, by intros; rfl⟩

theorem LocalView.trans {first middle last : TypedSource} {left right : List ExpressionId}
    (a : LocalView first middle left) (b : LocalView middle last right) :
    LocalView first last (left ++ right) := by
  refine ⟨a.metadata.trans b.metadata, ?_⟩
  intro id fresh
  have both : id ∉ left ∧ id ∉ right := by simpa only [List.mem_append, not_or] using fresh
  exact (a.unchanged id both.1).trans (b.unchanged id both.2)

/-- One actual `withNode` pass records the selected ID and preserves the
entire metadata of every other lookup. -/
theorem withNode {source : TypedSource} {node replacement : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (sameId : node.id = replacement.id) (sameForm : node.form = replacement.form) :
    LocalView source (SourceCoreEvidence.withNode source replacement) [node.id] := by
  refine ⟨LambdaMetadataViews.withNode_view unique found sameId sameForm, ?_⟩
  intro id fresh
  apply (lookup_other source replacement id ?_).symm
  simpa only [← sameId, List.mem_singleton] using fresh

theorem raw {source : TypedSource} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (ordinary : List RequirementId) :
    LocalView source (SourceCoreEvidence.withNode source
      {node with type := node.rawType, requirements := ordinary, coercions := []}) [node.id] :=
  withNode unique found rfl rfl

/-- Successful local-scheme normalization changes at most the selected
occurrence; the accepted factory's original-node check remains in the proof. -/
theorem normalized {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source view : TypedSource} {id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id = .ok view) :
    LocalView source view [id] := by
  unfold SourceCoreLocalEvidence.normalizeOccurrence at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · next reference reference_found =>
      split at accepted
      · next current current_found =>
        split at accepted
        · next ordinary ordinary_found =>
          split at accepted
          · next same =>
            cases accepted
            subst current
            have atSelf : source.lookupExpression? reference.original.id = some reference.original := by
              simpa only [(lookupExpression?_sound current_found).2] using current_found
            have related := withNode (replacement := reference.normalized) unique atSelf rfl rfl
            have sameId : reference.normalized.id = id := (lookupExpression?_sound current_found).2
            have views : { source with nodes := source.nodes.map (fun
                | .expression old => if old.id = id then .expression reference.normalized else .expression old
                | .statement old => .statement old) } = SourceCoreEvidence.withNode source reference.normalized := by
              unfold SourceCoreEvidence.withNode
              apply congrArg (fun (nodes : List Node) => ({ source with nodes := nodes } : TypedSource))
              apply List.map_congr_left
              intro item _
              cases item with
              | expression old => by_cases equal : old.id = id <;> simp [sameId, equal]
              | statement => rfl
            have result : LocalView source (SourceCoreEvidence.withNode source reference.normalized) [id] := by
              simpa only [(lookupExpression?_sound current_found).2] using related
            exact views.symm ▸ result
          · split at accepted
            · cases accepted; exact ⟨.refl _, by intros; rfl⟩
            · cases accepted
        · cases accepted
      · cases accepted

/-- A finite static body footprint can use these equalities once its actual
reference IDs have been checked against the edit list. -/
theorem LocalView.expressions {source view : TypedSource} {changed footprint : List ExpressionId}
    (receipt : LocalView source view changed)
    (fresh : ∀ id ∈ footprint, id ∉ changed) :
    ∀ id ∈ footprint, source.lookupExpression? id = view.lookupExpression? id :=
  fun id member => receipt.unchanged id (fresh id member)

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewEdits
