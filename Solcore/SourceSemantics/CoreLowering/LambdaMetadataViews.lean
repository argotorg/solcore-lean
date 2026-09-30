import Solcore.SourceSemantics.CoreLowering.LambdaSourceAlignment

/-! Temporary metadata views preserve the source shapes used by callable
contracts. The actual evidence lowerer can change an expression's output type,
requirements, and coercion path without changing its occurrence or form.

The source table remains distinct from the compiler view. This relation proves
lambda parameter/result/body provenance, not typing or execution equivalence
of arbitrary metadata edits, nor general decorated-body code correspondence. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
open Frontend Frontend.SourceInference DataPatternValues

inductive NodeView : Node → Node → Prop where
  | expression {before after : ExpressionNode} (id : before.id = after.id)
      (form : before.form = after.form) : NodeView (.expression before) (.expression after)
  | statement (node : StatementNode) : NodeView (.statement node) (.statement node)

theorem NodeView.occurrence {before after : Node} (related : NodeView before after) :
    before.occurrenceId = after.occurrenceId := by
  cases related with
  | expression id _ => exact congrArg ExpressionId.occurrence id
  | statement => rfl

theorem NodeView.refl (node : Node) : NodeView node node := by
  cases node with
  | expression => exact .expression rfl rfl
  | statement => exact .statement _

theorem NodeView.symm {before after : Node} (related : NodeView before after) : NodeView after before := by
  cases related with
  | expression id form => exact .expression id.symm form.symm
  | statement => exact .statement _

theorem NodeView.trans {a b c : Node} (left : NodeView a b) (right : NodeView b c) : NodeView a c := by
  cases left with
  | expression id form => cases right with | expression id' form' => exact .expression (id.trans id') (form.trans form')
  | statement => exact right

structure MetadataView (original view : TypedSource) : Prop where
  owner : original.owner = view.owner
  inputs : original.inputs = view.inputs
  roots : original.roots = view.roots
  nodes : ListRel NodeView original.nodes view.nodes

private theorem nodes_refl (nodes : List Node) : ListRel NodeView nodes nodes := by
  induction nodes with
  | nil => exact .nil
  | cons head tail ih => exact .cons (.refl head) ih

private theorem nodes_symm {a b : List Node} (related : ListRel NodeView a b) : ListRel NodeView b a := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons head.symm ih

private theorem nodes_trans {a b c : List Node} (left : ListRel NodeView a b) (right : ListRel NodeView b c) :
    ListRel NodeView a c := by
  induction left generalizing c with
  | nil => exact right
  | cons head rest ih => cases right with | cons head' rest' => exact .cons (head.trans head') (ih rest')

theorem MetadataView.refl (source : TypedSource) : MetadataView source source :=
  ⟨rfl, rfl, rfl, nodes_refl _⟩

theorem MetadataView.symm {a b : TypedSource} (related : MetadataView a b) : MetadataView b a :=
  ⟨related.owner.symm, related.inputs.symm, related.roots.symm, nodes_symm related.nodes⟩

theorem MetadataView.trans {a b c : TypedSource} (left : MetadataView a b) (right : MetadataView b c) :
    MetadataView a c :=
  ⟨left.owner.trans right.owner, left.inputs.trans right.inputs, left.roots.trans right.roots,
    nodes_trans left.nodes right.nodes⟩

private theorem nodes_occurrences {a b : List Node} (related : ListRel NodeView a b) :
    a.map Node.occurrenceId = b.map Node.occurrenceId := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, head.occurrence, ih]

theorem MetadataView.unique {original view : TypedSource} (related : MetadataView original view)
    (unique : NodeOccurrencesUnique original) : NodeOccurrencesUnique view := by
  change (view.nodes.map Node.occurrenceId).Nodup
  rw [← nodes_occurrences related.nodes]
  exact unique

private inductive Selection : Option Node → Option Node → Prop where
  | none : Selection none none
  | some {before after : Node} (related : NodeView before after) : Selection (some before) (some after)

private theorem find_related {a b : List Node} (related : ListRel NodeView a b) (id : OccurrenceId) :
    Selection (a.find? fun node => decide (node.occurrenceId = id))
      (b.find? fun node => decide (node.occurrenceId = id)) := by
  induction related with
  | nil => exact .none
  | @cons before tail after rest head _ ih =>
    simp only [List.find?_cons, head.occurrence]
    split
    · exact .some head
    · exact ih

/-- An actual view lookup reconstructs the original occurrence and its exact
form; no claim is made that the expression metadata fields are equal. -/
theorem MetadataView.expression {original view : TypedSource} (related : MetadataView original view)
    {id : ExpressionId} {node : ExpressionNode} (found : view.lookupExpression? id = some node) :
    ∃ originalNode, original.lookupExpression? id = some originalNode ∧
      originalNode.id = node.id ∧ originalNode.form = node.form := by
  have selected := find_related related.nodes id.occurrence
  change Selection (original.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupExpression? at found ⊢
  cases left : original.lookupNode? id.occurrence <;> cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected found ⊢
  · cases found
  · cases selected
  · cases found
  · cases selected with
    | some values =>
      cases values with
      | expression sameId sameForm =>
        cases found
        exact ⟨_, rfl, sameId, sameForm⟩
      | statement => cases found

/-- Raw expression views leave every statement node intact. This supports
later body certificates that retain the original statement metadata. -/
theorem MetadataView.statement {original view : TypedSource} (related : MetadataView original view)
    {id : StatementId} {node : StatementNode} (found : view.lookupStatement? id = some node) :
    original.lookupStatement? id = some node := by
  have selected := find_related related.nodes id.occurrence
  change Selection (original.lookupNode? id.occurrence) (view.lookupNode? id.occurrence) at selected
  unfold TypedSource.lookupStatement? at found ⊢
  cases left : original.lookupNode? id.occurrence <;> cases right : view.lookupNode? id.occurrence <;>
    simp only [left, right] at selected found ⊢
  · cases found
  · cases selected
  · cases found
  · cases selected with
    | some values =>
      cases values with
      | expression => cases found
      | statement => exact found

private theorem nodes_map (nodes : List Node) (change : Node → Node)
    (each : ∀ old ∈ nodes, NodeView old (change old)) : ListRel NodeView nodes (nodes.map change) := by
  induction nodes with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (each head (by simp)) (ih (by intro old member; exact each old (List.mem_cons_of_mem head member)))

private theorem withNode_nodes {source : TypedSource} {node replacement : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (sameId : node.id = replacement.id) (sameForm : node.form = replacement.form) :
    ListRel NodeView source.nodes (SourceCoreEvidence.withNode source replacement).nodes := by
  change ListRel NodeView source.nodes (source.nodes.map _)
  apply nodes_map
  intro old member
  cases old with
  | statement current => exact .statement _
  | expression current =>
    by_cases same : current.id = replacement.id
    · have lookup := lookupExpression?_complete unique (show ContainsExpression source node.id current from
        ⟨member, same.trans sameId.symm⟩)
      have eq := Option.some.inj (lookup.symm.trans found)
      subst current
      simpa only [same, ↓reduceIte] using NodeView.expression sameId sameForm
    · simpa only [same, ↓reduceIte] using NodeView.expression (before := current) rfl rfl

/-- The real evidence lowerer's replacement preserves the metadata view when
it retains the selected occurrence's ID and form. -/
theorem withNode_view {source : TypedSource} {node replacement : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (sameId : node.id = replacement.id) (sameForm : node.form = replacement.form) :
    MetadataView source (SourceCoreEvidence.withNode source replacement) :=
  ⟨rfl, rfl, rfl, withNode_nodes unique found sameId sameForm⟩

/-- Exact raw view emitted by `SourceCoreEvidence.lowerWithCaller`. Ordinary
requirement ownership can change independently of the preserved lambda form. -/
theorem raw_view {source : TypedSource} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? node.id = some node)
    (ordinary : List RequirementId) :
    MetadataView source (SourceCoreEvidence.withNode source
      { node with type := node.rawType, requirements := ordinary, coercions := [] }) :=
  withNode_view unique found rfl rfl

/-- Local scheme-evidence normalization has the same metadata-view law.
The accepted factory compares the actual occurrence before replacing only its
ordinary requirements; repeated normalization preserves the current view. -/
theorem normalized_view {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {binding : SourceCoreLocalPolymorphism.Binding} {parent : Option SourceCoreLocalEvidence.Prepared}
    {source normalized : TypedSource} {id : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (accepted : SourceCoreLocalEvidence.normalizeOccurrence program plan binding parent source id = .ok normalized) :
    MetadataView source normalized := by
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
            have related := withNode_view (replacement := reference.normalized) unique atSelf rfl rfl
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
            exact views.symm ▸ related
          · split at accepted
            · cases accepted; exact .refl _
            · cases accepted
        · cases accepted
      · cases accepted

/-- Canonical preparation plus actual raw-view lookup suffices for source
lambda provenance. The source closure keeps the canonical table; the code
certificate may separately refer to the compiler's temporary view. -/
theorem lambda_origin {checked : CheckedProgram} {plan : SourceCoreStageContracts.Plan}
    {owner : SourceCoreStageContracts.Key} {id : ExpressionId} {active : TypeSystem.Substitution}
    {contract : SourceCoreStageContracts.Contract} {function : Dynamic.Closure} {view : TypedSource}
    {node : ExpressionNode}
    (receipt : LambdaSourceAlignment.SourceReceipt checked plan owner active function.source)
    (original : AuthenticatedCallableLedger.LambdaSource plan owner id active contract)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) :
    CallableLedger.LambdaOrigin plan owner id active function contract := by
  obtain ⟨sourceNode, selected, _, sameForm⟩ := metadata.expression found
  exact original.alignment (LambdaSourceAlignment.source_alignment receipt original) unique selected (sameForm.trans form)

/-- The real codebook factory and descriptor recover callable provenance for
a lambda compiled through temporary metadata views. This is the origin half
of the payload relation: the raw code/capture certificate remains separate. -/
theorem origin_of_prepare {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {owner : SourceCoreStageCodebook.Key} {id : ExpressionId}
    {active : TypeSystem.Substitution} {function : Dynamic.Closure} {view : TypedSource} {node : ExpressionNode}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt checkedProgram plan owner active function.source)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (found : view.lookupExpression? id = some node)
    (form : node.form = .lambda function.parameters function.resultType function.body) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) := by
  obtain ⟨site⟩ := AuthenticatedCallableLedger.lambda_site_of_descriptor accepted descriptor
  have origin := lambda_origin receipt site.original metadata unique found form
  have represented := CallableLedger.OriginRep.closure (raw := raw) site.member site.origin site.retained origin
  simpa only [site.id_eq] using represented

/-- Consume the actual accepted decorated-lambda certificate at its compiler
view, while keeping the source closure and its staging contract canonical.
This theorem concerns provenance; a value simulation must additionally relate
the certificate's emitted raw body and captured environment. -/
theorem decorated_origin_of_prepare {checkedProgram : CheckedProgram} {plan : SourceCoreStageCodebook.Plan}
    {checked : SourceCoreDataCatalog.Checked} {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
    {table : SourceCoreStageCodebook.Table} {active : TypeSystem.Substitution}
    {bodyCertificate : FunctionCode.BodyCertificate} {policy : SourceCoreFunctions.Policy}
    {compilation : SourceCoreFunctions.Context} {view : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {function : Dynamic.Closure}
    {reportedType : Core.Ty} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreStageCodebook.prepare checkedProgram plan checked limits firstId = .ok table)
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id active))
    (receipt : LambdaSourceAlignment.SourceReceipt checkedProgram plan compilation.owner active function.source)
    (metadata : MetadataView function.source view)
    (unique : NodeOccurrencesUnique function.source)
    (artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate policy compilation view scope id node
      function.parameters function.resultType function.body reportedType lowered) (raw : Core.Value) :
    CallableLedger.OriginRep plan table (.closure function) (.pair raw (.word descriptor.id)) :=
  origin_of_prepare accepted descriptor receipt metadata unique artifact.raw.found artifact.raw.form raw

end Solcore.SourceSemantics.CoreLowering.LambdaMetadataViews
